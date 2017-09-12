open Printf
open Util

type 'file_name disk_op =
  | Append of file_name * Serialize_primitives.serializer
  | Write of file_name * Serialize_primitives.serializer
  | Delete of file_name

module type ARRANGEMENT = sig
  type name
  type file_name
  type state
  type input
  type output
  type msg
  type client_id
  type res = ((disk_op list * output list) * state) * ((name * msg) list) (* product is left-associative? *)
  type disk = file_name -> Serializer_primitives.serializer
  val system_name : string
  val init : name -> state
  val disk_init : name -> disk
  val reboot : name -> (file_name -> Serializer_primitives.wire) -> state * disk
  val handle_input : name -> input -> state -> res
  val handle_msg : name -> name -> msg -> state -> res
  val handle_timeout : name -> state -> res
  val set_timeout : name -> state -> float
  val deserialize_msg : bytes -> msg
  val serialize_msg : msg -> bytes
  val deserialize_input : bytes -> client_id -> input option
  val serialize_output : output -> client_id * bytes
  val debug : bool
  val debug_input : state -> input -> unit
  val debug_recv : state -> (name * msg) -> unit
  val debug_send : state -> (name * msg) -> unit
  val debug_timeout : state -> unit
  val create_client_id : unit -> client_id
  val string_of_client_id : client_id -> string
  val string_of_file_name : file_name -> string
  val file_name_of_string : string -> file_name
  val files : file_name list
end

module Shim (A: ARRANGEMENT) = struct
  type cfg =
      { cluster : (A.name * (string * int)) list
      ; me : A.name
      ; port : int
      ; fspath : string
      }

  type env =
      { cfg : cfg
      ; nodes_fd : Unix.file_descr
      ; clients_fd : Unix.file_descr
      ; nodes : (A.name * Unix.sockaddr) list
      ; client_read_fds : (Unix.file_descr, A.client_id) Hashtbl.t
      ; client_write_fds : (A.client_id, Unix.file_descr) Hashtbl.t
      ; client_read_bufs : (Unix.file_descr, int * bytes) Hashtbl.t
      ; mutable saves : int
      }

  type log_step =
  | LogInput of A.input
  | LogNet of A.name * A.msg
  | LogTimeout

  let full_path_of_file_name (cfg : cfg) (f : file_name) =
    cfg.db_path ^ "/" ^ A.string_of_file_name f

  (* keep all files open? currently assumes we reopen on each op *)
  let apply_disk_op (env : env) (op : disk_op) =
    let file_string_descriptor f =
      let fs = env.cfg.fspath ^ A.string_of_file_name f in
      (fs, Unix.out_channel_of_descr
             (Unix.openfile fs
	                        [Unix.O_WRONLY ; if append then Unix.O_APPEND else Unix.O_TRUNC;
                             Unix.O_CREAT ; Unix.O_DSYNC]
                            0o640)) in
    let aux f v (append : bool) =
      let (fs, f_out) = file_string_descriptor f in
      if A.debug
      then print_endline (if append then "appending" else "writing") ^ " to " ^ fs;
      if (not append) then Unix.ftruncate (Unix.descr_out_of_channel f_out) 0;
      output_string f_out (Bytes.to_string (Serializer_primitives.wire_wrap v));
      flush f_out;
      close_out f_out in
    match op with
    | Append (f, v) -> aux f v true
    | Write (f, v) -> aux f v false
    | Delete f -> Unix.truncate (A.string_of_file_name f) 0

  (* Translate node name to UDP socket address. *)
  let denote_node (env : env) (name : A.name) : Unix.sockaddr =
    List.assoc name env.nodes

  (* Translate UDP socket address to node name. *)
  let undenote_node (env : env) (addr : Unix.sockaddr) : A.name =
    let flip = function (x, y) -> (y, x) in
    List.assoc addr (List.map flip env.nodes)

  (* Translate client id to TCP socket address *)
  let denote_client (env : env) (c : A.client_id) : Unix.file_descr =
    Hashtbl.find env.client_write_fds c

  (* Translate TCP socket address to client id *)
  let undenote_client (env : env) (fd : Unix.file_descr) : A.client_id =
    Hashtbl.find env.client_read_fds fd

  (* maybe return a function that returns cached results? *)
  let file_name_to_wire (fspath) : file_name -> Serializer_primitives.wire =
    fun f -> let channel = open_in_bin (fspath ^ "/" ^ string_of_file_name f);
                           let rec reads () =
                             let size = 512 in
                             let buf = Bytes.make size (Char.chr 0) in
                             let res = Unix.read (Unix.descr_of_in_channel channel) buf 0 size in
                             buf :: if (res < size) then [] else reads () in
                           Bytes.concat Bytes.empty (reads ())



  let restore (cfg : cfg) =
    try reboot cfg.me (file_name_to_wire cfg.fspath)
    with Sys_error -> (A.init cfg.me, A.disk_init cfg.me)

  let save_disk (cfg : cfg) (dsk : disk) =
    failwith "Unimplemented"

  (* Load state from disk, initialize environment, and start server. *)
  let setup (cfg : cfg) : (env * A.state) =
    Random.self_init ();
    let addressify (name, (host, port)) =
      let entry = Unix.gethostbyname host in
      (name, Unix.ADDR_INET (entry.Unix.h_addr_list.(0), port))
    in
    begin
      try
        Unix.mkdir cfg.fspath 0o700
      with Unix.Unix_error (err, fn, param) ->
        if err != Unix.EEXIST then
          raise (Unix.Unix_error (err, fn, param))
    end;
    let (initial_state, initial_disk) = restore cfg in
    save cfg initial_disk;
    let env =
      { cfg = cfg
      ; nodes_fd = Unix.socket Unix.PF_INET Unix.SOCK_DGRAM 0
      ; clients_fd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0
      ; nodes = List.map addressify cfg.cluster
      ; client_read_fds = Hashtbl.create 17
      ; client_write_fds = Hashtbl.create 17
      ; client_read_bufs = Hashtbl.create 17
      }
    in
    let (node_addr, node_port) =
      match List.assoc cfg.me env.nodes with
      | Unix.ADDR_INET (addr, port) -> (addr, port)
      | _ -> assert false in
    Unix.setsockopt env.clients_fd Unix.SO_REUSEADDR true;
    Unix.setsockopt env.nodes_fd Unix.SO_REUSEADDR true;
    Unix.bind env.nodes_fd (Unix.ADDR_INET (node_addr, node_port));
    Unix.bind env.clients_fd (Unix.ADDR_INET (node_addr, cfg.port));
    Unix.listen env.clients_fd 8;
    Unix.set_nonblock env.clients_fd;
    (env, initial_state)

  let disconnect_client env fd reason =
    let c = undenote_client env fd in
    Hashtbl.remove env.client_read_fds fd;
    Hashtbl.remove env.client_write_fds c;
    Hashtbl.remove env.client_read_bufs fd;
    Unix.close fd;
    if A.debug then begin
      printf "client %s disconnected: %s" (A.string_of_client_id c) reason;
      print_newline ()
    end

  let sendto sock buf addr =
    try
      ignore (Unix.sendto sock buf 0 (Bytes.length buf) [] addr)
    with Unix.Unix_error (err, fn, arg) ->
      eprintf "error in sendto: %s, dropping message" (Unix.error_message err);
      prerr_newline ()

  let send env ((nm : A.name), (msg : A.msg)) =
    sendto env.nodes_fd (A.serialize_msg msg) (denote_node env nm)

  let output env o =
    let (c, out) = A.serialize_output o in
    try send_chunk (denote_client env c) out
    with
    | Not_found ->
      eprintf "output: failed to find socket for client %s" (A.string_of_client_id c);
      prerr_newline ()
    | Disconnect s ->
      disconnect_client env (denote_client env c)
        (sprintf "output: failed send to client %s: %s" (A.string_of_client_id c) s)
    | Unix.Unix_error (err, fn, _) ->
       disconnect_client env (denote_client env c)
         (sprintf "output: error %s" (Unix.error_message err))

  let respond env (((ops, os), s), ps) =
    List.iter (output env) os;
    List.iter (fun p -> if A.debug then A.debug_send s p; send env p) ps;
    List.iter (apply_disk_op env) ops;
    s

  let new_client_conn env =
    let (client_fd, client_addr) = Unix.accept env.clients_fd in
    let c = A.create_client_id () in
    Unix.set_nonblock client_fd;
    Hashtbl.add env.client_read_fds client_fd c;
    Hashtbl.add env.client_write_fds c client_fd;
    if A.debug then begin
      printf "client %s connected on %s" (A.string_of_client_id c) (string_of_sockaddr client_addr);
      print_newline ()
    end

  let input_step (fd : Unix.file_descr) (env : env) (state : A.state) =
    try
      match recv_buf_chunk fd env.client_read_bufs with
      | None ->
	state
      | Some buf ->
	let c = undenote_client env fd in
	match A.deserialize_input buf c with
	| Some inp ->
          let state' = respond env (A.handle_input env.cfg.me inp state) in
          if A.debug then A.debug_input state' inp;
          state'
	| None ->
	  disconnect_client env fd "input deserialization failed";
	  state
    with
    | Disconnect s ->
      disconnect_client env fd s;
      state
    | Unix.Unix_error (err, fn, _) ->
      disconnect_client env fd (sprintf "error in %s: %s" fn (Unix.error_message err));
      state

  let msg_step (env : env) (state : A.state) : A.state =
    let len = 65536 in
    let buf = Bytes.make len '\x00' in
    let (_, from) = Unix.recvfrom env.nodes_fd buf 0 len [] in
    let (src, msg) = (undenote_node env from, A.deserialize_msg buf) in
    let state' = respond env (A.handle_msg env.cfg.me src msg state) in
    if A.debug then A.debug_recv state' (src, msg);
    state'

  let timeout_step (env : env) (state : A.state) : A.state =
    if A.debug then A.debug_timeout state;
    let x = A.handle_timeout env.cfg.me state in
    respond env x

  let process_fd env state fd : A.state =
    if fd = env.clients_fd then
      (new_client_conn env; state)
    else if fd = env.nodes_fd then
      msg_step env state
    else
      input_step fd env state

  let rec eloop (env : env) (state : A.state) : unit =
    let all_fds = env.nodes_fd :: env.clients_fd :: keys_of_hashtbl env.client_read_fds in
    let (ready_fds, _, _) = select_unintr all_fds [] [] (A.set_timeout env.cfg.me state) in
    let state' =
      match ready_fds with
      | [] -> timeout_step env state
      | _ -> List.fold_left (process_fd env) state ready_fds in
    eloop env state'

  let main (cfg : cfg) : unit =
    printf "unordered shim running setup for %s" A.system_name;
    print_newline ();
    let (env, initial_state) = setup cfg in
    print_endline "unordered shim ready for action";
    eloop env initial_state
end
