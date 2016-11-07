open Str
open Printf
open VarDRaft
open VarD
open Util

module type VardParams = sig
    val debug : bool
    val heartbeat_timeout : float
    val election_timeout : float
  end

module DebugParams = struct
    let debug = true
    let heartbeat_timeout = 2.0
    let election_timeout = 10.0
  end

module BenchParams = struct
    let debug = false
    let heartbeat_timeout = 0.05
    let election_timeout = 0.5
  end

module VarDArrangement (M : VardParams) = struct
  type name = VarDRaft.name
  type state = raft_data0
  type input = VarDRaft.raft_input
  type output = VarDRaft.raft_output
  type msg = VarDRaft.msg
  type res = (VarDRaft.raft_output list * raft_data0) * ((VarDRaft.name * VarDRaft.msg) list)
  type request_id = (int * int)
  let debug = M.debug
  let init x = Obj.magic (init_handlers0 vard_base_params vard_one_node_params raft_params x)
  let handleIO (n : name) (inp : input) (st : state) = Obj.magic (vard_raft_multi_params.input_handlers (Obj.magic n) (Obj.magic inp) (Obj.magic st))
  let handleNet (n : name) (src: name) (m : msg) (st : state)  = Obj.magic (vard_raft_multi_params.net_handlers (Obj.magic n) (Obj.magic src) (Obj.magic m) (Obj.magic st))
  let handleTimeout (me : name) (st : state) =
    (Obj.magic vard_raft_multi_params.input_handlers (Obj.magic me) (Obj.magic Timeout) (Obj.magic st))
  let reboot = Obj.magic (reboot vard_base_params raft_params)
  let setTimeout _ s =
    match s.type0 with
    | Leader -> M.heartbeat_timeout
    | _ -> M.election_timeout +. (Random.float 0.1)
  let deserialize = VarDSerialization.deserialize
  let serialize = VarDSerialization.serialize
  let debugRecv s (other, m) =
    (match m with
     | AppendEntries (t, leaderId, prevLogIndex, prevLogTerm, entries, commitIndex) ->
        printf "[Term %d] Received %d entries from %d (currently have %d entries)\n"
               s.currentTerm (List.length entries) other (List.length s.log)
     | AppendEntriesReply (_, entries, success) ->
        printf "[Term %d] Received AppendEntriesReply %d entries %B, commitIndex %d\n"
               s.currentTerm (List.length entries) success s.commitIndex
     | RequestVoteReply (t, votingFor) ->
        printf "[Term %d] Received RequestVoteReply(%d, %B) from %d, have %d votes\n"
               s.currentTerm t votingFor other (List.length s.votesReceived)
     | _ -> ()); flush_all ()
  let debugSend s (other, m) =
    (match m with
     | AppendEntries (t, leaderId, prevLogIndex, prevLogTerm, entries, commitIndex) ->
        printf "[Term %d] Sending %d entries to %d (currently have %d entries), commitIndex=%d\n"
               s.currentTerm (List.length entries) other (List.length s.log) commitIndex
     | RequestVote _ ->
        printf "[Term %d] Sending RequestVote to %d, have %d votes\n"
               s.currentTerm other (List.length s.votesReceived)
     | _ -> ()); flush_all ()

  let debugTimeout (s : state) = ()
    (* (match s.type0 with
     | Leader -> printf "Leader\n"
     | Follower -> printf "Follower\n"
     | Candidate -> printf "Candidate\n"); *)

end
