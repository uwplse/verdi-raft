open Str
open Printf
open VarDRaft
open VarD
open Util

let serialize out =
  match (Obj.magic out) with
  | NotLeader (client, id) ->
     ((client, id), sprintf "NotLeader %s %s" (string_of_int client) (string_of_int id))
  | ClientResponse (client, id, o) ->
     let Response (k, value, old) = (Obj.magic o) in
     ((client, id),
      match (value, old) with
      | Some v, Some o -> sprintf "Response %s %s %s %s %s"
                                 (string_of_int client)
                                 (string_of_int id)
                                 (string_of_char_list k)
                                 (string_of_char_list v)
                                 (string_of_char_list o)
      | Some v, None -> sprintf "Response %s %s %s %s -"
                               (string_of_int client)
                               (string_of_int id)
                               (string_of_char_list k)
                               (string_of_char_list v)
      | None, Some o -> sprintf "Response %s %s %s - %s"
                               (string_of_int client)
                               (string_of_int id)
                               (string_of_char_list k)
                               (string_of_char_list o)
      | None, None -> sprintf "Response %s %s %s - -"
                             (string_of_int client)
                             (string_of_int id)
                             (string_of_char_list k))

let deserialize_input i =
  let inp = String.trim i in
  let r = regexp "\\([0-9]+\\) \\([0-9]+\\) \\([A-Z]+\\) +\\([/A-za-z0-9]+\\|-\\) +\\([/A-za-z0-9]+\\|-\\) +\\([/A-za-z0-9]+\\|-\\)[^/A-za-z0-9]*" in
  if string_match r inp 0 then
    (match (matched_group 1 inp, matched_group 2 inp,
            matched_group 3 inp, matched_group 4 inp,
            matched_group 5 inp, matched_group 6 inp) with
     | (c, i, "GET", k, _, _) -> Some (int_of_string c, int_of_string i, Get (char_list_of_string k))
     | (c, i, "DEL", k, _, _) -> Some (int_of_string c, int_of_string i, Del (char_list_of_string k))
     | (c, i, "PUT", k, v, _) -> Some (int_of_string c, int_of_string i, Put ((char_list_of_string k), (char_list_of_string v)))
     | (c, i, "CAD", k, o, _) -> Some (int_of_string c, int_of_string i, CAD (char_list_of_string k, char_list_of_string o))
     | (c, i, "CAS", k, "-", v) -> Some (int_of_string c, int_of_string i, CAS ((char_list_of_string k), None, (char_list_of_string v)))
     | (c, i, "CAS", k, o, v) -> Some (int_of_string c, int_of_string i, CAS ((char_list_of_string k), Some (char_list_of_string o), (char_list_of_string v)))
     | _ -> None)
  else
    (print_endline "No match" ; None)

let deserialize inp =
  match (deserialize_input inp) with
  | Some (client, id, input) ->
     Some ((client, id), (ClientRequest (client, id, (Obj.magic input))))
  | None -> None
