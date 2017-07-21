open OUnit2
open ListLabels
open Util

let tear_down () text_ctxt = ()

let test_serialize_output_not_leader text_ctxt =
  assert_equal (2, "NotLeader 15")
    (VarDSerialization.serializeOutput (VarDRaft.NotLeader (2, 15)))

let test_serialize_output_client_response test_ctxt =
  let o = VarDRaft.Response (char_list_of_string "awesome", None, None) in
  assert_equal (3, "Response 34 awesome - -")
    (VarDSerialization.serializeOutput (VarDRaft.ClientResponse (3, 34, (Obj.magic o))))
  
let test_list =
  [
    "serialize NotLeader", test_serialize_output_not_leader;
    "serialize ClientResponse", test_serialize_output_client_response
  ]

let tests =
  "VarDSerialization" >:::
    (map test_list ~f:(fun (name, test_fn) ->
      name >:: (fun test_ctxt ->
	bracket ignore tear_down test_ctxt;
	test_fn test_ctxt)
     ))
