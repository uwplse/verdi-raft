open ListLabels
open OUnit2

let tear_down () text_ctxt = ()

let test_serialize_not_leader text_ctxt =
  assert_equal ((1, 15), "NotLeader 1 15") (VarDSerialization.serialize (VarDRaft.NotLeader (1, 15)))
  
let test_list =
  ["serialize NotLeader", test_serialize_not_leader]

let test_suite =
  "VarDSerialization" >:::
    (map test_list ~f:(fun (name, test_fn) ->
      name >:: (fun test_ctxt ->
	bracket ignore tear_down test_ctxt;
	test_fn test_ctxt)
     ))

let _ = run_test_tt_main test_suite
