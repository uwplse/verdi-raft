open ListLabels
open OUnit2

let arr_of_string s =
  let listl = (Str.split (Str.regexp " ") s) in
  (Array.of_list listl)

let tear_down () text_ctxt =
  VarDOpts.cluster := VarDOpts.cluster_default;
  VarDOpts.me := VarDOpts.me_default;
  VarDOpts.port := VarDOpts.port_default;
  VarDOpts.dbpath := VarDOpts.dbpath_default;
  VarDOpts.debug := VarDOpts.debug_default

let test_parse_correct_line test_ctxt =
  VarDOpts.parse (arr_of_string "./vard.native -dbpath /tmp/vard-8000 -me 0 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 -node 2,localhost:9002");
  assert_equal 0 !VarDOpts.me;
  assert_equal 8000 !VarDOpts.port;
  assert_equal [(0, ("localhost", 9000)); (1, ("localhost", 9001)); (2, ("localhost", 9002))] !VarDOpts.cluster;
  assert_equal "/tmp/vard-8000" !VarDOpts.dbpath;
  assert_equal false !VarDOpts.debug

let test_validate_correct_line test_ctxt =
  VarDOpts.parse (arr_of_string "./vard.native -dbpath /tmp/vard-8000 -me 0 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 -node 2,localhost:9002");
  assert_equal () (VarDOpts.validate ())

let test_validate_missing_me text_ctxt =
  VarDOpts.parse (arr_of_string "./vard.native -dbpath /tmp/vard-8000 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 -node 2,localhost:9002");
  assert_raises (Arg.Bad "Please specify the node name -me") VarDOpts.validate

let test_validate_empty_cluster text_ctxt =
  VarDOpts.parse (arr_of_string "./vard.native -dbpath /tmp/vard-8000 -me 0 -port 8000");
  assert_raises (Arg.Bad "Please specify at least one -node") VarDOpts.validate

let test_validate_me_not_cluster_member text_ctxt =
  VarDOpts.parse (arr_of_string "./vard.native -dbpath /tmp/vard-8000 -me 0 -port 8000 -node 1,localhost:9001 -node 2,localhost:9002");
  assert_raises (Arg.Bad "0 is not a member of this cluster") VarDOpts.validate

let test_list =
  ["parse correct line", test_parse_correct_line;
   "validate correct line", test_validate_correct_line;
   "validate missing me", test_validate_missing_me;
   "validate empty cluster", test_validate_empty_cluster;
   "validate me not member of cluster", test_validate_me_not_cluster_member;
  ]
  
let test_suite =
  "VarDOpts" >:::
    (map test_list ~f:(fun (name, test_fn) ->
      name >:: (fun test_ctxt ->
	bracket ignore tear_down test_ctxt;
	test_fn test_ctxt)
     ))

let _ = run_test_tt_main test_suite
