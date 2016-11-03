open OUnit2

let parse_line line =
  let listl = (Str.split (Str.regexp " ") line) in
  (Array.of_list listl)

let tear_down () text_ctxt =
  VarDOpts.cluster := VarDOpts.cluster_default;
  VarDOpts.me := VarDOpts.me_default;
  VarDOpts.port := VarDOpts.port_default;
  VarDOpts.dbpath := VarDOpts.dbpath_default;
  VarDOpts.debug := VarDOpts.debug_default

let parse_correct_line test_ctxt =
  VarDOpts.parse (parse_line "./vard.native -dbpath /tmp/vard-8000 -me 0 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 -node 2,localhost:9002");
  assert_equal 0 !VarDOpts.me;
  assert_equal 8000 !VarDOpts.port;
  assert_equal [(0, ("localhost", 9000)); (1, ("localhost", 9001)); (2, ("localhost", 9002))] !VarDOpts.cluster;
  assert_equal "/tmp/vard-8000" !VarDOpts.dbpath;
  assert_equal false !VarDOpts.debug

let validate_correct_line test_ctxt =
  VarDOpts.parse (parse_line "./vard.native -dbpath /tmp/vard-8000 -me 0 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 -node 2,localhost:9002");
  assert_equal () (VarDOpts.validate ())

let validate_missing_me text_ctxt =
  VarDOpts.parse (parse_line "./vard.native -dbpath /tmp/vard-8000 -port 8000 -node 0,localhost:9000 -node 1,localhost:9001 -node 2,localhost:9002");
  assert_raises (Arg.Bad "Please specify the node name -me") VarDOpts.validate
  

let suite = "vard" >:::
[
  "parse correct line" >:: (fun test_ctxt -> bracket ignore tear_down test_ctxt; parse_correct_line test_ctxt);

  "validate correct line" >:: (fun test_ctxt -> bracket ignore tear_down test_ctxt; validate_correct_line test_ctxt);
  
  "validate missing me" >:: (fun test_ctxt -> bracket ignore tear_down test_ctxt; validate_missing_me test_ctxt);
 
]

let _ = run_test_tt_main suite
