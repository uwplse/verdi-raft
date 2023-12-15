open OUnit2

let () =
  run_test_tt_main 
    ~exit
    ("VarDLog" >:::
	[
          OptsTest.tests;
          VarDLogSerializationTest.tests
	])
