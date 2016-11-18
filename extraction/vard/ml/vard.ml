open List
open Printf
open Str
open Opts

module VarDDebug = Shim.Shim(VarDArrangement.VarDArrangement(VarDArrangement.DebugParams))
module VarDBench = Shim.Shim(VarDArrangement.VarDArrangement(VarDArrangement.BenchParams))

let _ =
  let  _ = parse Sys.argv in

  let _ =
    try
      validate ()
    with Arg.Bad msg ->
      eprintf "%s: %s." Sys.argv.(0) msg;
      prerr_newline ();
      exit 2
  in

  if !debug then
    let open VarDDebug in
    main { cluster = !cluster
         ; me = !me
         ; port = !port
         ; dbpath = !dbpath
         }
  else
    let open VarDBench in
    main { cluster = !cluster
         ; me = !me
         ; port = !port
         ; dbpath = !dbpath
         }
