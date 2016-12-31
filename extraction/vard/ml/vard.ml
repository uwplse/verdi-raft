open List
open Printf
open Str
open Opts

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
  let module NumNodes : VarDArrangement.IntValue = 
      struct let v = length !cluster end
  in
  if !debug then
    let module VarD = (Shim.Shim(VarDArrangement.VarDArrangement(VarDArrangement.DebugParams(NumNodes)))) in
    let open VarD in
    main { cluster = !cluster
         ; me = !me
         ; port = !port
         ; dbpath = !dbpath
         }
  else
    let module VarD = Shim.Shim(VarDArrangement.VarDArrangement(VarDArrangement.BenchParams(NumNodes))) in
    let open VarD in
    main { cluster = !cluster
         ; me = !me
         ; port = !port
         ; dbpath = !dbpath
         }
