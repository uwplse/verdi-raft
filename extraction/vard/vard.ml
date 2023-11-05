open List
open Printf
open Opts

let _ =
  let _ =
    try
      parse Sys.argv
    with
    | Arg.Help msg ->
      printf "%s: %s" Sys.argv.(0) msg;
      exit 2
    | Arg.Bad msg ->
      eprintf "%s" msg;
      exit 2
  in
  let _ =
    try
      validate ();
      if length !cluster < 2 then raise (Arg.Bad "Cluster size must be two or greater")
    with Arg.Bad msg ->
      eprintf "%s: %s" Sys.argv.(0) msg;
      prerr_newline ();
      exit 2
  in
  let module NumNodes =
      struct
	let v = length !cluster
      end
  in
  let module Params =
	(val (if !debug then
	    (module VarDArrangement.DebugParams(NumNodes) : VarDArrangement.VarDParams)
	  else
	    (module VarDArrangement.BenchParams(NumNodes) : VarDArrangement.VarDParams)))
  in
  let module VarD = Shim.Shim(VarDArrangement.VarDArrangement(Params)) in
  let open VarD in
  main { cluster = !cluster
       ; me = !me
       ; port = !port
       ; dbpath = !dbpath
       }