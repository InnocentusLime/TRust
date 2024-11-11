let usage_msg = "trust [-v] [-q] [-Q] [file1] [file2] ..."
let verbose = ref false
let quiet = ref false
let quit_on_done = ref false
let modules = ref []

let anon_fun filename =
  modules := filename :: !modules

let speclist =
  [("-v", Arg.Set verbose, "Print debug information");
   ("-q", Arg.Set quiet, "Quiet mode");
   ("-Q", Arg.Set quit_on_done, "Quit when done executing")]

let () =
  Arg.parse speclist anon_fun usage_msg;
  Top.run (Top.make_empty_ctx ()) |> fun _ -> ()
