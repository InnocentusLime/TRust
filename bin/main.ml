let usage_msg = "trust [-v] [-q] [-Q] [file1] [file2] ..."
let quit_on_done = ref false
let modules = ref []

let anon_fun filename =
  modules := filename :: !modules

let speclist =
  [("-v", Arg.Set Ui.verbose, "Print debug information");
   ("-q", Arg.Set Ui.quiet, "Quiet mode");
   ("-Q", Arg.Set quit_on_done, "Quit when done executing")]

let () =
  Arg.parse speclist anon_fun usage_msg;
  Ui.debug "Verbose: %B\nQuit-on-done:%B\nModules:\n" !Ui.verbose !Ui.quiet;
  List.fold_right (fun x () -> Ui.debug "* %s\n" x) !modules ();
  Ui.info "Welcome to TRust. Type `help.` for available commands\n";
  Top.run (Top.make_empty_ctx ()) |> fun _ -> ()
