let usage_msg = "trust [-v] [-q] [-Q] [file1] [file2] ..."
let quit_on_done = ref false
let modules = ref []

let anon_fun filename =
  modules := filename :: !modules

let speclist =
  [("-v", Arg.Set Ui.verbose, "Print debug information");
   ("-q", Arg.Set Ui.quiet, "Quiet mode");
   ("-Q", Arg.Set quit_on_done, "Quit when done executing")]

let try_mod f =
  try Some (In_channel.open_bin f)
  with Sys_error x -> (Ui.info "Failed to open \"%s\": %s\n" f x; None)

let build_cmd_stream files =
  let file_cmds =
    files |> List.filter_map try_mod
          |> List.map Top.cmds_from_chan
          |> List.fold_left Seq.append Seq.empty
  in
  if !quit_on_done then file_cmds
  else Seq.append file_cmds Top.cmds_from_stdin

let () =
  Arg.parse speclist anon_fun usage_msg;
  Ui.debug "Verbose: %B\nQuit-on-done:%B\nModules:\n" !Ui.verbose !Ui.quiet;
  List.fold_right (fun x () -> Ui.debug "* %s\n" x) !modules ();
  Ui.info "Welcome to TRust. Type `help.` for available commands\n";
  Out_channel.flush stdout;
  Top.run IrDeBrujin.empty_ctx (build_cmd_stream !modules) |> ignore
