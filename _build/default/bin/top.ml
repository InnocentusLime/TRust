let rec compile_args ctx args =
  match args with
  | [] -> (ctx, [])
  | (name, arg) :: t -> (
    let arg = Conv.IrUnname.compile_term (Conv.IrUnname.translate_ctx_from_typing_ctx ctx) arg in
    let _ = IrDeBrujin.tc ctx arg in
    let (ctx', args') = compile_args (IrDeBrujin.add_var ctx (name, arg)) t in
    (ctx', (name, arg) :: args')
  )

(* The top-level for the TRust *)
let read_command_terminal () =
  let cmd = ref TopCmd.Quit
  and success = ref false in
  while not !success do
    try (
      print_string "> ";
      let s = read_line () in
      let result = Ast.toplevel_command Lex.lex (Lexing.from_string s) in
      success := true; cmd := result
    ) with Parsing.Parse_error -> Printf.printf "Failed to parse command.\n"
  done;
  !cmd

let read_subcommand_terminal () = print_string ">> "; read_line ()

let read_arg_terminal () = print_string ">>> "; read_line ()

let rec execute_command ctx cmd =
    match cmd with
    | TopCmd.Quit -> ()
    | TopCmd.Reset -> (Printf.printf "Context reset.\n"; ctx := IrDeBrujin.empty_ctx)
    | TopCmd.Axiom (s, t) -> (
      try (
        let t = Conv.IrUnname.compile_term (Conv.IrUnname.translate_ctx_from_typing_ctx !ctx) t in
        let _ = IrDeBrujin.tc !ctx t in
        ctx := IrDeBrujin.add_var !ctx (s, t);
        Printf.printf "Axiom added.\n"
      ) with 
      | Parsing.Parse_error -> Printf.printf "Syntax error\n"
      | Failure s -> Printf.printf "Failured:\n%s\n" s
      | _ -> Printf.printf "Err\n"
    )
    | TopCmd.TcIrTerm t -> (
      try (
        let t = Conv.IrUnname.compile_term (Conv.IrUnname.translate_ctx_from_typing_ctx !ctx) t in
        let typ = IrDeBrujin.tc !ctx t in
        Printf.printf "Success\nterm : %s\ntype : %s\n" 
        (Conv.IrToString.string_of_de_brujin_ir_term (Conv.IrToString.translate_ctx_from_typing_ctx !ctx) t) 
        (Conv.IrToString.string_of_de_brujin_ir_term (Conv.IrToString.translate_ctx_from_typing_ctx !ctx) typ)
      ) with
      | Parsing.Parse_error -> Printf.printf "Syntax error\n"
      | Failure s -> Printf.printf "Failured:\n%s\n" s
      | _ -> Printf.printf "Err\n"
    )
    | TopCmd.IrDefinition (name, args, body) -> (
      try (
        let (body_ctx, args) = compile_args !ctx args in
        let body = Conv.IrUnname.compile_term (Conv.IrUnname.translate_ctx_from_typing_ctx body_ctx) body in
        let ret_type = IrDeBrujin.tc body_ctx body in
        let func : IrDeBrujin.func = {
          IrDeBrujin.args = args;
          IrDeBrujin.ret_type = ret_type;
          IrDeBrujin.value = List.fold_right (fun (name, domain) acc -> IrDeBrujin.Abs (name, domain, acc)) args body;
        } in
        ctx := IrDeBrujin.add_func !ctx (name, func);
        Printf.printf "%s defined\n" name;
      ) with
      | Parsing.Parse_error -> Printf.printf "Syntax error\n"
      | Failure s -> Printf.printf "Failured:\n%s\n" s
      | _ -> Printf.printf "Err\n"
    )
    | TopCmd.IrPrintDef name -> (
      try (
        let func = (IrDeBrujin.dispatch_func !ctx name) in
        Printf.printf "%s\n : %s\n"
        (Conv.IrToString.string_of_de_brujin_ir_term (Conv.IrToString.translate_ctx_from_typing_ctx !ctx) func.IrDeBrujin.value)
        (
          Conv.IrToString.string_of_de_brujin_ir_term 
          (Conv.IrToString.translate_ctx_from_typing_ctx !ctx) 
          (IrDeBrujin.build_product func.IrDeBrujin.args func.IrDeBrujin.ret_type)
        );
      ) with
      | Failure s -> Printf.printf "Failure:\n%s\n" s
      | _ -> Printf.printf "Err\n" 
    )
and execute_file ctx path =
  let old_ctx = !ctx in
  let chan = open_in_bin path in
  let lexing = Lexing.from_channel chan in
  let cmd = ref None in
  try (
    while (cmd := Ast.maybe_toplevel_command Lex.lex lexing; !cmd <> None && !cmd <> Some TopCmd.Quit) do
      execute_command ctx (Option.get !cmd)
    done; 
    Printf.printf "Done!\nReason: ";
    (
      match !cmd with
      | None -> Printf.printf "Reached end of file\n"
      | Some TopCmd.Quit -> Printf.printf "Reached a `quit` command\n"
      | Some _ -> failwith "Unreachable\n"
    );
    !ctx
  )
  with 
  | _ -> (
    Printf.printf "Encountered an error when executing the file\n";
    old_ctx
  )

let top_level_main command_reader ctx =
  let cmd = ref TopCmd.Quit in
  while (cmd := command_reader (); !cmd) <> TopCmd.Quit do
    execute_command ctx !cmd
  done;
  !ctx

let top_level_main_terminal ctx = top_level_main read_command_terminal ctx

let top_level_main_file ctx path = top_level_main_terminal (ref (execute_file ctx path))

let allocate_ctx () = ref IrDeBrujin.empty_ctx
