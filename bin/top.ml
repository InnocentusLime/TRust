let cmds_from_lexbuf l_c =
  let rec gen () =
    try
      let lexbuf = l_c () in
      Some (Ast.toplevel_command Lex.lex lexbuf)
    with
    | Lex.Eof -> None
    | Parsing.Parse_error -> (
      Ui.info "Syntax error\n";
      gen ()
    )
  in
  Seq.of_dispenser gen

let cmds_from_chan ch =
  let l_c () = Lexing.from_channel ch in
  cmds_from_lexbuf l_c

let cmds_from_stdin =
  let l_c () =
    Ui.info "> ";
    Out_channel.flush stdout;
    Lexing.from_channel stdin
  in
  cmds_from_lexbuf l_c

let rec compile_args ctx args =
  match args with
  | [] -> (ctx, [])
  | (name, arg) :: t -> (
    let arg = Conv.IrUnname.compile_term (Conv.IrUnname.translate_ctx_from_typing_ctx ctx) arg in
    let _ = IrDeBrujin.tc ctx arg in
    let (ctx', args') = compile_args (IrDeBrujin.add_var ctx (name, arg)) t in
    (ctx', (name, arg) :: args')
  )

let rec process_command_throw ctx cmd =
  match cmd with
  | TopCmd.Quit -> ctx
  | TopCmd.Reset -> (Ui.info "Context reset.\n"; IrDeBrujin.empty_ctx)
  | TopCmd.Axiom (s, t) -> (
    let t = Conv.IrUnname.compile_term (Conv.IrUnname.translate_ctx_from_typing_ctx ctx) t in
    let _ = IrDeBrujin.tc ctx t in
    Ui.info "Axiom added.\n";
    IrDeBrujin.add_var ctx (s, t)
  )
  | TopCmd.TcIrTerm t -> (
    let t = Conv.IrUnname.compile_term (Conv.IrUnname.translate_ctx_from_typing_ctx ctx) t in
    let typ = IrDeBrujin.tc ctx t in
    Ui.info "Success\nterm : %s\ntype : %s\n"
      (Conv.IrToString.string_of_de_brujin_ir_term (Conv.IrToString.translate_ctx_from_typing_ctx ctx) t)
      (Conv.IrToString.string_of_de_brujin_ir_term (Conv.IrToString.translate_ctx_from_typing_ctx ctx) typ);
    ctx
  )
  | TopCmd.IrDefinition (name, args, body) -> (
    let (body_ctx, args) = compile_args ctx args in
    let body = Conv.IrUnname.compile_term (Conv.IrUnname.translate_ctx_from_typing_ctx body_ctx) body in
    let ret_type = IrDeBrujin.tc body_ctx body in
    let func : IrDeBrujin.func = {
      IrDeBrujin.args = args;
      IrDeBrujin.ret_type = ret_type;
      IrDeBrujin.value = List.fold_right (fun (name, domain) acc -> IrDeBrujin.Abs (name, domain, acc)) args body;
    } in
    Ui.info "%s defined\n" name;
    IrDeBrujin.add_func ctx (name, func)
  )
  | TopCmd.IrPrintDef name -> (
    let func = (IrDeBrujin.dispatch_func ctx name) in
    Ui.info "%s\n : %s\n"
      (Conv.IrToString.string_of_de_brujin_ir_term (Conv.IrToString.translate_ctx_from_typing_ctx ctx) func.IrDeBrujin.value)
      (
        Conv.IrToString.string_of_de_brujin_ir_term
        (Conv.IrToString.translate_ctx_from_typing_ctx ctx)
        (IrDeBrujin.build_product func.IrDeBrujin.args func.IrDeBrujin.ret_type)
      );
    ctx
  )
  | TopCmd.IrIsConv (l, r) -> (
    let l = Conv.IrUnname.compile_term (Conv.IrUnname.translate_ctx_from_typing_ctx ctx) l
    and r = Conv.IrUnname.compile_term (Conv.IrUnname.translate_ctx_from_typing_ctx ctx) r in
    let l_typ = (IrDeBrujin.tc ctx l)
    and r_typ = (IrDeBrujin.tc ctx r) in
    if IrDeBrujin.conv ctx l_typ r_typ then Ui.info "Answer: %B\n" (IrDeBrujin.conv ctx l r)
    else Ui.info "Can't check for conversion of terms of two different types.\n";
    ctx
  )
  | TopCmd.IrSimpl x -> (
    let x = Conv.IrUnname.compile_term (Conv.IrUnname.translate_ctx_from_typing_ctx ctx) x in
    let _ = (IrDeBrujin.tc ctx x) in
    let nf = (IrDeBrujin.find_nf ctx x) |> Option.get in
    Ui.info "Answer: %s\n"
      (
        Conv.IrToString.string_of_de_brujin_ir_term
        (Conv.IrToString.translate_ctx_from_typing_ctx ctx)
        nf
      );
    ctx
  )
  | TopCmd.IrLoadModule _path -> failwith "todo"
  | TopCmd.Help -> (
    Ui.info "%s"
    (
      "\
      quit --- exit TRust toplevel\n\
      reset --- reset the current global context, making it empty\n\
      axiom [IDENT] : [TYPE] --- add a variable named [IDENT] of type [TYPE] to global context, essentially making an axiom\n\
      tc_ir_term [TERM] --- typecheck [TERM] and print its type\n\
      ir_def [IDENT] (arg1 : T1) ... (argn : Tn) = [TERM] --- declare a function with body equal to [TERM]\n\
      ir_print_def [IDENT] --- print body of function [IDENT]\n\
      ir_is_conv [TERM] [TERM] --- check if the two terms are convertible\n\
      ir_simpl [TERM] --- compute normal form of a term (note: non-halting terms will make this command work infinitely)\n\
      ir_load_mod [PATH_IN_QUOTES] --- load a TRust module, essentially exeucting all commands inside it\n\
      help --- prints this message\n\
      "
    );
    ctx
  )
and process_command ctx cmd =
  try process_command_throw ctx cmd
  with
  | Failure s -> (Printf.printf "Failure:\n%s\n" s; ctx)
  | _ -> (Printf.printf "Err\n"; ctx)
and run ctx cmd_seq =
  let prc ctx cmd =
    let res = process_command ctx cmd in
    Out_channel.flush stdout; res
  in
  cmd_seq |>
    Seq.take_while (fun x -> not (TopCmd.is_quit x)) |>
    Seq.fold_left prc ctx
