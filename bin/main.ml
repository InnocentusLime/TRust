type test_type =
| TestWhatsUsed of string
| TestTarjan of string
| TestCompile of string
| TestCompileTc of string
| TestFetchComments of string
| TestBuildEffect of string
| TestCompileETc of string

type launch_reason =
| Test of test_type
| Run
| RunFile of string

let arg_count = Array.length Sys.argv

let get_path_for_whats_used_test () =
  if arg_count > 3 then (
    let path = Sys.argv.(3) in
    Some (Test (TestWhatsUsed path))
  ) else None

let get_path_for_tarjan_test () =
  if arg_count > 3 then (
    let path = Sys.argv.(3) in
    Some (Test (TestTarjan path))
  ) else None

let get_path_for_compile_test () =
  if arg_count > 3 then (
    let path = Sys.argv.(3) in
    Some (Test (TestCompile path))
  ) else None

let get_path_for_compile_test_tc () =
  if arg_count > 3 then (
    let path = Sys.argv.(3) in
    Some (Test (TestCompileTc path))
  ) else None

let get_path_for_fetch_comments_test () =
  if arg_count > 3 then (
    let path = Sys.argv.(3) in 
    Some (Test (TestFetchComments path))
  ) else None

let get_path_for_build_effectful_typ_test () =
  if arg_count > 3 then (
    let path = Sys.argv.(3) in
    Some (Test (TestBuildEffect path))
  ) else None

let get_path_for_compile_test_etc () =
  if arg_count > 3 then (
    let path = Sys.argv.(3) in
    Some (Test (TestCompileETc path))
  ) else None

let get_test_type () =
  if arg_count > 2 then (
    match Sys.argv.(2) with
    | "whats_used" -> get_path_for_whats_used_test ()
    | "tarjan" -> get_path_for_tarjan_test ()
    | "compile" -> get_path_for_compile_test ()
    | "compile_tc" -> get_path_for_compile_test_tc ()
    | "fetch_comments" -> get_path_for_fetch_comments_test ()
    | "build_effectful_typ" -> get_path_for_build_effectful_typ_test ()
    | "compile_etc" -> get_path_for_compile_test_etc ()
    | _ -> None
  ) else None

let get_run_type () =
  if arg_count > 2 then Some (RunFile (Sys.argv.(2)))  
  else Some Run

let get_launch_reason () =
  if arg_count > 1 then (
    match Sys.argv.(1) with
    | "test" -> get_test_type ()
    | "run" -> get_run_type ()
    | _ -> None
  ) else None

let launch_test t =
  match t with
  | TestWhatsUsed path -> (
    let chan = open_in_bin path in
    Ast.rust_file Lex.lex (Lexing.from_channel chan) |>
    Conv.RustUnname.reference_hierarchy |>
    Hashtbl.iter (
      fun key value ->
      Printf.printf "%s: [%s]\n" key (String.concat " " value)
    ); 
    close_in chan 
  ) 
  | TestTarjan path -> (
    let chan = open_in_bin path in
    Ast.rust_file Lex.lex (Lexing.from_channel chan) |>
    Conv.RustUnname.reference_hierarchy |>
    Conv.RustUnname.tarjan |>
    fun value -> 
    Printf.printf 
    "%s\n" 
    (
      String.concat 
      "\n" 
      (
        List.map 
        (
          fun x -> 
          Printf.sprintf 
          "[%s]" 
          (String.concat ", " x)
        ) 
        value
      )
    );
    close_in chan
  )
  | TestCompile path -> (
    let chan = open_in_bin path in
    let contents =
      Ast.rust_file Lex.lex (Lexing.from_channel chan) |>
      Conv.RustUnname.compile_file Conv.RustUnname.empty_ctx |> 
      List.map (RustDeBrujin.string_of_func) |>
      String.concat "\n" |>
      Printf.sprintf "%s\n"
    in
    close_in chan;
    let chan = open_out_bin (path ^ ".out") in
    Printf.fprintf chan "%s" contents;
    close_out chan
  )
  | TestCompileTc path -> (
    let chan = open_in_bin path in
    Ast.rust_file Lex.lex (Lexing.from_channel chan) |>
    Conv.RustUnname.compile_file Conv.RustUnname.empty_ctx |>
    RustDeBrujin.load_module RustDeBrujin.empty_ctx |>
    fun _ -> ();
    close_in chan;
    Printf.printf "File TC'ed successfully\n" 
  )
  | TestFetchComments path -> (
    let sep = String.init 64 (fun _ -> '=') in
    let chan = open_in_bin path in
    Ast.rust_file Lex.lex (Lexing.from_channel chan) |>
    Conv.RustUnname.fetch_comments_attached_to_funcs |>
    Hashtbl.iter (fun k c -> Printf.printf "COMMENTS FOR: %s\n%s\n%s\n" k (String.concat "\n" c) sep);
    close_in chan
  )
  | _ -> failwith "todo"

let launch r =
  match r with
  | Test t -> launch_test t
  | Run -> Top.top_level_main_terminal (Top.make_empty_ctx ()) |> fun _ -> ()
  | RunFile file -> Top.top_level_main_file (Top.make_empty_ctx ()) file |> fun _ -> ()

let help_message () =
  Printf.printf "This message is displayed either when you provide wrong args or call `trust help`\n";
  Printf.printf "Here are the avaliable commands:\n";
  Printf.printf "- trust run\n";
  Printf.printf "- trust test whats_used [PATH]\n";
  Printf.printf "- trust test tarjan [PATH]\n";
  Printf.printf "- trust test compile [PATH]\n";
  Printf.printf "- trust test compile_tc [PATH]\n"

let () =
  let reason = get_launch_reason () in
  (
    match reason with
    | Some r -> (Printf.printf "Launching...\n"; launch r)
    | None -> help_message ()
  ); Printf.printf "TRust has successuly terminated!\n"
