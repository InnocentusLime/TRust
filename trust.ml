open ExplicitTyping
open ReprConversion

let file_requiring_modes = ["test_renaming"; "reduction_step"; "normal_form"; "check"; "reprint"; "normal_form_notred"; "naive"; "check_simpl"]

let retrive_args () =
	let mode = 
		if Array.length Sys.argv >= 2 then Array.get Sys.argv 1 else (Printf.printf "Enter mode \n"; read_line ())
	in
	let file =
		if List.mem mode file_requiring_modes then ( 
			if Array.length Sys.argv >= 3 then Array.get Sys.argv 2
			else (Printf.printf "Enter file name\n"; read_line ())
		) else "con"
	in
	(mode, file)

let read_file_contents file_name =
	if file_name = "#stdin" then read_line ()
	else (
		let chan = open_in_bin file_name in
		let n = in_channel_length chan in
		let s = really_input_string chan n in
		(close_in chan; s)
	)

let print_result x = 
	match x with
	| Some x -> x |> IrToPreIr.convert_term |> PreIrToStr.convert_term |> Printf.printf "%s\n"
	| None -> Printf.printf "Failed to typecheck\n"

let () = 
	let (mode, file_name) = retrive_args () in
	match mode with
	| "naive" -> file_name |> read_file_contents |> StrToPreIr.convert_str |> PreIrToStr.convert_term |> Printf.printf "%s\n"
	| "reprint" -> file_name |> read_file_contents |> StrToPreIr.convert_str |> PreIrToIr.convert_term |> IrToPreIr.convert_term |> PreIrToStr.convert_term |> Printf.printf "%s\n"
	| "test_renaming" -> file_name |> read_file_contents |> StrToPreIr.convert_str |> PreIrToIr.convert_term |> IrToPreIr.convert_term |> PreIrToStr.convert_term |> Printf.printf "%s\n"
	| "reduction_step" -> file_name |> read_file_contents |> StrToPreIr.convert_str |> PreIrToIr.convert_term |> Ir.reduction_step |> IrToPreIr.convert_term |> PreIrToStr.convert_term |> Printf.printf "%s\n"
	| "normal_form" -> file_name |> read_file_contents |> StrToPreIr.convert_str |> PreIrToIr.convert_term |> Ir.find_normal_form ~notation_reduction:false |> IrToPreIr.convert_term |> PreIrToStr.convert_term |> Printf.printf "%s\n"
	| "normal_form_notred" -> file_name |> read_file_contents |> StrToPreIr.convert_str |> PreIrToIr.convert_term |> Ir.find_normal_form |> IrToPreIr.convert_term |> PreIrToStr.convert_term |> Printf.printf "%s\n"
	| "check" -> file_name |> read_file_contents |> StrToPreIr.convert_str |> PreIrToIr.convert_term |> typecheck_ctxless |> print_result
	| "check_simpl" -> file_name |> read_file_contents |> StrToPreIr.convert_str |> PreIrToIr.convert_term |> typecheck_ctxless >>= (fun x -> Some (Ir.find_normal_form ~notation_reduction:false x)) |> print_result
(*	| "verify" -> contents |> Lexing.from_string |> lambda_term lex |> PreIrToIr.convert_term |> Typing.verify *)
	| _ -> Printf.printf "I don't understand you\n"