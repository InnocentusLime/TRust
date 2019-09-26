open LambdaLex;;
open LambdaAst;;
open ReprConversion;;

let retrive_args () =
	let mode = 
		if Array.length Sys.argv >= 2 then Array.get Sys.argv 1 else (Printf.printf "Enter mode \n"; read_line ())
	and file = 
		if Array.length Sys.argv >= 3 then Array.get Sys.argv 2
		else (Printf.printf "Enter file name\n"; read_line ())
	in
	(mode, file)
;;

let read_file_contents file_name =
	if file_name = "#stdin" then read_line ()
	else (
		let chan = open_in_bin file_name in
		let n = in_channel_length chan in
		let s = really_input_string chan n in
		(close_in chan; s)
	)
;;

let print_result t =
	match t with
	| Some t -> Printf.printf "Ok: %s\n" (t |> ReprConversion.IrToPreIr.convert_type |> PreIr.string_of_type)
	| None -> Printf.printf "Err\n"
;;
 
let () = 
	let (mode, file_name) = retrive_args () in
	let contents = read_file_contents file_name in
	match mode with
	| "test_renaming" -> contents |> Lexing.from_string |> lambda_term lex |> PreIrToIr.convert_term |> IrToPreIr.convert_term |> PreIr.string_of_term |> Printf.printf "%s\n"
	| "simply_typed_tc" -> contents |> Lexing.from_string |> lambda_term lex |> PreIrToIr.convert_term |> Ir.simply_typed_typecheck |> print_result
	| "verify" -> contents |> Lexing.from_string |> lambda_term lex |> PreIrToIr.convert_term |> Typing.verify
	| _ -> Printf.printf "I don't understand you\n"
;;
