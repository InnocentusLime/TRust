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

let check_0_eq_0_proof x =
	match x with
	| Some (Typing.Proof (ctx, h, prp)) when ctx = Ir.create_empty_context () && h = [] && prp = Ir.Eq (Ir.NatO, Ir.NatO, Ir.Nat) -> Printf.printf "OH MY"
	| _ -> Printf.printf "INYA, FIX YOUR FAULTY CODE"
;;
 
let () = 
	let (mode, file_name) = retrive_args () in
	let contents = read_file_contents file_name in
	match mode with
	| "test_renaming" -> contents |> Lexing.from_string |> lambda_term lex |> PreIrToIr.convert_term |> IrToPreIr.convert_term |> PreIr.string_of_term |> Printf.printf "%s\n"
	| "simply_typed_tc" -> contents |> Lexing.from_string |> lambda_term lex |> PreIrToIr.convert_term |> Ir.simply_typed_typecheck |> print_result
	| "reduction_step" -> contents |> Lexing.from_string |> lambda_term lex |> PreIrToIr.convert_term |> Ir.reduction_step |> IrToPreIr.convert_term |> PreIr.string_of_term |> Printf.printf "%s\n"
	| "0_eq_0_proof" -> Typing.interactive_proving (Ir.create_empty_context ()) [] (Ir.Eq (Ir.NatO, Ir.NatO, Ir.Nat)) |> (fun x -> Typing.typecheck_proof x (Ir.create_empty_context ()) []) |> check_0_eq_0_proof
	| "0_eq_1_obvious_fail" ->  (Printf.printf "Try `eq_refl` :)\n"; try Typing.interactive_proving (Ir.create_empty_context ()) [] (Ir.Eq (Ir.NatO, Ir.App (Ir.NatSucc, Ir.NatO), Ir.Nat)) |> (fun x -> Typing.typecheck_proof x (Ir.create_empty_context ()) []) |> (fun x -> ()) with Failure s -> Printf.printf "%s\nsee, you failed with `eq_refl`. That was supposed to happen!" s)
	| "verify" -> contents |> Lexing.from_string |> lambda_term lex |> PreIrToIr.convert_term |> Typing.verify
	| _ -> Printf.printf "I don't understand you\n"
;;
