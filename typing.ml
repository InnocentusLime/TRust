(*
	the data types which encode the typing
	trees, subtyping trees and proof trees 
	of the tool.
*)
open Ir;;

type typing =
| IVar of int
| IAbs of string * type_ast * typing
| IApp of typing * typing
| INatO
| INatSucc
and proof =
| PTt
| PEqRefl of term_ast * type_ast * typing
and subtyping =
| SRefl of type_ast
| STrans of subtyping * subtyping
;;

type prooving_command =
| ApplyTt
| ApplyEqRefl
;;

type typing_type = context * prop_ast list * term_ast * type_ast;;
type subtyping_type = context * prop_ast list * type_ast * type_ast;;
type proof_type = context * prop_ast list * prop_ast;;

let list_set_eq l r = List.for_all (fun x -> List.mem x r) l && List.for_all (fun x -> List.mem x l) r;;

let rec typecheck_typing t ctx h =
	match t with
	| INatO -> Some ((ctx, h, NatO, Nat))
	| INatSucc -> Some ((ctx, h, NatSucc, Map ("_", Nat, Nat)))
	| IAbs (v, arg_t, r) -> (
		let ctx_a = push_var v (Data arg_t) ctx in
		match (typecheck_typing r ctx_a h) with
		| Some ((ctx_b, h', r_term, r_type)) when ctx_a = ctx_b && (list_set_eq h h') && is_type_small arg_t -> Some ((ctx, h, Abs (v, arg_t, r_term), Map (v, arg_t, r_type))) 
		| _ -> None
	)
	| IApp (l, r) -> (
		match (typecheck_typing l ctx h, typecheck_typing r ctx h) with
		| (Some ((ctx_a, h_a, l_term, Map (v, l_type_domain, l_type_res))), Some ((ctx_b, h_b, r_term, r_type))) 
			when ctx = ctx_a && ctx = ctx_b && list_set_eq h h_a && list_set_eq h h_b && l_type_domain = r_type && is_type_small r_type 
				-> Some ((ctx, h, App (l_term, r_term), clean_after_unbind_type l_type_res))
		| _ -> None	
	)
	| IVar v -> ( 
		match fetch_var ctx v with
		| Some (Data x) -> Some ((ctx, h, Var v, x))
		| _ -> None
	)
and typecheck_proof t ctx h =
	match t with
	| PTt -> Some ((ctx, h, Top))
	| PEqRefl (tm, t, x) -> (
		match typecheck_typing x ctx h with
		| Some ((ctx', h', tm', t')) when ctx' = ctx && list_set_eq h' h && tm' = tm && t' = t -> Some ((ctx, h, Eq (tm, tm, t)))
		| _ -> None
	)
and typecheck_subtyping t ctx h =
	match t with
	| SRefl typ -> Some ((ctx, h, typ, typ))
	| STrans (l, r) -> failwith "unimplemented"
;;  

let read_term ctx =
	let ctx' = ReprConversion.PreIrToIr.index_context_from_ir_typing_context ctx in
	read_line () |> Lexing.from_string |> LambdaAst.lambda_term LambdaLex.lex |> (fun x -> ReprConversion.PreIrToIr.convert_term_ctx x ctx')
;;

let read_proof_mode_command ctx h = 
	let input = read_line () in
	match input with
	| "tt" -> ApplyTt
	| "eq_refl" -> ApplyEqRefl
	| _ -> failwith "THE FUCK YOU SAID TO ME, YOU LITTLE SHIT"
;;                                                                                                                            

let rec consider_app_problem ctx li ri tm1 t1 tm2 t2 =
	Printf.printf "Dummy implementation. Generating an answer, which may not work.\n";
	IApp (li, ri)
and interactive_typing ctx h t =
	match t with
	| Var v ->  IVar v
	| NatO -> INatO
	| NatSucc -> INatSucc
	| App (l, r) -> (
		let (li, ri) = (interactive_typing ctx h l, interactive_typing ctx h r) in
		match (typecheck_typing li ctx h, typecheck_typing ri ctx h) with
		| (Some ((ctx1, h1, tm1, t1)), Some ((ctx2, h2, tm2, t2))) when ctx1 = ctx && ctx2 = ctx && list_set_eq h1 h && list_set_eq h2 h -> consider_app_problem ctx li ri tm1 t1 tm2 t2
		| _ -> failwith "failed to type"
	)
	| Abs (v, arg_t, body) -> (
		let ctx' = ctx |> push_var v (Data arg_t) in
		let i = interactive_typing ctx' h body in
		let c = typecheck_typing i ctx' h in
		match c with
		| Some ((ctx, h', tm, typ)) when ctx = ctx' && list_set_eq h h' && tm = body -> IAbs (v, arg_t, i)
		| _ -> failwith "failed to type"
	)
	| _ -> failwith "not supported"
and interactive_proving ctx h t = 
	(
		let ctx' = ReprConversion.IrToPreIr.naming_context_from_ir_typing_context ctx in
		ReprConversion.IrToPreIr.convert_prop_ctx t ctx' |> PreIr.string_of_prop |> Printf.printf "Goal: %s\n"
	);
	let cmd = (Printf.printf "Enter proof command\n>"; read_proof_mode_command ctx h) in
	match (t, cmd) with
	| (Top, ApplyTt) -> PTt
	| (Eq (l_tm_target, r_tm_target, target_typ), ApplyEqRefl) -> (
		if l_tm_target = r_tm_target then (
			let i = interactive_typing ctx h l_tm_target in
			match (typecheck_typing i ctx h) with
			| Some ((ctx', h', tm, typ)) when ctx = ctx' && list_set_eq h h' && tm = l_tm_target && typ = target_typ -> PEqRefl (tm, typ, i)
			| _ -> failwith "failed to type the term"
		) else failwith "Can't proof this equality with reflexivity, because left and right sides are not the same" 
	)
	| _ -> failwith "Unimplemented"
;;

let verify t =
	let ctx' = create_empty_context ()
	and h' = [] in
	let i = interactive_typing ctx' h' t |> fun x -> typecheck_typing x ctx' h' in
	match i with
	| Some ((ctx, h, tm, typ)) when ctx = ctx' && h = h' && tm = t -> Printf.printf "Ok\n"
	| _ -> Printf.printf "Failed to verify\n"
;;