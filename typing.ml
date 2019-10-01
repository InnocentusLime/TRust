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
| INil
| INatO
| INatSucc
| ISubtype of typing * subtyping
| IProofMem of typing * type_ast * proof
and proof =
| PTt
| PEqRefl of term_ast * type_ast * typing
| PExtractProof of term_ast * type_ast * typing
| PAnd of proof * proof
| POrLeft of proof * prop_ast
| POrRight of proof * prop_ast
| PImplies of prop_ast * proof
| PAssumption of prop_ast
| PForall of string * type_ast * proof
| PExists of string * type_ast * prop_ast * proof * typing
| PExistsProofProj of proof
| PForallElim of proof * typing
| PImpliesElim of proof * proof
| PAndElim of proof * proof
| POrElim of proof * proof * proof
| PEqSymm of proof
| PEqTrans of proof * proof
| PEqRedL of proof
| PEqRedR of proof
| PEqRedRevL of proof * term_ast
| PEqRedRevR of proof * term_ast
and subtyping =
| SRefl of type_ast
| STrans of subtyping * subtyping
| SUnrefine of type_ast
;;

type prooving_command =
| ApplyTt
| ApplyEqRefl
| ApplyAnd
| ApplyOrL
| ApplyOrR
| ApplyImplication
| ApplyAssumption
| ApplyExistsProof
| ApplyForallProof
| ApplyExistsExtraction
| ApplyForallElimination
| ApplyAndElim of prop_ast * prop_ast
| ApplyImplicationElim of prop_ast
| ApplyOrElim of prop_ast * prop_ast
| ApplyEqRedRevL
| ApplyEqRedRevR
| ApplyEqRedL of term_ast
| ApplyEqRedR of term_ast
| ApplyEqSymm
| ApplyEqTrans of term_ast
;;
type subtyping_command =
| ApplySubRefl
| ApplySubTrans of type_ast
type typing_command =
| ApplySubtype
| ApplyMemProof
;;

type typing_type = context * prop_ast list * term_ast * type_ast;;
type subtyping_type = context * prop_ast list * type_ast * type_ast;;
type proof_type = context * prop_ast list * prop_ast;; 

let string_of_bool x = if x then "true" else "false";;
let list_set_eq l r = List.for_all (fun x -> List.mem x r) l && List.for_all (fun x -> List.mem x l) r;;

let rec typecheck_typing t ctx h =
	match t with
	| INil -> Some (ctx, h, Nil, Unit)
	| INatO -> Some ((ctx, h, NatO, Nat))
	| INatSucc -> Some ((ctx, h, NatSucc, Map ("_", Nat, Nat)))
	| IAbs (v, arg_t, r) -> (
		let ctx_a = push_var v (Data arg_t) ctx in
		match (typecheck_typing r ctx_a h) with
		| Some ((ctx_b, h', r_term, r_type)) 
			when ctx_a = ctx_b && (list_set_eq h h') && is_type_small arg_t 
				-> Some ((ctx, h, Abs (v, arg_t, r_term), Map (v, arg_t, r_type))) 
		| _ -> None
	)
	| IApp (l, r) -> (
		match (typecheck_typing l ctx h, typecheck_typing r ctx h) with
		| (Some ((ctx_a, h_a, l_term, Map (v, l_type_domain, l_type_res))), Some ((ctx_b, h_b, r_term, r_type))) 
			when ctx = ctx_a && ctx = ctx_b && list_set_eq h h_a && list_set_eq h h_b && eq_types l_type_domain r_type && is_type_small r_type 
				-> Some ((ctx, h, App (l_term, r_term), top_subst_type l_type_res (SubstData r_term)))
		| _ -> None	
	)
	| IVar v -> ( 
		match fetch_var ctx v with
		| Some (Data x) -> Some ((ctx, h, Var v, x))
		| _ -> None
	)
	| ISubtype (i, s) -> (
		match (typecheck_typing i ctx h, typecheck_subtyping s ctx h) with
		| (Some ((ctx1, h1, tm, t)), Some ((ctx2, h2, lt, rt))) 
			when ctx1 = ctx && ctx2 = ctx && list_set_eq h1 h && list_set_eq h2 h && eq_types t lt 
				-> Some ((ctx, h, tm, rt))
		| _ -> None
	)
	| IProofMem (i, t, p) -> (
		match (typecheck_typing i ctx h, t, typecheck_proof p ctx h) with
		| (Some (ctx_a, h_a, orig_tm, orig_typ), Refine (_, refined_typ, prp), Some (ctx_b, h_b, proofed_prp)) 
			when ctx_a = ctx && ctx_b = ctx && list_set_eq h_a h && list_set_eq h_b h && eq_types orig_typ refined_typ && eq_props proofed_prp (top_subst_prop prp (SubstData orig_tm)) 
				-> Some ((ctx, h, orig_tm, t))
		| _ -> None
	)
and typecheck_proof t ctx h =
	match t with
	| PTt -> Some ((ctx, h, Top))
	| PEqRefl (tm, t, x) -> (
		match typecheck_typing x ctx h with
		| Some ((ctx', h', tm', t')) when ctx' = ctx && list_set_eq h' h && eq_terms tm' tm && eq_types t' t -> Some ((ctx, h, Eq (tm, tm, t)))
		| _ -> None
	)
	| PExtractProof (tm, t, x) -> (
		match typecheck_typing x ctx h with
		| Some ((ctx', h', tm', Refine (v, t', prp))) 
			when ctx' = ctx && list_set_eq h' h && eq_terms tm' tm && eq_types (Refine (v, t', prp)) t 
				-> Some ((ctx, h, top_subst_prop prp (SubstData tm)))
		| _ -> None
	)
	| PAnd (l, r) -> (
		match (typecheck_proof l ctx h, typecheck_proof r ctx h) with
		| (Some (ctx_a, h_a, lp), Some (ctx_b, h_b, rp)) 
			when ctx_a = ctx && ctx_b = ctx && list_set_eq h_a h && list_set_eq h_b h
				-> Some (ctx, h, Conjunction (lp, rp))
		| _ -> None 
	)
	| POrLeft (p, right) -> (
		let p = typecheck_proof p ctx h in
		match p with
		| Some (ctx', h', left) when ctx' = ctx && list_set_eq h' h -> Some (ctx, h, Disjunction (left, right))
		| _ -> None
	)
	| POrRight (p, left) -> (
		let p = typecheck_proof p ctx h in
		match p with
		| Some (ctx', h', right) when ctx' = ctx && list_set_eq h' h -> Some (ctx, h, Disjunction (left, right))
		| _ -> None
	)
	| PImplies (hyp, conclusion) -> (
		let p = typecheck_proof conclusion ctx (hyp :: h) in
		match p with
		| Some (ctx', h', prp) when ctx' = ctx && list_set_eq h' (hyp :: h) -> Some (ctx, h, Implication (hyp, prp))
		| _ -> None
	)
	| PAssumption target -> (
		if List.exists (fun x -> eq_props x target) h then Some (ctx, h, target)
		else None
	)
	| PForall (v, typ, body) -> (
		let ctx_a = push_var v (Data typ) ctx in
		match (typecheck_proof body ctx_a h) with
		| Some (ctx_b, h', prp) when ctx_b = ctx_a && list_set_eq h' h -> Some (ctx, h, Forall (v, typ, prp))
		| _ -> None
	)
	| PExists (v, typ, prp, body, i) -> (
		let ctx_a = push_var v (Data typ) ctx in
		match (typecheck_proof body ctx_a h, typecheck_typing i ctx h) with
		| (Some (ctx_b, h_a, prp'), Some (ctx', h_b, tm, typ)) 
			when ctx' = ctx && ctx_b = ctx_a && list_set_eq h_a h && list_set_eq h_b h && prp' = top_subst_prop prp (SubstData tm)
				-> Some (ctx, h, Exists (v, typ, prp))
		| _ -> None
	)
	| PExistsProofProj p -> (
		match (typecheck_proof p ctx h) with
		| Some (ctx', h', Exists (_, typ, body))
			when ctx' = ctx && list_set_eq h' h
				-> failwith "not yet implemented"
		| _ -> None
	)
	| PForallElim (p, i) -> (
		match (typecheck_proof p ctx h, typecheck_typing i ctx h) with
		| (Some (ctx_a, h_a, Forall (_, expected_typ, body)), Some (ctx_b, h_b, tm, infered_typ))
			when ctx_a = ctx && ctx_b = ctx && list_set_eq h_a h && list_set_eq h_b h && eq_types expected_typ infered_typ
				-> Some (ctx, h, top_subst_prop body (SubstData tm))  
		| _ -> None
	)
	| PImpliesElim (l, r) -> (
		match (typecheck_proof l ctx h, typecheck_proof r ctx h) with
		| (Some (ctx_a, h_a, Implication (x, y)), Some (ctx_b, h_b, z))
			when ctx_a = ctx && ctx_b = ctx && list_set_eq h_a h && list_set_eq h_b h && eq_props z x 
				-> Some (ctx, h, y)
		| _ -> None
	)
	| PAndElim (x, y) -> (
		match (typecheck_proof x ctx h, typecheck_proof y ctx h) with
		| (Some (ctx_a, h_a, Conjunction (l, r)), Some (ctx_b, h_b, Implication (l', Implication (r', z))))
			when ctx_a = ctx && ctx_b = ctx && list_set_eq h_a h && list_set_eq h_b h && eq_props l' l && eq_props r' r
				-> Some (ctx, h, z)                                                                                                                                 
		| _ -> None
	)
	| POrElim (l, r, z) -> (
		match typecheck_proof z ctx h with
		| Some (ctx', h', Disjunction (l', r')) when ctx' = ctx && list_set_eq h' h -> (
			match (typecheck_proof l ctx h, typecheck_proof r ctx h) with
			| (Some (ctx_a, h_a, Implication (l'', x)), Some (ctx_b, h_b, Implication (r'', y)))
				when ctx_a = ctx && ctx_b = ctx && list_set_eq h_a h && list_set_eq h_b h && eq_props x y && eq_props l' l'' && eq_props r' r''
					-> Some (ctx, h, x)
			| _ -> None
		)
		| _ -> None
	)
	| PEqSymm x -> (
		match typecheck_proof x ctx h with
		| Some (ctx', h', Eq (l, r, typ)) when ctx' = ctx && list_set_eq h' h -> Some (ctx, h, Eq (r, l, typ))
		| _ -> None
	)
	| PEqTrans (x, y) -> (
		match (typecheck_proof x ctx h, typecheck_proof y ctx h) with
		| (Some (ctx_a, h_a, Eq (l, t_a, typ_a)), Some (ctx_b, h_b, Eq (t_b, r, typ_b))) 
			when ctx_a = ctx && ctx_b = ctx && list_set_eq h_a h && list_set_eq h_b h && eq_terms t_a t_b && eq_types typ_a typ_b 
				-> Some (ctx, h, Eq (l, r, typ_a))
		| _ -> None
	)
	| PEqRedL x -> (
		match typecheck_proof x ctx h with
		| Some (ctx', h', Eq (l, r, typ)) 
			when ctx' = ctx && list_set_eq h' h 
				-> Some (ctx, h, Eq (reduction_step l, r, typ))	 
		| _ -> None
	)
	| PEqRedR x -> (
		match typecheck_proof x ctx h with
		| Some (ctx', h', Eq (l, r, typ)) 
			when ctx' = ctx && list_set_eq h' h 
				-> Some (ctx, h, Eq (l, reduction_step r, typ))	 
		| _ -> None
	)
	| PEqRedRevL (x, t) -> (
		match typecheck_proof x ctx h with
		| Some (ctx', h', Eq (l, r, typ)) 
			when ctx' = ctx && list_set_eq h' h && reduction_step t = l
				-> Some (ctx, h, Eq (t, r, typ))	 
		| _ -> None
	)
	| PEqRedRevR (x, t) -> (
		match typecheck_proof x ctx h with
		| Some (ctx', h', Eq (l, r, typ)) 
			when ctx' = ctx && list_set_eq h' h && reduction_step t = r
				-> Some (ctx, h, Eq (l, t, typ))	 
		| _ -> None
	)
and typecheck_subtyping t ctx h =
	match t with
	| SRefl typ -> Some ((ctx, h, typ, typ))
	| STrans (l, r) -> (
		match (typecheck_subtyping l ctx h, typecheck_subtyping r ctx h) with
		| (Some (ctx1, h1, l_typ1, r_typ1), Some (ctx2, h2, l_typ2, r_typ2)) 
			when ctx = ctx1 && ctx = ctx && list_set_eq h h1 && list_set_eq h h2 && r_typ1 = l_typ2
				-> Some ((ctx, h, l_typ1, r_typ2))
		| _ -> None
	)
	| SUnrefine (Refine (v, typ, prp)) -> Some ((ctx, h, Refine (v, typ, prp), typ))
	| SUnrefine _ -> None
;;  

let read_term ctx =
	let ctx' = ReprConversion.PreIrToIr.index_context_from_ir_typing_context ctx in
	read_line () |> Lexing.from_string |> LambdaAst.lambda_term LambdaLex.lex |> (fun x -> ReprConversion.PreIrToIr.convert_term_ctx x ctx')
;;
let read_type ctx = 
    let ctx' = ReprConversion.PreIrToIr.index_context_from_ir_typing_context ctx in
	read_line () |> Lexing.from_string |> LambdaAst.lambda_type LambdaLex.lex |> (fun x -> ReprConversion.PreIrToIr.convert_type_ctx x ctx')
;;
let read_prop ctx = 
    let ctx' = ReprConversion.PreIrToIr.index_context_from_ir_typing_context ctx in
	read_line () |> Lexing.from_string |> LambdaAst.lambda_prop LambdaLex.lex |> (fun x -> ReprConversion.PreIrToIr.convert_prop_ctx x ctx')
;;

let read_typing_command ctx h =
	let input = read_line () in
	match input with
	| "subtype" -> ApplySubtype
	| "prove_membership" -> ApplyMemProof
	| _ -> failwith "Unrecognized command"
;;
let read_proof_mode_command ctx h = 
	let input = read_line () in
	match input with
	| "tt" -> ApplyTt
	| "eq_refl" -> ApplyEqRefl
	| "and" -> ApplyAnd
	| "or_left" -> ApplyOrL
	| "or_right" -> ApplyOrR
	| "implication" -> ApplyImplication
	| "assumption" -> ApplyAssumption
	| "forall" -> ApplyForallProof
	| "exists" -> ApplyExistsProof
	| "elim_implication" -> (
		let () = Printf.printf "Enter the right side of implication to eliminate\n>>" in
		ApplyImplicationElim (read_prop ctx)
	)
	| "elim_and" -> (
		let l = (Printf.printf "Enter the left side of `and`\n>>"; read_prop ctx)
		and r = (Printf.printf "Enter the right side of `and`\n>>"; read_prop ctx) in
		ApplyAndElim (l, r)
	)
	| "elim_or" -> (
		let l = (Printf.printf "Enter the left side of `or`\n>>"; read_prop ctx)
		and r = (Printf.printf "Enter the right side of `or`\n>>"; read_prop ctx) in
		ApplyOrElim (l, r)
	)
	| "red_rev_l" -> ApplyEqRedRevL
	| "red_rev_r" -> ApplyEqRedRevR
	| "red_l" -> (
		let x = (Printf.printf "Enter the term\n>>"; read_term ctx) in
		ApplyEqRedL x
	) 
	| "red_r" -> (
		let x = (Printf.printf "Enter the term\n>>"; read_term ctx) in
		ApplyEqRedR x
	)
	| "eq_symm" -> ApplyEqSymm
	| "eq_trans" -> (
		let x = (Printf.printf "Enter the term\n>>"; read_term ctx) in
		ApplyEqTrans x
	)
	| _ -> failwith "Unrecognized command"
;;
let read_subtyping_mode_command ctx h =
	let input = read_line () in
	match input with
	| "sub_refl" -> ApplySubRefl
	| "sub_trans" -> (
		let () = Printf.printf "Enter the type you are going to use in for transitivity (S <: ? <: T)\n>>" in
		ApplySubTrans (read_type ctx)
	)
	| _ -> failwith "Unrecognized command"
;;                                                                                                                            
                                    
(*TODO lookup for proofs in the lbt_list*)
(*TODO add a `cut` tactic for typing*)
let rec prove_type_memembership ctx h term current_typ expected_typ ri lbt_list =
    (
		let ctx' = ReprConversion.IrToPreIr.naming_context_from_ir_typing_context ctx in
		let tm_str = ReprConversion.IrToPreIr.convert_term_ctx term ctx' |> PreIr.string_of_term in
		Printf.printf "Goal:\nIf following typing holds\n%s : %s\nThen the following typing is legal\n%s : %s\n"  tm_str (ReprConversion.IrToPreIr.convert_type_ctx current_typ ctx' |> PreIr.string_of_type) tm_str (ReprConversion.IrToPreIr.convert_type_ctx expected_typ ctx' |> PreIr.string_of_type)
	);
	let cmd = (Printf.printf "Enter typing command\n>"; read_typing_command ctx h) in
	match (cmd, expected_typ) with
	| (ApplySubtype, _) -> (
		let s = interactive_subtyping ctx h (current_typ, expected_typ) lbt_list in
		match (typecheck_subtyping s ctx h) with
		| Some (ctx', h', current_typ', expected_typ') when ctx = ctx' && list_set_eq h h' && eq_types current_typ current_typ' && eq_types expected_typ expected_typ' -> ISubtype (ri, s)
		| _ -> failwith "failed to solve the problem with subtyping"
	)
	| (ApplyMemProof, Refine (_, refined_typ, prp)) when eq_types current_typ refined_typ -> (
		let target = top_subst_prop prp (SubstData term) in
		let p = interactive_proving ctx h target lbt_list in
		match (typecheck_proof p ctx h) with
		| Some (ctx', h', prp') when ctx = ctx' && list_set_eq h h' && eq_props target prp' -> IProofMem (ri, expected_typ, p) 
		| _ -> failwith "bad proof"
	)
	| _ -> failwith "the current command is not applicable in this situation"
and consider_app_problem ctx h li ri ltm lt rtm rt lbt_list =
	match lt with
	| Refine (_, typ, prp) -> consider_app_problem ctx h (ISubtype (li, SUnrefine lt)) ri ltm typ rtm rt lbt_list
	| Map (_, x, y) -> (
		if eq_types x rt then IApp (li, ri)
		else (
			let p = prove_type_memembership ctx h rtm rt x ri (li :: ri :: lbt_list) in (*TODO narrowing*)
			IApp (li, p)
		)
	)
	| _ -> failwith "unsolvable problem"
and interactive_typing ctx h t lbt_list =
	match t with
	| Var v ->  IVar v
	| Nil -> INil
	| NatO -> INatO
	| NatSucc -> INatSucc
	| App (l, r) -> (
		let (li, ri) = (interactive_typing ctx h l lbt_list, interactive_typing ctx h r lbt_list) in
		match (typecheck_typing li ctx h, typecheck_typing ri ctx h) with
		| (Some ((ctx1, h1, ltm, lt)), Some ((ctx2, h2, rtm, rt))) when ctx1 = ctx && ctx2 = ctx && list_set_eq h1 h && list_set_eq h2 h -> consider_app_problem ctx h li ri ltm lt rtm rt lbt_list
		| _ -> failwith "failed to type"
	)
	| Abs (v, arg_t, body) -> (
		let ctx' = ctx |> push_var v (Data arg_t) in
		let i = interactive_typing ctx' h body lbt_list in
		let c = typecheck_typing i ctx' h in
		match c with
		| Some ((ctx, h', tm, typ)) when ctx = ctx' && list_set_eq h h' && eq_terms tm body -> IAbs (v, arg_t, i)
		| _ -> failwith "failed to type"
	)
	| _ -> failwith "not supported"
and interactive_proving ctx h t lbt_list = 
	(
		let ctx' = ReprConversion.IrToPreIr.naming_context_from_ir_typing_context ctx in
		ReprConversion.IrToPreIr.convert_prop_ctx t ctx' |> PreIr.string_of_prop |> Printf.printf "Goal: %s\n"
	);
	let cmd = (Printf.printf "Enter proof command\n>"; read_proof_mode_command ctx h) in
	match (t, cmd) with
	| (_, ApplyAssumption) -> (
		if List.exists (fun x -> eq_props x t) h then PAssumption t
		else failwith "This is not an assumption"
	)
	| (Top, ApplyTt) -> PTt
	| (Eq (l_tm_target, r_tm_target, target_typ), ApplyEqRefl) -> (
		if eq_terms l_tm_target r_tm_target then (
			let i = interactive_typing ctx h l_tm_target lbt_list in
			match (typecheck_typing i ctx h) with
			| Some ((ctx', h', tm, typ)) when ctx = ctx' && list_set_eq h h' && eq_terms tm l_tm_target && eq_types typ target_typ -> PEqRefl (tm, typ, i)
			| _ -> failwith "failed to type the term"
		) else failwith "Can't proof this equality with reflexivity, because left and right sides are not the same" 
	)
	| (Conjunction (l, r), ApplyAnd) -> (
		let (lp, rp) = (interactive_proving ctx h l lbt_list, interactive_proving ctx h r lbt_list) in
		match (typecheck_proof lp ctx h, typecheck_proof rp ctx h) with
		| (Some (ctx_a, h_a, l'), Some (ctx_b, h_b, r')) 
			when ctx_a = ctx && ctx_b = ctx && list_set_eq h_a h && list_set_eq h_b h && eq_props l' l && eq_props r' r 
				-> PAnd (lp, rp) 
		| _ -> failwith "bad left or right proof"
	)
	| (Disjunction (l, r), ApplyOrL) -> (
		let lp = interactive_proving ctx h l lbt_list in
		match typecheck_proof lp ctx h with
		| Some (ctx', h', l') 
			when ctx = ctx' && list_set_eq h h' && eq_props l l'
				 -> POrLeft (lp, r) 
		| _ -> failwith "bad left proof"
	)
	| (Disjunction (l, r), ApplyOrR) -> (
		let rp = interactive_proving ctx h l lbt_list in
		match typecheck_proof rp ctx h with
		| Some (ctx', h', r') 
			when ctx = ctx' && list_set_eq h h' && eq_props r r'
				 -> POrRight (rp, l) 
		| _ -> failwith "bad right proof"
	)
	| (Implication (l, r), ApplyImplication) -> (
		let p = interactive_proving ctx (l :: h) r lbt_list in
		match typecheck_proof p ctx (l :: h) with
		| Some (ctx', h', r')
			when ctx = ctx' && list_set_eq (l :: h) h' && eq_props r r' 
				-> PImplies (l, p)
		| _ -> failwith "bad conclusion proof"
	)	
	| (Exists (v, typ, prp), ApplyExistsProof) -> (
		let term = (Printf.printf "Enter term\n>>"; read_term ctx) in
		let i = interactive_typing ctx h term lbt_list in
		let target = top_subst_prop prp (SubstData term) in
		let p = interactive_proving ctx h target lbt_list in
		match (typecheck_proof p ctx h, typecheck_typing i ctx h) with
		| (Some (ctx_a, h_a, target'), Some (ctx_b, h_b, tm, typ'))
			when ctx_a = ctx && ctx_b = ctx && list_set_eq h_a h && list_set_eq h_b h && eq_props target target' && eq_types typ typ'
				-> PExists (v, typ, prp, p, i)
		| _ -> failwith "failed to prove existensial statement"	
	)
	| (Forall (v, typ, prp), ApplyForallProof) -> (
		let ctx' = push_var v (Data typ) ctx in
		let p = interactive_proving ctx' h prp lbt_list in
		match typecheck_proof p ctx' h with
		| Some (ctx'', h', prp')
			when ctx'' = ctx' && list_set_eq h' h && eq_props prp' prp
				-> PForall (v, typ, p)
		| _ -> failwith "bad body proof"
	)
	| (_, ApplyAndElim (l, r)) -> (
		let p = interactive_proving ctx h (Conjunction (l, r)) lbt_list 
        and p' = interactive_proving ctx h (Implication (l, Implication (r, t))) lbt_list in
		match (typecheck_proof p ctx h, typecheck_proof p' ctx h) with
		| (Some (ctx_a, h_a, Conjunction (l_a, r_a)), Some (ctx_b, h_b, Implication (l_b, Implication (r_b, t'))))
			when ctx_a = ctx && ctx_b = ctx && list_set_eq h_a h && list_set_eq h_b h && eq_props l_a l && eq_props r_a r && eq_props l_b l && eq_props r_b r && eq_props t' t
				-> PAndElim (p, p')
		| _ -> failwith "bad and proof"
	)
	| (_, ApplyOrElim (l, r)) -> (
		let p = interactive_proving ctx h (Disjunction (l, r)) lbt_list 
        and lp = interactive_proving ctx h (Implication (l, t)) lbt_list
        and rp = interactive_proving ctx h (Implication (r, t)) lbt_list in
		match (typecheck_proof p ctx h, typecheck_proof lp ctx h, typecheck_proof rp ctx h) with
		| (Some (ctx_a, h_a, Conjunction (l_a, r_a)), Some (ctx_b, h_b, Implication (l_b, t_b)), Some (ctx_c, h_c, Implication (r_c, t_c)))
			when ctx_a = ctx && ctx_b = ctx && ctx_c = ctx && list_set_eq h_a h && list_set_eq h_b h && list_set_eq h_c h && eq_props l_a l && eq_props r_a r && eq_props l_b l && eq_props r_c r && eq_props t_b t && eq_props t_c t
				-> POrElim (lp, rp, p)
		| _ -> failwith "bad and proof"
	)
	| (Eq (l, r, typ), ApplyEqRedL x) -> (
		let p = interactive_proving ctx h (Eq (x, r, typ)) lbt_list in
		match typecheck_proof p ctx h with
		| Some (ctx', h', Eq (x', r', typ'))
			when ctx' = ctx && list_set_eq h' h && eq_terms x' x && eq_terms r' r && eq_types typ' typ
				-> PEqRedL p 
		| _ -> failwith "bad eq proof" 
	)
	| (Eq (l, r, typ), ApplyEqRedR x) -> (
		let p = interactive_proving ctx h (Eq (l, x, typ)) lbt_list in
		match typecheck_proof p ctx h with
		| Some (ctx', h', Eq (l', x', typ'))
			when ctx' = ctx && list_set_eq h' h && eq_terms x' x && eq_terms l' l && eq_types typ' typ
				-> PEqRedL p 
		| _ -> failwith "bad eq proof" 
	)
	| (Eq (l, r, typ), ApplyEqRedRevL) -> (
		let l_red = reduction_step l in
		let p = interactive_proving ctx h (Eq (l_red, r, typ)) lbt_list in
		match typecheck_proof p ctx h with
		| Some (ctx', h', Eq (l_red', r', typ'))
			when ctx' = ctx && list_set_eq h' h && eq_terms l_red' l_red && eq_terms r' r && eq_types typ' typ
				-> PEqRedRevL (p, l)
		| _ -> failwith "bad eq proof"
	)
	| (Eq (l, r, typ), ApplyEqRedRevR) -> (
		let r_red = reduction_step r in
		let p = interactive_proving ctx h (Eq (l, r_red, typ)) lbt_list in
		match typecheck_proof p ctx h with
		| Some (ctx', h', Eq (l', r_red', typ'))
			when ctx' = ctx && list_set_eq h' h && eq_terms r_red' r_red && eq_terms l' l && eq_types typ' typ
				-> PEqRedRevR (p, r)
		| _ -> failwith "bad eq proof"
	)
	| (Eq (l, r, typ), ApplyEqSymm) -> (
		let p = interactive_proving ctx h (Eq (r, l, typ)) lbt_list in
		match typecheck_proof p ctx h with
		| Some (ctx', h', Eq (r', l', typ'))
			when ctx' = ctx && list_set_eq h' h && eq_terms r' r && eq_terms l' l && eq_types typ' typ
				-> PEqSymm p
		| _ -> failwith "bad eq proof"
	)
	| (Eq (l, r, typ), ApplyEqTrans x) -> (
		let lp = interactive_proving ctx h (Eq (l, x, typ)) lbt_list
		and rp = interactive_proving ctx h (Eq (x, r, typ)) lbt_list in
		match (typecheck_proof lp ctx h, typecheck_proof rp ctx h) with
		| (Some (ctx_a, h_a, Eq (l_a, x_a, typ_a)), Some (ctx_b, h_b, Eq (x_b, r_b, typ_b))) 
			when ctx_a = ctx && ctx_b = ctx && list_set_eq h_a h && list_set_eq h_b h && eq_terms l_a l && eq_terms x_a x && eq_terms r_b r && eq_terms x_b x && eq_types typ_a typ && eq_types typ_b typ 
				-> PEqTrans (lp, rp)
		| _ -> failwith "bad eq proof"
	)
	| _ -> failwith "Unimplemented"
and interactive_subtyping ctx h (l, r) lbt_list =
	(
		let ctx' = ReprConversion.IrToPreIr.naming_context_from_ir_typing_context ctx in
		Printf.printf "Goal: %s <: %s\n" (l |> (fun x -> ReprConversion.IrToPreIr.convert_type_ctx x ctx') |> PreIr.string_of_type) (r |> (fun x -> ReprConversion.IrToPreIr.convert_type_ctx x ctx') |> PreIr.string_of_type)
	);
	let cmd = (Printf.printf "Enter subtyping command\n>"; read_subtyping_mode_command ctx h) in
	match ((l, r), cmd) with
	| (_, ApplySubRefl) -> if eq_types l r then SRefl l else failwith "Can't proof this subtyping with reflexivity, because left and right sides are not the same"
	| (_, ApplySubTrans t) -> (
		let (li, ri) = (interactive_subtyping ctx h (l, t) lbt_list, interactive_subtyping ctx h (t, r) lbt_list) in
		match (typecheck_subtyping li ctx h, typecheck_subtyping ri ctx h) with
		| (Some (ctx1, h1, lt1, rt1), Some (ctx2, h2, lt2, rt2)) when ctx = ctx1 && ctx = ctx2 && list_set_eq h h1 && list_set_eq h h2 -> STrans (li, ri)
		| _ -> failwith "failed to check subtyping proofs"
	)
;;

let verify t =
	let ctx' = create_empty_context ()
	and h' = [] in
	let i = interactive_typing ctx' h' t [] |> fun x -> typecheck_typing x ctx' h' in
	match i with
	| Some ((ctx, h, tm, typ)) -> 
			if ctx = ctx' && list_set_eq h h' && eq_terms tm t then Printf.printf "Ok\n" 
		else (
			Printf.printf "Context, term or hypothesis list mismatch\nCtx = [%s]\nExpectedCtx = [%s]\nTerm = %s\nExpectedTerm = %s\nHypothesisList = [%s]\n" (ReprConversion.CtxUtil.string_of_context ctx) (ReprConversion.CtxUtil.string_of_context ctx') (t |> ReprConversion.IrToPreIr.convert_term |> PreIr.string_of_term) (tm |> ReprConversion.IrToPreIr.convert_term |> PreIr.string_of_term) (h |> List.map (fun x -> x |> ReprConversion.IrToPreIr.convert_prop |> PreIr.string_of_prop) |> String.concat ",");
		    (*
				if `old_term_equality` is false and `term_equality` is true, that should be okay, but if the
				situation is vice versa, then there must be a bad impl hidden somewhere
			*)
			Printf.printf "context_equality: %s\nhypothesis_set_equality: %s\nterm_equality: %s\nold_term_equality: %s\n" (ctx = ctx' |> string_of_bool) (list_set_eq h h' |> string_of_bool) (eq_terms tm t |> string_of_bool) (tm = t |> string_of_bool)
		)
	| None -> Printf.printf "Got NONE\n"
;;