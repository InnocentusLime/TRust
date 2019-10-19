(*
	VARIABLE NAMING HANDLING
	==============================================================
	Imagine us encountering the following problem:
		when we are trying to give the names back to the variables
		we notice that two variabled have the same name in the
		context `ctx`
	This problem doesn't look so concerning unless we encounter,
	for example, the following term:
		i j
	where `i` and `j` are different De-Brujin indices, but in
	the same time `ctx` associates two same names with them. If
	`TRust` encounters that problem, he would calculate the fresh 
	name for conflicted variable (`j` in that case), traverse back 
	to the binder of that variable change the string and try to
	name all the variables again 

	VARIABLE UNNAMING HANDLING
	==============================================================
	We need to unname the term, but encountered the following
	problem:
		When unnaming the variable we notice that two indices are
		associated with one name
	In this case `TRust` favours choosing the first matching
	variable in the context. Basically, `TRust` uses variable
	shadowing.
*)

let freshiny_name_impl x f =          
	let build_name_suffix n = if n = 0 then "" else string_of_int n in
	let rec freshiny_name_impl' x f n =
		let s = (x ^ (build_name_suffix n)) in
		if f s then freshiny_name_impl' x f (n + 1)
		else s
	in
	freshiny_name_impl' x f 0		

(*
module CtxUtil = struct
	open Ir;;
	let freshiny_context ctx = 
		let name_mem_mem offset ctx v = Array.fold_left (fun (pos, acc) x -> (pos + 1, acc || ((snd x) = v && offset <= pos))) (0, false) ctx.mem |> snd in 
		{ mem = Array.mapi (fun i (v, str) -> (v, freshiny_name_impl str (name_mem_mem i ctx))) ctx.mem }
	;;
	let extract_naming_from_typing_context ctx = Array.map (fun x -> snd x) ctx.mem;;
	let name_context ctx = ctx |> freshiny_context |> extract_naming_from_typing_context;;

	let string_of_context ctx = ctx |> name_context |> Array.to_list |> String.concat ", ";;
end
*)                                                                                                      

module IrToPreIr = struct
	open Ir
	open Common
	open Aliases

	type usage_table = bool str_hashtbl

	type naming_context = { typing_ctx : context; usage : usage_table }

	let name_of { typing_ctx; _ } v = !(Array.get typing_ctx.mem v |> snd)

	let pick_fresh_name ctx v = freshiny_name_impl (name_of ctx v) (fun attempt -> ArrayExt.exists (fun (_, name) -> !name = attempt) ctx.typing_ctx.mem)

	let is_name_used used x = if Hashtbl.mem used x then Hashtbl.find used x else false

	let conflicts ctx v = ArrayExt.existsi (fun i (_, name) -> i <> v && !name = name_of ctx v && is_name_used ctx.usage !name) ctx.typing_ctx.mem

	let rewrite_name ctx v str = ((Array.get ctx.typing_ctx.mem v |> snd) := str)

	let push ctx v t = { typing_ctx = push_var v t ctx.typing_ctx; usage = ctx.usage }

	let unnaming_context_from_typing_context ctx = { typing_ctx = ctx; usage = Hashtbl.create 0 } 

	(*
		DESCRIPTION
		==================================================
		Algorithm responsible for `Ir -> PreIr`

		HOW DOES IT WORK?
		==================================================
		This algorithm tries to rename variables as
		sparingly as possible. Shortly speaking, it 
		works the following way:
			* when the algorithm encounters an abstraction
			it adds the variable to the context of names
			* if it encounters a variable then:
				- if the variable conflicts with the
				current situation, the algorithm picks
				a fresh name and renames it.
				- if it is doesn't, the algorithm proceeds
		
		SIDE EFFECTS
		==========================================================
		the supplied context may get overwritten to contain no
		conflicts
	*)
	let rec convert_term_ctx t ctx =
		match t with
		| BoolTrue -> PreIr.BoolTrue
		| BoolFalse -> PreIr.BoolFalse
		| Nil -> PreIr.Nil
		| NatO -> PreIr.NatO
		| NatSucc -> PreIr.NatSucc
		| Var v -> (
			if conflicts ctx v then rewrite_name ctx v (pick_fresh_name ctx v); 
			Hashtbl.add ctx.usage (name_of ctx v) true; 
			PreIr.Var (name_of ctx v)
		)
		| Bool -> PreIr.Bool
		| Nat -> PreIr.Nat
		| Unit -> PreIr.Unit
		| Forall (v, arg_typ, body) -> 
			let arg_typ' = convert_term_ctx arg_typ ctx in
			let body' = convert_term_ctx body (push ctx v arg_typ) in
			(Hashtbl.remove ctx.usage !v; PreIr.Forall (!v, arg_typ', body'))
		| Refine (x, y) -> PreIr.Refine (convert_term_ctx x ctx, convert_term_ctx y ctx)
		| Abs (v, arg_typ, body) ->
			let arg_typ' = convert_term_ctx arg_typ ctx in
			let body' = convert_term_ctx body (push ctx v arg_typ) in
			(Hashtbl.remove ctx.usage !v; PreIr.Abs (!v, arg_typ', body'))
		| App (l, r) -> 
			let l' = convert_term_ctx l ctx in
			let r' = convert_term_ctx r ctx in
			PreIr.App (l', r')
		| NatRec (x1, x2, x3, x4) -> 
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			let x4' = convert_term_ctx x4 ctx in
			PreIr.NatRec (x1', x2', x3', x4')			
		| BoolRec (x1, x2, x3, x4) -> 
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			let x4' = convert_term_ctx x4 ctx in
			PreIr.BoolRec (x1', x2', x3', x4')			
		| Type x -> PreIr.Type x
		| Small -> PreIr.Small
		| Prop -> PreIr.Prop
		| Convert (x1, x2) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			PreIr.Convert (x1', x2')
		| Extract (x1, x2, x3, x4, x5) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in 
			let x3' = convert_term_ctx x3 ctx in 
			let x4' = convert_term_ctx x4 ctx in 
			let x5' = convert_term_ctx x5 ctx in  
			PreIr.Extract (x1', x2', x3', x4', x5')
		| Subtyping (x1, x2) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			PreIr.Subtyping (x1', x2')
		| Sumbool (x1, x2) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			PreIr.Sumbool (x1', x2')
		| SBLeft (x1, x2) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			PreIr.SBLeft (x1', x2')
		| SBRight (x1, x2) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			PreIr.SBRight (x1', x2')
		| SumboolRec (x1, x2, x3, x4, x5, x6) -> 
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			let x4' = convert_term_ctx x4 ctx in
			let x5' = convert_term_ctx x5 ctx in
			let x6' = convert_term_ctx x6 ctx in
			PreIr.SumboolRec (x1', x2', x3', x4', x5', x6')			
		| Membership (x1, x2, x3, x4) -> 
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			let x4' = convert_term_ctx x4 ctx in
			PreIr.Membership (x1', x2', x3', x4')			
		| SubTrans (x1, x2, x3, x4, x5) -> 
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			let x4' = convert_term_ctx x4 ctx in
			let x5' = convert_term_ctx x5 ctx in
			PreIr.SubTrans (x1', x2', x3', x4', x5')
		| SubSub (x1, x2, x3, x4) -> 
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			let x4' = convert_term_ctx x4 ctx in
			PreIr.SubSub (x1', x2', x3', x4')			
		| SubRefl x -> PreIr.SubRefl (convert_term_ctx x ctx)
		| SubProd (x1, x2, x3, x4, x5, x6) -> 
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in 
			let x3' = convert_term_ctx x3 ctx in 
			let x4' = convert_term_ctx x4 ctx in 
			let x5' = convert_term_ctx x5 ctx in
			let x6' = convert_term_ctx x6 ctx in  
			PreIr.SubProd (x1', x2', x3', x4', x5', x6')
		| SubUnrefine (x1, x2) -> PreIr.SubUnrefine (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx)
		| SubGen (x1, x2, x3) -> 
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			PreIr.SubGen (x1', x2', x3')
		| Conjunction (x1, x2) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			PreIr.Conjunction (x1', x2')
		| Disjunction (x1, x2) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			PreIr.Disjunction (x1', x2')
		| OrIntroL (x1, x2, x3) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			PreIr.OrIntroL (x1', x2', x3')
		| OrIntroR (x1, x2, x3) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			PreIr.OrIntroR (x1', x2', x3')
		| AndIntro (x1, x2, x3, x4) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			let x4' = convert_term_ctx x4 ctx in
			PreIr.AndIntro (x1', x2', x3', x4')
		| Eq (x1, x2, x3) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			PreIr.Eq (x1', x2', x3')
		| EqRefl (x1, x2) -> 
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			PreIr.EqRefl (x1', x2')
		| Exists (v, x1, x2) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 (push ctx v x1) in
			PreIr.Exists (!v, x1', x2')
		| Exist (x1, x2, x3, x4) ->
			let x1' = convert_term_ctx x1 ctx in
			let x2' = convert_term_ctx x2 ctx in
			let x3' = convert_term_ctx x3 ctx in
			let x4' = convert_term_ctx x4 ctx in
			PreIr.Exist (x1', x2', x3', x4')

	let convert_term t = convert_term_ctx t { typing_ctx = create_empty_context (); usage = Hashtbl.create 0 }
end

module PreIrToStr = struct
	open PreIr

let rec convert_term t =
		match t with
		| NatO -> "O"
		| NatSucc -> "S"
		| BoolTrue -> "true"
		| BoolFalse -> "false"
		| Nil -> "nil"
		| Var x -> x
		| Bool -> "bool"
		| Nat -> "nat"
		| Unit -> "unit"
		| Forall (v, typ, body) -> if v = "_" then "(" ^ (convert_term typ) ^ " -> " ^ (convert_term body) ^ ")" else "(forall " ^ v ^ ":" ^ (convert_term typ) ^ "." ^ (convert_term body) ^ ")"
		| Refine (l, r) -> "{" ^ (convert_term l) ^ " | " ^ (convert_term r) ^ "}"
		| Abs (v, typ, body) -> "(/" ^ v ^ ":" ^ (convert_term typ) ^ "." ^ (convert_term body) ^ ")"
		| App (l, r) -> "(" ^ (convert_term l) ^ " " ^ (convert_term r) ^ ")"
		| NatRec (x1, x2, x3, x4) -> "nat_rec(" ^ (convert_term x1) ^ "; " ^ (convert_term x2) ^ "; " ^ (convert_term x3) ^ "; " ^ (convert_term x4) ^ ")"
		| BoolRec (x1, x2, x3, x4) -> "bool_rec(" ^ (convert_term x1) ^ "; " ^ (convert_term x2) ^ "; " ^ (convert_term x3) ^ "; " ^ (convert_term x4) ^ ")"
		| Type x -> "type[" ^ string_of_int x ^ "]"
		| Small -> "small"
		| Prop -> "prop"
		| Convert (x1, x2) -> "convert(" ^ (convert_term x1) ^ "; " ^ (convert_term x2) ^ ")"
		| Membership (x1, x2, x3, x4) -> "membership(" ^ (convert_term x1) ^ "; " ^ (convert_term x2) ^ "; " ^ (convert_term x3) ^ "; " ^ (convert_term x4) ^ ")"
		| SubTrans (x1, x2, x3, x4, x5) -> "trans(" ^ convert_term x1 ^ "; " ^ convert_term x2 ^ "; " ^ convert_term x3 ^ "; " ^ convert_term x4 ^ "; " ^ convert_term x5 ^ ")"
		| SubSub (x1, x2, x3, x4) -> "subset(" ^ (convert_term x1) ^ "; " ^ (convert_term x2) ^ "; " ^ (convert_term x3) ^ "; " ^ (convert_term x4) ^ ")"
		| SubRefl x -> "refl(" ^ (convert_term x) ^ ")"
		| SubProd (x1, x2, x3, x4, x5, x6) -> "prod(" ^ (convert_term x1) ^ "; " ^ (convert_term x2) ^ "; " ^ (convert_term x3) ^ "; " ^ (convert_term x4) ^ "; " ^ (convert_term x5) ^ "; " ^ (convert_term x6) ^ ")"
		| SubUnrefine (x1, x2) -> "unrefine(" ^ convert_term x1 ^ "; " ^ convert_term x2 ^ ")"
		| SubGen (x1, x2, x3) -> "gen(" ^ (convert_term x1) ^ "; " ^ (convert_term x2) ^ "; " ^ (convert_term x3) ^ ")"
		| Extract (x1, x2, x3, x4, x5) -> "extract(" ^ (convert_term x1) ^ "; " ^ (convert_term x2) ^ "; " ^ (convert_term x3) ^ "; " ^ (convert_term x4) ^ "; " ^ (convert_term x5) ^ ")"
		| Sumbool (x1, x2) -> "[" ^ (convert_term x1) ^ "] & [" ^ (convert_term x2) ^ "]"
		| SBLeft (x1, x2) -> "sboolL(" ^ (convert_term x1) ^ "; " ^ (convert_term x2) ^ ")"
		| SBRight (x1, x2) -> "sboolR(" ^ (convert_term x1) ^ "; " ^ (convert_term x2) ^ ")"
		| SumboolRec (x1, x2, x3, x4, x5, x6) -> "sboolRec(" ^ (convert_term x1) ^ "; " ^ (convert_term x2) ^ "; " ^ (convert_term x3) ^ "; " ^ (convert_term x4) ^ "; " ^ convert_term x5 ^ "; " ^ convert_term x6 ^ ")"
		| Subtyping (x1, x2) -> (convert_term x1) ^ " <: " ^ (convert_term x2)
		| Conjunction (x1, x2) -> "(" ^ convert_term x1 ^ " /\\ " ^ convert_term x2 ^ ")"
		| Disjunction (x1, x2) -> "(" ^ convert_term x1 ^ " \\/ " ^ convert_term x2 ^ ")"  
		| OrIntroL (x1, x2, x3) -> "or_introl(" ^ convert_term x1 ^ "; " ^ convert_term x2 ^ "; " ^ convert_term x3 ^ ")" 
		| OrIntroR (x1, x2, x3) -> "or_intror(" ^ convert_term x1 ^ "; " ^ convert_term x2 ^ "; " ^ convert_term x3 ^ ")" 
		| AndIntro (x1, x2, x3, x4) -> "and_intro(" ^ convert_term x1 ^ "; " ^ convert_term x2 ^ "; " ^ convert_term x3 ^ "; " ^ convert_term x4 ^ ")"
		| Eq (x1, x2, x3) -> "(" ^ convert_term x1 ^ " == " ^ convert_term x2 ^ " :> " ^ convert_term x3 ^ ")"
		| EqRefl (x1, x2) -> "eq_refl(" ^ convert_term x1 ^ "; " ^ convert_term x2 ^ ")"
		| Exists (v, x1, x2) -> "(exists " ^ v ^ " : " ^ convert_term x1 ^ "." ^ convert_term x2 ^ ")"
		| Exist (x1, x2, x3, x4) -> "exist(" ^ convert_term x1 ^ "; " ^ convert_term x2 ^ "; " ^ convert_term x3 ^ "; " ^ convert_term x4 ^ ")" 
end


module PreIrToIr = struct	
	open PreIr
	open Common

	type unnaming_mem = int Aliases.StrMap.t
	let empty_ctx = Aliases.StrMap.empty
	let mem_mem = Aliases.StrMap.mem
	let mem_add = Aliases.StrMap.add
	let mem_find = Aliases.StrMap.find
	let mem_map = Aliases.StrMap.map

	type unnaming_context = { mem : unnaming_mem };;

	let try_bind ctx x t = if mem_mem x ctx then ctx else mem_add x t ctx
		

	let unnaming_context_from_ir_context ctx =
		{ mem = ArrayExt.fold_left_i (fun i acc (_, x) -> try_bind acc x i) empty_ctx ctx }
	;;

	let create_empty_context () = { mem = empty_ctx };;
	let delta_indices ctx delta = mem_map (fun x -> x + delta) ctx;;
	let bump_indices ctx = delta_indices ctx 1;;
	let add_var v ctx = { mem = ctx.mem |> bump_indices |> mem_add v 0 };;
	let fetch_var v ctx = mem_find v ctx.mem;;

	let rec convert_term_ctx t ctx =
		match t with
		| BoolFalse -> Ir.BoolFalse
		| BoolTrue -> Ir.BoolTrue
		| Nil -> Ir.Nil
		| Nat -> Ir.Nat
		| Bool -> Ir.Bool
		| Unit -> Ir.Unit
		| NatO -> Ir.NatO
		| NatSucc -> Ir.NatSucc
		| Var var -> Ir.Var (fetch_var var ctx)
		| Abs (var, typ, body) -> Ir.Abs (ref var, convert_term_ctx typ ctx, ctx |> add_var var |> convert_term_ctx body)
		| Forall (var, typ, body) -> Ir.Forall (ref var, convert_term_ctx typ ctx, ctx |> add_var var |> convert_term_ctx body)
		| Small -> Ir.Small
		| Type x -> Ir.Type x
		| Prop -> Ir.Prop
		| App (l, r) -> Ir.App (convert_term_ctx l ctx, convert_term_ctx r ctx)
		| Refine (x, y) -> Ir.Refine (convert_term_ctx x ctx, convert_term_ctx y ctx)
		| Convert (x1, x2) -> Ir.Convert (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx)
		| Membership (x1, x2, x3, x4) -> Ir.Membership (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx, convert_term_ctx x4 ctx)
		| SubTrans (x1, x2, x3, x4, x5) -> Ir.SubTrans (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx, convert_term_ctx x4 ctx, convert_term_ctx x5 ctx)
		| SubSub (x1, x2, x3, x4) -> Ir.SubSub (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx, convert_term_ctx x4 ctx)
		| SubRefl x -> Ir.SubRefl (convert_term_ctx x ctx)
		| SubProd (x1, x2, x3, x4, x5, x6) -> Ir.SubProd (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx, convert_term_ctx x4 ctx, convert_term_ctx x5 ctx, convert_term_ctx x6 ctx)
		| SubUnrefine (x1, x2) -> Ir.SubUnrefine (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx)
		| SubGen (x1, x2, x3) -> Ir.SubGen (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx)
		| Subtyping (x1, x2) -> Ir.Subtyping (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx)
		| Extract (x1, x2, x3, x4, x5) -> Ir.Extract (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx, convert_term_ctx x4 ctx, convert_term_ctx x5 ctx)
		| Sumbool (x1, x2) -> Ir.Sumbool (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx)
		| SBLeft (x1, x2) -> Ir.SBLeft (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx)
		| SBRight (x1, x2) -> Ir.SBRight (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx)
		| NatRec (x1, x2, x3, x4) -> Ir.NatRec (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx, convert_term_ctx x4 ctx)
		| BoolRec (x1, x2, x3, x4) -> Ir.BoolRec (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx, convert_term_ctx x4 ctx)
		| SumboolRec (x1, x2, x3, x4, x5, x6) -> Ir.SumboolRec (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx, convert_term_ctx x4 ctx, convert_term_ctx x5 ctx, convert_term_ctx x6 ctx)

		| Conjunction (x1, x2) -> Ir.Conjunction (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx)
		| Disjunction (x1, x2) -> Ir.Disjunction (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx)
		| OrIntroL (x1, x2, x3) -> Ir.OrIntroL (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx)
		| OrIntroR (x1, x2, x3) -> Ir.OrIntroR (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx)
		| AndIntro (x1, x2, x3, x4) -> Ir.AndIntro (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx, convert_term_ctx x4 ctx)
		| Eq (x1, x2, x3) -> Ir.Eq (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx)
		| EqRefl (x1, x2) -> Ir.EqRefl (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx)
		| Exists (v, x1, x2) -> Ir.Exists (ref v, convert_term_ctx x1 ctx, convert_term_ctx x2 (add_var v ctx))
		| Exist (x1, x2, x3, x4) -> Ir.Exist (convert_term_ctx x1 ctx, convert_term_ctx x2 ctx, convert_term_ctx x3 ctx, convert_term_ctx x4 ctx) 

	let convert_term t = convert_term_ctx t (create_empty_context ())
end

module StrToPreIr = struct
	open LambdaAst
	open LambdaLex
 
	let convert_str s =
		let lex_buf = Lexing.from_string s in
		lambda_term lex lex_buf
end