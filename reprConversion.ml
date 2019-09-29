let freshiny_name_impl x f =          
	let build_name_suffix n = if n = 0 then "" else string_of_int n in
	let rec freshiny_name_impl' x f n =
		let s = (x ^ (build_name_suffix n)) in
		if f s then freshiny_name_impl' x f (n + 1)
		else s
	in
	freshiny_name_impl' x f 0
;;		

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

module IrToPreIr = struct
	open Ir;;
	type naming_context = {
		name_mem : string array;
	};;

    let naming_context_from_ir_typing_context ctx =
		{ name_mem = CtxUtil.name_context ctx }
	;;

	let create_empty_naming_context () = { name_mem = Array.make 0 ""; };;

	(* fetch_name : context -> int -> string *)
	let fetch_name ctx v = Array.get ctx.name_mem v;; 

	let freshiny_name x ctx =
		let name_mem_mem ctx v = Array.fold_left (fun acc x -> acc || x = v) false ctx.name_mem in
		freshiny_name_impl x (name_mem_mem ctx)
	;;
	let push_name t ctx = { name_mem = Array.init (Array.length ctx.name_mem + 1) (fun x -> if x = 0 then t else Array.get ctx.name_mem (x - 1)) };;

	let rec convert_prop_ctx t ctx =
		match t with
		| Top -> PreIr.Top
		| Bot -> PreIr.Bot
		| Forall (x, typ, body) -> (
			let x' = freshiny_name x ctx in
			PreIr.Forall (x', convert_type_ctx typ ctx, ctx |> push_name x' |> convert_prop_ctx body)
		)
		| ForallGen (x, body) -> (
			let x' = freshiny_name x ctx in
			PreIr.ForallGen (x', ctx |> push_name x' |> convert_prop_ctx body)
		)
		| Exists (x, typ, body) -> (
			let x' = freshiny_name x ctx in
			PreIr.Forall (x', convert_type_ctx typ ctx, ctx |> push_name x' |> convert_prop_ctx body)
		)
		| Eq (l, r, typ) -> PreIr.Eq (convert_term_ctx l ctx, convert_term_ctx r ctx, convert_type_ctx typ ctx)
		| Conjunction (l, r) -> PreIr.Conjunction (convert_prop_ctx l ctx, convert_prop_ctx r ctx)
		| Disjunction (l, r) -> PreIr.Disjunction (convert_prop_ctx l ctx, convert_prop_ctx r ctx)
		| Implication (l, r) -> PreIr.Implication (convert_prop_ctx l ctx, convert_prop_ctx r ctx)
	and convert_type_ctx t ctx =
		match t with
		| Unit -> PreIr.Unit
		| Nat -> PreIr.Nat
		| Bool -> PreIr.Bool
		| TVar v -> PreIr.TVar (fetch_name ctx v)
		| Refine (v, typ, prp) -> (
			let v' = freshiny_name v ctx in
			PreIr.Refine (v', convert_type_ctx typ ctx, ctx |> push_name v' |> convert_prop_ctx prp)
		)
		| Map (v, l, r) -> (
			let v' = freshiny_name v ctx in
			PreIr.Map (v', convert_type_ctx l ctx, ctx |> push_name v' |> convert_type_ctx r)
		)
		| Prod l -> PreIr.Prod (List.map (fun x -> convert_type_ctx x ctx) l)
		| Gen (v, body) -> (
			let v' = freshiny_name v ctx in
			PreIr.Gen (v', ctx |> push_name v' |> convert_type_ctx body)
		)
	and convert_term_ctx t ctx =
		match t with
		| True -> PreIr.True
		| False -> PreIr.False
		| Nil -> PreIr.Nil
		| NatO -> PreIr.NatO
		| NatSucc -> PreIr.NatSucc
		| Var v -> PreIr.Var (fetch_name ctx v)
		| Abs (v, arg_typ, body) -> (
			let v' = freshiny_name v ctx in
			PreIr.Abs (v', convert_type_ctx arg_typ ctx, ctx |> push_name v' |> convert_term_ctx body)
		)
		| Generic (v, body) -> (
			let v' = freshiny_name v ctx in
			PreIr.Generic (v', ctx |> push_name v' |> convert_term_ctx body)
		)
		| App (l, r) -> PreIr.App (convert_term_ctx l ctx, convert_term_ctx r ctx)
		| TApp (l, r) -> PreIr.TApp (convert_term_ctx l ctx, convert_type_ctx r ctx)
		| Tuple l -> PreIr.Tuple (List.map (fun x -> convert_term_ctx x ctx) l)
		| Proj (l, i) -> PreIr.Proj (convert_term_ctx l ctx, i)
		| Ite (a, b, c, d) -> PreIr.Ite (convert_term_ctx a ctx, convert_term_ctx b ctx, convert_term_ctx c ctx, convert_prop_ctx d ctx)
		| For (a, b, c, d) -> PreIr.For (convert_term_ctx b ctx, convert_term_ctx b ctx, convert_term_ctx c ctx, convert_prop_ctx d ctx)
	;;
	let convert_type t = convert_type_ctx t (create_empty_naming_context ());;
	let convert_term t = convert_term_ctx t (create_empty_naming_context ());;
	let convert_prop t = convert_prop_ctx t (create_empty_naming_context ());;
end
module PreIrToIr = struct	
	open PreIr;;
	module Ctx = Map.Make(String);;

	type index_context = { mem : int Ctx.t };;

	let index_context_from_ir_typing_context ctx =
		{ mem = CtxUtil.name_context ctx |> Array.fold_left (fun (acc, i) x -> (acc |> Ctx.add x i, i + 1)) (Ctx.empty, 0) |> fst }
	;;

	let empty_context = { mem = Ctx.empty };;

	let delta_indices ctx delta = Ctx.map (fun x -> x + delta) ctx;;
	let bump_indices ctx = delta_indices ctx 1;;
	let add_var v ctx = { mem = ctx.mem |> bump_indices |> Ctx.add v 0 };;
	let fetch_var v ctx = Ctx.find v ctx.mem;;

	let rec convert_prop_ctx t ctx =
		match t with
		| Top -> Ir.Top
		| Bot -> Ir.Bot
		| Forall (var, typ, body) -> Ir.Forall (var, convert_type_ctx typ ctx, ctx |> add_var var |> convert_prop_ctx body)
		| Exists (var, typ, body) -> Ir.Exists (var, convert_type_ctx typ ctx, ctx |> add_var var |> convert_prop_ctx body)
		| ForallGen (var, body) -> Ir.ForallGen (var, ctx |> add_var var |> convert_prop_ctx body)
		| Eq (l, r, typ) -> Ir.Eq (convert_term_ctx l ctx, convert_term_ctx r ctx, convert_type_ctx typ ctx)
		| Conjunction (l, r) -> Ir.Conjunction (convert_prop_ctx l ctx, convert_prop_ctx r ctx)
		| Disjunction (l, r) -> Ir.Disjunction (convert_prop_ctx l ctx, convert_prop_ctx r ctx)
		| Implication (l, r) -> Ir.Implication (convert_prop_ctx l ctx, convert_prop_ctx r ctx)
	and convert_type_ctx t ctx =
		match t with
		| Unit -> Ir.Unit
		| Nat -> Ir.Nat
		| Bool -> Ir.Bool
		| TVar var -> Ir.TVar (fetch_var var ctx)
		| Refine (var, typ, prp) -> Ir.Refine (var, convert_type_ctx typ ctx, ctx |> add_var var |> convert_prop_ctx prp)
		| Map (var, l, r) -> Ir.Map (var, convert_type_ctx l ctx, ctx |> add_var var |> convert_type_ctx r)
		| Prod l -> Ir.Prod (List.map (fun x -> convert_type_ctx x ctx) l)
		| Gen (var, body) -> Ir.Gen (var, ctx |> add_var var |> convert_type_ctx body)
	and convert_term_ctx t ctx =
		match t with
		| False -> Ir.False
		| True -> Ir.True
		| Nil -> Ir.Nil
		| NatO -> Ir.NatO
		| NatSucc -> Ir.NatSucc
		| Var var -> Ir.Var (fetch_var var ctx)
		| Abs (var, typ, body) -> Ir.Abs (var, convert_type_ctx typ ctx, ctx |> add_var var |> convert_term_ctx body)
		| Generic (var, body) -> Ir.Generic (var, ctx |> add_var var |> convert_term_ctx body)
		| App (l, r) -> Ir.App (convert_term_ctx l ctx, convert_term_ctx r ctx)
		| TApp (l, r) -> Ir.TApp (convert_term_ctx l ctx, convert_type_ctx r ctx)
		| Tuple l -> Ir.Tuple (List.map (fun x -> convert_term_ctx x ctx) l)
		| Proj (x, i) -> Ir.Proj (convert_term_ctx x ctx, i)
		| Ite (a, b, c, d) -> Ir.Ite (convert_term_ctx a ctx, convert_term_ctx b ctx, convert_term_ctx c ctx, convert_prop_ctx d ctx)
		| For (a, b, c, d) -> Ir.For (convert_term_ctx a ctx, convert_term_ctx b ctx, convert_term_ctx c ctx, convert_prop_ctx d ctx)
	;;

	let convert_term t = convert_term_ctx t empty_context;;
end