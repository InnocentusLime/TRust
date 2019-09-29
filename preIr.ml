(*
	This is an incomplete IR. It uses strings for
	variables instead of De Brujin indices
*)

type prop_ast =
| Top
| Bot
| Forall of string * type_ast * prop_ast
| ForallGen of string * prop_ast
| Exists of string * type_ast * prop_ast
| Eq of term_ast * term_ast * type_ast
| Conjunction of prop_ast * prop_ast
| Disjunction of prop_ast * prop_ast
| Implication of prop_ast * prop_ast
and type_ast =
| Unit
| Nat
| Bool
| TVar of string
| Refine of string * type_ast * prop_ast
| Map of string * type_ast * type_ast
| Prod of type_ast list
| Gen of string * type_ast
and term_ast =
| False
| True
| Nil
| NatO
| NatSucc
| Var of string
| Abs of string * type_ast * term_ast
| Generic of string * term_ast
| App of term_ast * term_ast
| TApp of term_ast * type_ast
| Tuple of term_ast list
| Proj of term_ast * int
| Ite of term_ast * term_ast * term_ast * prop_ast
| For of term_ast * term_ast * term_ast * prop_ast 
;;

let rec string_of_prop t =
	match t with
	| Top -> "TRUE"
	| Bot -> "FALSE"
	| Forall (v, typ, body) -> "forall " ^ v ^ ":" ^ (string_of_type typ) ^ "." ^ (string_of_prop body)
	| ForallGen (v, body) -> "forall " ^ v ^ "." ^ (string_of_prop body)
	| Exists (v, typ, body) -> "exists " ^ v ^ ":" ^ (string_of_type typ) ^ "." ^ (string_of_prop body)
	| Eq (l, r, typ) -> "(" ^ (string_of_term l) ^ " == " ^ (string_of_term r) ^ " :> " ^ (string_of_type typ) ^ ")"
	| Conjunction (l, r) -> "(" ^ (string_of_prop l) ^ " /\\ " ^ (string_of_prop r) ^ ")" 
	| Disjunction (l, r) -> "(" ^ (string_of_prop l) ^ " \\/ " ^ (string_of_prop r) ^ ")" 
	| Implication (l, r) -> "(" ^ (string_of_prop l) ^ " => " ^ (string_of_prop r) ^ ")" 
and string_of_type t =
	match t with
	| Unit -> "unit"
	| Nat -> "nat"
	| Bool -> "bool"
	| TVar v -> v
	| Refine (v, typ, prp) -> "{" ^ v ^ ":" ^ (string_of_type typ) ^ "|" ^ (string_of_prop prp) ^ "}"
	| Map (v, l, r) -> 
		if v = "_" then "(" ^ (string_of_type l) ^ "->" ^ (string_of_type r) ^ ")"
		else "((" ^ v ^ ":" ^ (string_of_type l) ^ ") -> " ^ (string_of_type r) ^ ")"
	| Prod l -> String.concat " * " (List.map string_of_type l)
	| Gen (v, body) -> "forall " ^ v ^ "." ^ (string_of_type body)
and string_of_term t =
	match t with
	| False -> "false"
	| True -> "true"
	| Nil -> "nil"
	| NatO -> "O"
	| NatSucc -> "succ"
	| Var v -> v
	| Abs (v, typ, body) -> "(/" ^ v ^ ":" ^ (string_of_type typ) ^ "." ^ (string_of_term body) ^ ")"
	| Generic (v, body) -> "(//" ^ v ^ "." ^ (string_of_term body) ^ ")"
	| App (l, r) -> "(" ^ (string_of_term l) ^ " " ^ (string_of_term r) ^ ")"
	| TApp (l, r) -> "(" ^ (string_of_term l) ^ " (" ^ (string_of_type r) ^ "))"
	| Tuple l -> String.concat ", " (List.map string_of_term l)
	| Proj (l, i) -> (string_of_term l) ^ "." ^ (string_of_int i)
	| Ite (a, b, c, d) -> "if " ^ (string_of_term a) ^ " <" ^ (string_of_prop d) ^ "> then {" ^ (string_of_term b) ^ "} else {" ^ (string_of_term c) ^ "}"
	| For (a, b, c, d) -> "for " ^ (string_of_term a) ^ " <" ^ (string_of_prop d) ^ "> do {" ^ (string_of_term b) ^ "} {" ^ (string_of_term c) ^ "}"
;;

module Ctx = Map.Make(String);;

type index_context = { mem : int Ctx.t };;

let empty_context = { mem = Ctx.empty };;

let delta_indices ctx delta = Ctx.map (fun x -> x + delta) ctx;;
let bump_indices ctx = delta_indices ctx 1;;
let add_var v ctx = { mem = ctx.mem |> bump_indices |> Ctx.add v 0 };;
let fetch_var v ctx = Ctx.find v ctx.mem;;

let rec convert_prop' t ctx =
	match t with
	| Top -> Ir.Top
	| Bot -> Ir.Bot
	| Forall (var, typ, body) -> Ir.Forall (var, convert_type' typ ctx, ctx |> add_var var |> convert_prop' body)
	| Exists (var, typ, body) -> Ir.Exists (var, convert_type' typ ctx, ctx |> add_var var |> convert_prop' body)
	| ForallGen (var, body) -> Ir.ForallGen (var, ctx |> add_var var |> convert_prop' body)
	| Eq (l, r, typ) -> Ir.Eq (convert_term' l ctx, convert_term' r ctx, convert_type' typ ctx)
	| Conjunction (l, r) -> Ir.Conjunction (convert_prop' l ctx, convert_prop' r ctx)
	| Disjunction (l, r) -> Ir.Disjunction (convert_prop' l ctx, convert_prop' r ctx)
	| Implication (l, r) -> Ir.Implication (convert_prop' l ctx, convert_prop' r ctx)
and convert_type' t ctx =
	match t with
	| Unit -> Ir.Unit
	| Nat -> Ir.Nat
	| Bool -> Ir.Bool
	| TVar var -> Ir.TVar (fetch_var var ctx)
	| Refine (var, typ, prp) -> Ir.Refine (var, convert_type' typ ctx, ctx |> add_var var |> convert_prop' prp)
	| Map (var, l, r) -> Ir.Map (var, convert_type' l ctx, ctx |> add_var var |> convert_type' r)
	| Prod l -> Ir.Prod (List.map (fun x -> convert_type' x ctx) l)
	| Gen (var, body) -> Ir.Gen (var, ctx |> add_var var |> convert_type' body)
and convert_term' t ctx =
	match t with
	| False -> Ir.False
	| True -> Ir.True
	| Nil -> Ir.Nil
	| NatO -> Ir.NatO
	| NatSucc -> Ir.NatSucc
	| Var var -> Ir.Var (fetch_var var ctx)
	| Abs (var, typ, body) -> Ir.Abs (var, convert_type' typ ctx, ctx |> add_var var |> convert_term' body)
	| Generic (var, body) -> Ir.Generic (var, ctx |> add_var var |> convert_term' body)
	| App (l, r) -> Ir.App (convert_term' l ctx, convert_term' r ctx)
	| TApp (l, r) -> Ir.TApp (convert_term' l ctx, convert_type' r ctx)
	| Tuple l -> Ir.Tuple (List.map (fun x -> convert_term' x ctx) l)
	| Proj (x, i) -> Ir.Proj (convert_term' x ctx, i)
	| Ite (a, b, c, d) -> Ir.Ite (convert_term' a ctx, convert_term' b ctx, convert_term' c ctx, convert_prop' d ctx)
	| For (a, b, c, d) -> Ir.For (convert_term' a ctx, convert_term' b ctx, convert_term' c ctx, convert_prop' d ctx)
;;

let convert_term t = convert_term' t empty_context;;