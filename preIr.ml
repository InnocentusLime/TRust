(*
	This is an incomplete IR. It uses strings for
	variables instead of De Brujin indices
*)

type term_ast =
| NatO | NatSucc | BoolTrue | BoolFalse | Nil | Var of string
| Bool | Nat | Unit | Forall of string * term_ast * term_ast | Refine of term_ast * term_ast
| Abs of string * term_ast * term_ast | App of term_ast * term_ast
| NatRec of term_ast * term_ast * term_ast * term_ast (* type choice, zero, step, number *)
| BoolRec of term_ast * term_ast * term_ast * term_ast (* type choice, false, true, bool *)
| Type of int | Small | Prop
| Convert of term_ast * term_ast (* reason, term *)
| Membership of term_ast * term_ast * term_ast * term_ast (* type, predicate, proof, term *)
| SubTrans of term_ast * term_ast * term_ast * term_ast * term_ast
| SubSub of term_ast * term_ast * term_ast * term_ast (* type, predicate1, predicate2, proof *)
| SubRefl of term_ast
| SubProd of term_ast * term_ast * term_ast * term_ast * term_ast * term_ast (* domain_l, domain_r, range_l, range_r, domain_subtyping, range_sutyping *)
| SubUnrefine of term_ast * term_ast
| SubGen of term_ast * term_ast * term_ast (* type_chooser_l, type_chooser_r, sub_typing *)
| Subtyping of term_ast * term_ast
| Extract of term_ast * term_ast * term_ast * term_ast * term_ast (* type, predicate, target, proof, term *)
| Sumbool of term_ast * term_ast
| SBLeft of term_ast * term_ast
| SBRight of term_ast * term_ast
| SumboolRec of term_ast * term_ast * term_ast * term_ast * term_ast * term_ast (* left_prop, right_prop, type, left, right, arg *)
(* "Ghost terms" or "notations" --- the terms which are here for syntaticalc convenience, but get expanded to their definition when needed *)
| Conjunction of term_ast * term_ast
| Disjunction of term_ast * term_ast
| OrIntroL of term_ast * term_ast * term_ast
| OrIntroR of term_ast * term_ast * term_ast
| AndIntro of term_ast * term_ast * term_ast * term_ast
| Eq of term_ast * term_ast * term_ast
| EqRefl of term_ast * term_ast
| Exists of string * term_ast * term_ast
| Exist of term_ast * term_ast * term_ast * term_ast (* type, predicate, term, proof *)

let implication l r = Forall ("_", l, r)

(*
let rec var_occurs v t =
	match t with
	| NatO -> false
	| NatSucc -> false
	| BoolTrue -> false
	| BoolFalse -> false
	| Nil -> false
	| Nat -> false
	| Bool -> false
	| Unit -> false
	| Var x -> x = v
	| Forall (x, arg, body) -> (if x = v then false else var_occurs v body) || var_occurs v arg
	| Refine (l, r) -> var_occurs v l || var_occurs v r
	| Abs (x, arg, body) -> (if x = v then false else var_occurs v body) || var_occurs v arg	
	| App (l, r) -> var_occurs v l || var_occurs v r
	| NatRec (x1, x2, x3, x4) -> var_occurs v x1 || var_occurs v x2 || var_occurs v x3 || var_occurs v x4
	| BoolRec (x1, x2, x3, x4) -> var_occurs v x1 || var_occurs v x2 || var_occurs v x3 || var_occurs v x4
	| Type _ -> false
	| Small -> false
	| Prop -> false
	| Convert (x, y) -> var_occurs v x || var_occurs v y
	| Membership (x1, x2, x3, x4) -> var_occurs v x1 || var_occurs v x2 || var_occurs v x3 || var_occurs v x4
	| SubTrans (x1, x2, x3, x4, x5) -> var_occurs v x1 || var_occurs v x2 || var_occurs v x3 || var_occurs v x4 || var_occurs v x5
	| SubSub (x1, x2, x3, x4) -> var_occurs v x1 || var_occurs v x2 || var_occurs v x3 || var_occurs v x4
	| SubRefl x -> var_occurs v x
	| SubProd (x1, x2, x3, x4, x5, x6) -> var_occurs v x1 || var_occurs v x2 || var_occurs v x3 || var_occurs v x4 || var_occurs v x5 || var_occurs v x6
	| SubUnrefine (x1, x2) -> var_occurs v x1 || var_occurs v x2
	| SubGen (x1, x2, x3) -> var_occurs v x1 || var_occurs v x2 || var_occurs v x3
	| Subtyping (x1, x2) -> var_occurs v x1 || var_occurs v x2
	| Extract (x1, x2, x3, x4, x5) -> var_occurs v x1 || var_occurs v x2 || var_occurs v x3 || var_occurs v x4 || var_occurs v x5
	| Sumbool (x1, x2) -> var_occurs v x1 || var_occurs v x2
	| SBLeft (x1, x2) -> var_occurs v x1 || var_occurs v x2
	| SBRight (x1, x2) -> var_occurs v x1 || var_occurs v x2
	| SumboolRec (x1, x2, x3, x4, x5, x6) -> var_occurs v x1 || var_occurs v x2 || var_occurs v x3 || var_occurs v x4 || var_occurs v x5 || var_occurs v x6
	| Notation (x, _) -> var_occurs v x
*)