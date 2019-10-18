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
