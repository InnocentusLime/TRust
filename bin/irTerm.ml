type term =
| Var of string
| Abs of string * term * term
| App of term * term
(* Built-in consts *)
| Total | Divergent
| IntegerType
| IntegerConst of int
| FunctionPointer of string
| Proposition | Type | PreType | ComputationKind | Predicate
| Kind of int 
(* Built-in ops *)
| ComputationType of term * term
| Opposite of term
| Add of term * term
| Subtract of term * term
| Multiply of term * term
| Recursion of string list * int
| Product of string * term * term
| Sequence of term * term
| AndIntroduction of term * term
| OrIntroductionL of term * term
| OrIntroductionR of term * term
| OrElimination of term * term * term
| AndEliminationL of term * term
| AndEliminationR of term * term
| And of term * term
| Or of term * term
| MaxEffect of term * term
| DerefFnPtr of term
| FnPtrType of term
| Eq of term * term * term
| EqIntro of term * term
| Truth
| ProofOfTruth
| Falsity
| EqElim of term * term * term
| FalsityEliminationProposition of term * term
| FalsityEliminationType of term * term
