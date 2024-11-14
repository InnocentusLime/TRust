let rec firstn l n =
  match (l, n) with
  | (l, 0) -> l
  | (_ :: t, n) when n > 0 -> firstn t (n - 1)
  | _ -> failwith "bad arg"

type term =
| Var of int
| Abs of string * term * term
| App of term * term
(* Built-in consts *)
| Total | Divergent
| IntegerType
| IntegerConst of int
| FunctionPointer of int
| Proposition | Predicate | Type | PreType
| ComputationKind
| Kind of int
| TypeBuilder
| True | False
| Bool
| Unit
| Nil
(* Built-in ops *)
| ComputationType of term * term
| Opposite of term
| Add of term * term
| Subtract of term * term
| Multiply of term * term
| Recursion of int list * int
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
| BoolRec of term * term * term * term
| BoolRecIndep of term * term * term

(* build the call in shape of `callee arg1 arg2 arg3 ... argn` *)
let build_call callee args = List.fold_left (fun acc x -> App (acc, x)) callee args

let build_product args range =
  match args with
  | (name, typ) :: t ->
    List.fold_left
    (fun acc (name, typ) -> Product (name, typ, acc))
    (Product (name, typ, range))
    t
  | [] -> failwith "no args"

let rec mem_var v t =
  match t with
  | Var v' -> v = v'
  | Abs (_, domain, body) -> mem_var v domain || mem_var (v + 1) body
  | App (l, r) -> mem_var v l || mem_var v r
  | ComputationType (eff, typ) -> mem_var v eff || mem_var v typ
  | Opposite x -> mem_var v x
  | Add (l, r) -> mem_var v l || mem_var v r
  | Subtract (l, r) -> mem_var v l || mem_var v r
  | Multiply (l, r) -> mem_var v l || mem_var v r
  | Product (_, domain, range) -> mem_var v domain || mem_var (v + 1) range
  | Sequence (head, tail) -> mem_var v head || mem_var v tail
  | AndIntroduction (l_proof, r_proof) -> mem_var v l_proof || mem_var v r_proof
  | OrIntroductionL (l_proof, r_prop) -> mem_var v l_proof || mem_var v r_prop
  | OrIntroductionR (r_proof, l_prop) -> mem_var v r_proof || mem_var v l_prop
  | AndEliminationL (l_proof, r_prop) -> mem_var v l_proof || mem_var v r_prop
  | AndEliminationR (r_proof, l_prop) -> mem_var v r_proof || mem_var v l_prop
  | OrElimination (on_left, on_right, proof) -> mem_var v on_left || mem_var v on_right || mem_var v proof
  | And (l, r) -> mem_var v l || mem_var v r
  | Or (l, r) -> mem_var v l || mem_var v r
  | MaxEffect (l, r) -> mem_var v l || mem_var v r
  | DerefFnPtr x -> mem_var v x
  | FnPtrType x -> mem_var v x
  | Eq (l, r, typ) -> mem_var v l || mem_var v r || mem_var v typ
  | EqIntro (value, typ) -> mem_var v value || mem_var v typ
  | EqElim (pred, proof, eq_proof) -> mem_var v pred || mem_var v proof || mem_var v eq_proof
  | FalsityEliminationProposition (prop, proof) -> mem_var v prop || mem_var v proof
  | FalsityEliminationType (typ, proof) -> mem_var v typ || mem_var v proof
  | BoolRec (choice, cond, on_true, on_false) -> mem_var v choice || mem_var v cond || mem_var v on_true || mem_var v on_false
  | BoolRecIndep (cond, on_true, on_false) -> mem_var v cond || mem_var v on_true || mem_var v on_false
  | _ -> false

let rec eq_terms l r =
  match (l, r) with
  | (Var lv, Var rv) when lv = rv -> true
  | (Abs (_, ldom, lbody), Abs (_, rdom, rbody)) -> eq_terms ldom rdom && eq_terms lbody rbody
  | (App (lcallee, larg), App (rcallee, rarg)) -> eq_terms lcallee rcallee && eq_terms larg rarg
  | (Total, Total) -> true
  | (Divergent, Divergent) -> true
  | (IntegerType, IntegerType) -> true
  | (IntegerConst lc, IntegerConst rc) when lc = rc -> true
  | (FunctionPointer lptr, FunctionPointer rptr) when lptr = rptr -> true
  | (Proposition, Proposition) -> true
  | (Type, Type) -> true
  | (PreType, PreType) -> true
  | (True, True) -> true
  | (False, False) -> true
  | (Bool, Bool) -> true
  | (Kind lo, Kind ro) when lo = ro -> true
  | (Predicate, Predicate) -> true
  | (ComputationKind, ComputationKind) -> true
  | (ComputationType (leff, ltype), ComputationType (reff, rtype)) -> eq_terms leff reff && eq_terms ltype rtype
  | (Opposite lterm, Opposite rterm) -> eq_terms lterm rterm
  | (Add (lx, ly), Add (rx, ry)) -> eq_terms lx rx && eq_terms ly ry
  | (Subtract (lx, ly), Subtract (rx, ry)) -> eq_terms lx rx && eq_terms ly ry
  | (Multiply (lx, ly), Multiply (rx, ry)) -> eq_terms lx rx && eq_terms ly ry
  | (Recursion (lbody_list, lid), Recursion (rbody_list, rid)) when lbody_list = rbody_list && lid = rid -> true
  | (Product (_, ldom, lrange), Product (_, rdom, rrange)) -> eq_terms ldom rdom && eq_terms lrange rrange
  | (Sequence (lhead, ltail), Sequence (rhead, rtail)) -> eq_terms lhead rhead && eq_terms ltail rtail
  | (AndIntroduction (lx, ly), AndIntroduction (rx, ry)) -> eq_terms lx rx && eq_terms ly ry
  | (OrIntroductionL (lproof, lprop), OrIntroductionL (rproof, rprop)) -> eq_terms lproof rproof && eq_terms lprop rprop
  | (OrIntroductionR (lproof, lprop), OrIntroductionR (rproof, rprop)) -> eq_terms lproof rproof && eq_terms lprop rprop
  | (OrElimination (lon_left, lon_right, lproof), OrElimination (ron_left, ron_right, rproof)) ->
    eq_terms lon_left ron_left && eq_terms lon_right ron_right && eq_terms lproof rproof
  | (AndEliminationL (lproj, lproof), AndEliminationL (rproj, rproof)) -> eq_terms lproj rproj && eq_terms lproof rproof
  | (AndEliminationR (lproj, lproof), AndEliminationR (rproj, rproof)) -> eq_terms lproj rproj && eq_terms lproof rproof
  | (And (lx, ly), And (rx, ry)) -> eq_terms lx rx && eq_terms ly ry
  | (Or (lx, ly), Or (rx, ry)) -> eq_terms lx rx && eq_terms ly ry
  | (MaxEffect (lx, ly), MaxEffect (rx, ry)) -> eq_terms lx rx && eq_terms ly ry
  | (DerefFnPtr lptr, DerefFnPtr rptr) -> eq_terms lptr rptr
  | (FnPtrType lt, FnPtrType rt) -> eq_terms lt rt
  | (Eq (ll, lr, ltyp), Eq (rl, rr, rtyp)) -> eq_terms ll rl && eq_terms lr rr && eq_terms ltyp rtyp
  | (EqIntro (lvalue, ltyp), EqIntro (rvalue, rtyp)) -> eq_terms lvalue rvalue && eq_terms ltyp rtyp
  | (Truth, Truth) -> true
  | (ProofOfTruth, ProofOfTruth) -> true
  | (Falsity, Falsity) -> true
  | (EqElim (lpred, lproof, leq), EqElim (rpred, rproof, req)) -> eq_terms lpred rpred && eq_terms lproof rproof && eq_terms leq req
  | (FalsityEliminationProposition (lprop, lproof), FalsityEliminationProposition (rprop, rproof)) -> eq_terms lprop rprop && eq_terms lproof rproof
  | (FalsityEliminationType (ltyp, lproof), FalsityEliminationType (rtyp, rproof)) -> eq_terms ltyp rtyp && eq_terms lproof rproof
  | (BoolRec (lchoice, lcond, lon_true, lon_false), BoolRec (rchoice, rcond, ron_true, ron_false)) -> eq_terms lchoice rchoice && eq_terms lcond rcond && eq_terms lon_true ron_true && eq_terms lon_false ron_false
  | (BoolRecIndep (lcond, lon_true, lon_false), BoolRecIndep (rcond, ron_true, ron_false)) -> eq_terms lcond rcond && eq_terms lon_true ron_true && eq_terms lon_false ron_false
  | (TypeBuilder, TypeBuilder) -> true
  | _ -> false

let rec lift_rec k n t =
  match t with
  | Var v -> if v < k then Var v else Var (v + n)
  | Abs (str, dom, body) -> Abs (str, lift_rec k n dom, lift_rec (k + 1) n body)
  | App (callee, arg) -> App (lift_rec k n callee, lift_rec k n arg)
  | ComputationType (eff, typ) -> ComputationType (lift_rec k n eff, lift_rec k n typ)
  | Opposite x -> Opposite (lift_rec k n x)
  | Add (x, y) -> Add (lift_rec k n x, lift_rec k n y)
  | Subtract (x, y) -> Subtract (lift_rec k n x, lift_rec k n y)
  | Multiply (x, y) -> Multiply (lift_rec k n x, lift_rec k n y)
  | Recursion (body, id) -> Recursion (body, id)
  | Product (s, dom, range) -> Product (s, lift_rec k n dom, lift_rec (k + 1) n range)
  | Sequence (head, tail) -> Sequence (lift_rec k n head, lift_rec k n tail)
  | AndIntroduction (x, y) -> AndIntroduction (lift_rec k n x, lift_rec k n y)
  | OrIntroductionL (proof, prop) -> OrIntroductionL (lift_rec k n proof, lift_rec k n prop)
  | OrIntroductionR (proof, prop) -> OrIntroductionR (lift_rec k n proof, lift_rec k n prop)
  | OrElimination (on_left, on_right, proof) -> OrElimination (lift_rec k n on_left, lift_rec k n on_right, lift_rec k n proof)
  | AndEliminationL (proj, proof) -> AndEliminationL (lift_rec k n proj, lift_rec k n proof)
  | AndEliminationR (proj, proof) -> AndEliminationR (lift_rec k n proj, lift_rec k n proof)
  | And (x, y) -> And (lift_rec k n x, lift_rec k n y)
  | Or (x, y) -> Or (lift_rec k n x, lift_rec k n y)
  | MaxEffect (x, y) -> MaxEffect (lift_rec k n x, lift_rec k n y)
  | DerefFnPtr x -> DerefFnPtr (lift_rec k n x)
  | FnPtrType x -> FnPtrType (lift_rec k n x)
  | Eq (l, r, typ) -> Eq (lift_rec k n l, lift_rec k n r, lift_rec k n typ)
  | EqIntro (value, typ) -> EqIntro (lift_rec k n value, lift_rec k n typ)
  | EqElim (pred, proof, eq_proof) -> EqElim (lift_rec k n pred, lift_rec k n proof, lift_rec k n eq_proof)
  | FalsityEliminationProposition (prop, proof) -> FalsityEliminationProposition (lift_rec k n prop, lift_rec k n proof)
  | FalsityEliminationType (typ, proof) -> FalsityEliminationType (lift_rec k n typ, lift_rec k n proof)
  | BoolRec (choice, cond, on_true, on_false) -> BoolRec (lift_rec k n choice, lift_rec k n cond, lift_rec k n on_true, lift_rec k n on_false)
  | BoolRecIndep (cond, on_true, on_false) -> BoolRecIndep (lift_rec k n cond, lift_rec k n on_true, lift_rec k n on_false)
  | _ -> t

let lower_rec k n t = lift_rec k (-n) t

let lift = lift_rec 0

let lower n = lift (-n)

let lift1 = lift 1

let lower1 = lower 1

let rec subst_rec n s t =
  match t with
  | Var v -> if v = n then s else Var v
  | Abs (str, dom, body) -> Abs (str, subst_rec n s dom, subst_rec (n + 1) (lift1 s) body)
  | App (callee, arg) -> App (subst_rec n s callee, subst_rec n s arg)
  | ComputationType (eff, typ) -> ComputationType (subst_rec n s eff, subst_rec n s typ)
  | Opposite x -> Opposite (subst_rec n s x)
  | Add (x, y) -> Add (subst_rec n s x, subst_rec n s y)
  | Subtract (x, y) -> Subtract (subst_rec n s x, subst_rec n s y)
  | Multiply (x, y) -> Multiply (subst_rec n s x, subst_rec n s y)
  | Recursion (l, i) -> Recursion (l, i)
  | Product (str, dom, range) -> Product (str, subst_rec n s dom, subst_rec (n + 1) (lift1 s) range)
  | Sequence (head, tail) -> Sequence (subst_rec n s head, subst_rec n s tail)
  | AndIntroduction (x, y) -> AndIntroduction (subst_rec n s x, subst_rec n s y)
  | OrIntroductionL (proof, prop) -> OrIntroductionL (subst_rec n s proof, subst_rec n s prop)
  | OrIntroductionR (proof, prop) -> OrIntroductionR (subst_rec n s proof, subst_rec n s prop)
  | OrElimination (on_left, on_right, proof) -> OrElimination (subst_rec n s on_left, subst_rec n s on_right, subst_rec n s proof)
  | AndEliminationL (proj, proof) -> AndEliminationL (subst_rec n s proj, subst_rec n s proof)
  | AndEliminationR (proj, proof) -> AndEliminationR (subst_rec n s proj, subst_rec n s proof)
  | And (x, y) -> And (subst_rec n s x, subst_rec n s y)
  | Or (x, y) -> Or (subst_rec n s x, subst_rec n s y)
  | MaxEffect (x, y) -> MaxEffect (subst_rec n s x, subst_rec n s y)
  | DerefFnPtr x -> DerefFnPtr (subst_rec n s x)
  | FnPtrType x -> FnPtrType (subst_rec n s x)
  | Eq (l, r, typ) -> Eq (subst_rec n s l, subst_rec n s r, subst_rec n s typ)
  | EqIntro (value, typ) -> EqIntro (subst_rec n s value, subst_rec n s typ)
  | EqElim (pred, proof, eq_proof) -> EqElim (subst_rec n s pred, subst_rec n s proof, subst_rec n s eq_proof)
  | FalsityEliminationProposition (prop, proof) -> FalsityEliminationProposition (subst_rec n s prop, subst_rec n s proof)
  | FalsityEliminationType (typ, proof) -> FalsityEliminationType (subst_rec n s typ, subst_rec n s proof)
  | BoolRec (choice, cond, on_true, on_false) -> BoolRec (subst_rec n s choice, subst_rec n s cond, subst_rec n s on_true, subst_rec n s on_false)
  | BoolRecIndep (cond, on_true, on_false) -> BoolRecIndep (subst_rec n s cond, subst_rec n s on_true, subst_rec n s on_false)
  | _ -> t

let subst = subst_rec 0

let top_subst s t = lower1 (subst (lift1 s) t)

(* A function. That is what hides behind `FuncPtr[id]` *)
type func =
{
  (* It is assumed all args are ordered by their dependency on each other *)
  args : (string * term) list;
  (* The return type *)
  ret_type : term;
  (* The body of the function. Used in reduction *)
  value : term;
}

(* The context *)
type typing_ctx =
{
  lib : (string * func) list;
  vars : (string * term) list;
}

let empty_ctx =
{
  lib = [];
  vars = [];
}

let dispatch_func ctx n = List.find (fun (n', _) -> n = n') ctx.lib |> snd

let value_of_func ctx i =
  let f = List.nth ctx.lib i |> snd in
  f.value

(* the reduction *)
let rec red1 ctx t =
  match t with
  | Var v -> Var v
  | Abs (s, dom, body) -> Abs (s, red1 ctx dom, body)
  | App (l, r) when not (is_value l) -> App (red1 ctx l, r)
  | App (l, r) when not (is_value r) -> App (l, red1 ctx r)
  | App (Abs (_, _, body), arg) -> top_subst arg body
  | App (Recursion (ptrs, id), arg) -> (
    let chosen_ptr = List.nth ptrs id in
    build_call (DerefFnPtr (FunctionPointer chosen_ptr)) (List.map (fun x -> FunctionPointer (List.nth ptrs x)) ptrs @ [arg])
  )
  | Opposite x when not (is_value x) -> Opposite (red1 ctx x)
  | Opposite (IntegerConst x) -> IntegerConst (-x)
  | Add (l, r) when not (is_value l) -> Add (red1 ctx l, r)
  | Add (l, r) when not (is_value r) -> Add (l, red1 ctx r)
  | Add (IntegerConst l, IntegerConst r) -> IntegerConst (l + r)
  | Subtract (l, r) when not (is_value l) -> Subtract (red1 ctx l, r)
  | Subtract (l, r) when not (is_value r) -> Subtract (l, red1 ctx r)
  | Subtract (IntegerConst l, IntegerConst r) -> IntegerConst (l - r)
  | Multiply (l, r) when not (is_value l) -> Multiply (red1 ctx l, r)
  | Multiply (l, r) when not (is_value r) -> Multiply (l, red1 ctx r)
  | Multiply (IntegerConst l, IntegerConst r) -> IntegerConst (l * r)
  | Sequence (head, tail) when not (is_value head) -> Sequence (red1 ctx head, tail)
  | Sequence (_, tail) -> tail
  | AndIntroduction (l, r) when not (is_value l) -> AndIntroduction (red1 ctx l, r)
  | AndIntroduction (l, r) when not (is_value r) -> AndIntroduction (l, red1 ctx r)
  | OrIntroductionL (proof, prop) when not (is_value prop) -> OrIntroductionL (proof, red1 ctx prop)
  | OrIntroductionL (proof, prop) when not (is_value proof) -> OrIntroductionL (red1 ctx proof, prop)
  | OrElimination (on_left, on_right, proof) when not (is_value proof) -> OrElimination (on_left, on_right, red1 ctx proof)
  | OrElimination (on_left, _, OrIntroductionL (proof, _)) -> App (on_left, proof)
  | OrElimination (_, on_right, OrIntroductionR (proof, _)) -> App (on_right, proof)
  | AndEliminationL (proj, proof) when not (is_value proof) -> AndEliminationL (proj, red1 ctx proof)
  | AndEliminationL (proj, (AndIntroduction (x, _) as proof)) when is_value proof -> App (proj, x)
  | AndEliminationR (proj, proof) when not (is_value proof) -> AndEliminationR (proj, red1 ctx proof)
  | AndEliminationR (proj, (AndIntroduction (_, x) as proof)) when is_value proof -> App (proj, x)
  | And (x, y) when not (is_value x) -> And (red1 ctx x, y)
  | And (x, y) when not (is_value y) -> And (x, red1 ctx y)
  | Or (x, y) when not (is_value x) -> Or (red1 ctx x, y)
  | Or (x, y) when not (is_value y) -> Or (x, red1 ctx y)
  | MaxEffect (Total, x) | MaxEffect (x, Total) -> x
  | MaxEffect (Divergent, _) | MaxEffect (_, Divergent) -> Divergent
  | MaxEffect (x, y) when not (is_value x) -> MaxEffect (red1 ctx x, y)
  | MaxEffect (x, y) when not (is_value y) -> MaxEffect (x, red1 ctx y)
  | ComputationType (x, y) when not (is_value x) -> ComputationType (red1 ctx x, y)
  | ComputationType (x, y) when not (is_value y) -> ComputationType (x, red1 ctx y)
  | DerefFnPtr (FunctionPointer i) -> value_of_func ctx i
  | DerefFnPtr x when not (is_value x) -> DerefFnPtr (red1 ctx x)
  | FnPtrType x when not (is_value x) -> FnPtrType (red1 ctx x)
  | Product (s, l, r) when not (is_value l) -> Product (s, red1 ctx l, r)
  | Product (s, l, r) when not (is_value r) -> Product (s, l, red1 ctx r)
  | Eq (l, r, typ) when not (is_value l) -> Eq (red1 ctx l, r, typ)
  | Eq (l, r, typ) when not (is_value r) -> Eq (l, red1 ctx r, typ)
  | Eq (l, r, typ) when not (is_value typ) -> Eq (l, r, red1 ctx typ)
  | EqIntro (value, typ) when not (is_value value) -> EqIntro (red1 ctx value, typ)
  | EqIntro (value, typ) when not (is_value typ) -> EqIntro (value, red1 ctx typ)
  | EqElim (pred, proof, eq_proof) when not (is_value pred) -> EqElim (red1 ctx pred, proof, eq_proof)
  | EqElim (pred, proof, eq_proof) when not (is_value proof) -> EqElim (pred, red1 ctx proof, eq_proof)
  | EqElim (pred, proof, eq_proof) when not (is_value eq_proof) -> EqElim (pred, proof, red1 ctx eq_proof)
  | EqElim (_, proof, EqIntro (_, _)) -> proof
  | BoolRec (choice, cond, on_true, on_false) when not (is_value cond) -> BoolRec (choice, red1 ctx cond, on_true, on_false)
  | BoolRec (_, True, on_true, _) -> on_true
  | BoolRec (_, False, _, on_false) -> on_false
  | BoolRecIndep (cond, on_true, on_false) when not (is_value cond) -> BoolRecIndep (red1 ctx cond, on_true, on_false)
  | BoolRecIndep (True, on_true, _) -> on_true
  | BoolRecIndep (False, _, on_false) -> on_false
  | _ -> t
and is_value t =
  match t with
  | Total | Divergent | IntegerType
  | IntegerConst _ | FunctionPointer _
  | Proposition | Type | Kind _
  | Recursion _ | Truth | ProofOfTruth | Falsity
  | Bool | True | False | TypeBuilder -> true
  | Abs (_, domain, _) -> is_value domain
  | Product (_, domain, range) -> is_value domain && is_value range
  | ComputationType (eff, typ) -> is_value eff && is_value typ
  | AndIntroduction (l, r) -> is_value l && is_value r
  | OrIntroductionL (l_proof, r_prop) -> is_value l_proof && is_value r_prop
  | OrIntroductionR (r_proof, l_prop) -> is_value r_proof && is_value l_prop
  | And (l, r) -> is_value l && is_value r
  | Or (l, r) -> is_value l && is_value r
  | FnPtrType x -> is_value x
  | Eq (l, r, typ) -> is_value l && is_value r && is_value typ
  | EqIntro (value, typ) -> is_value value && is_value typ
  | _ -> false

let rec reduce_to_computation_type ctx t =
  match t with
  | ComputationType (x, y) -> (x, y)
  | _ -> (
    let t' = red1 ctx t in
    if eq_terms t t' then failwith "The value can't be reduced to a computation type"
    else reduce_to_computation_type ctx t'
  )

let rec reduce_to_product_type ctx t =
  match t with
  | Product (s, x, y) -> (s, x, y)
  | _ -> (
    let t' = red1 ctx t in
    if eq_terms t t' then failwith "The value can't be reduced to a product type"
    else reduce_to_product_type ctx t'
  )

let rec reduce_to_or_type ctx t =
  match t with
  | Or (x, y) -> (x, y)
  | _ -> (
    let t' = red1 ctx t in
    if eq_terms t t' then failwith "The value can't be reduced to a disjunction type"
    else reduce_to_or_type ctx t'
  )

let rec reduce_to_function_pointer_type ctx t =
  match t with
  | FnPtrType x -> x
  | _ -> (
    let t' = red1 ctx t in
    if eq_terms t t' then failwith "The value can't be reduced to a function pointer type"
    else reduce_to_function_pointer_type ctx t'
  )

let rec reduce_to_and_type ctx t =
  match t with
  | And (x, y) -> (x, y)
  | _ -> (
    let t' = red1 ctx t in
    if eq_terms t t' then failwith "The value can't be reduced to a conjunction type"
    else reduce_to_and_type ctx t'
  )

let rec reduce_to_eq_type ctx t =
  match t with
  | Eq (l, r, typ) -> (l, r, typ)
  | _ -> (
    let t' = red1 ctx t in
    if eq_terms t t' then failwith "The value can't be reduced to an equality type"
    else reduce_to_eq_type ctx t'
  )

let is_nf ctx t = eq_terms t (red1 ctx t)

let rec find_nf ?(limit=None) ctx t =
  match limit with
  | None -> if is_nf ctx t then Some t else find_nf ctx (red1 ctx t)
  | Some limit -> (
    if limit = 0 && is_nf ctx t then Some t
    else if limit > 0 then find_nf ~limit:(Some (limit - 1)) ctx (red1 ctx t)
    else if limit < 0 then failwith "negative limit"
    else None
  )

let beta_eq ctx l r =
  match (find_nf ctx l, find_nf ctx r) with
  | (Some l, Some r) -> eq_terms l r
  | _ -> false

let conv = beta_eq

(* Infer the type of func *)
let type_of_func ctx i =
  let f = List.nth ctx.lib i |> snd in
  build_product f.args f.ret_type

(* Fetch the type of a var *)
let type_of_var ctx i = List.nth ctx.vars i |> snd |> lift (i + 1)

(* Add a variable to the context *)
let add_var ctx v =
  {
    lib = ctx.lib;
    vars = v :: ctx.vars;
  }

let add_func ctx v =
  {
    lib = v :: ctx.lib;
    vars = ctx.vars;
  }

let rec tc ctx t =
  match t with
  | Var v -> (
    wf ctx;
    let typ = type_of_var ctx v in
    if tc_is_program_value_type ctx typ then ComputationType (Total, typ)
    else typ
  )
  | Abs (s, domain, body) -> (
    let range = tc (add_var ctx (s, domain)) body in
    if tc_is_program_function ctx s domain range then ComputationType (Total, Product (s, domain, range))
    else Product (s, domain, range)
  )
  | App (callee, arg) -> (
    let func_typ = tc ctx callee
    and arg_typ = tc ctx arg in
    let func_kind = tc ctx func_typ in
    match func_kind with
    | Type -> (
      let (func_eff, func_pre_typ) = reduce_to_computation_type ctx func_typ in
      let (s, domain, range) = reduce_to_product_type ctx func_pre_typ in
      let _ = tc_function_kind ctx s domain range in
      let (body_eff, body_pre_typ) = reduce_to_computation_type ctx range in
      match arg_typ |> tc ctx |> find_nf ctx with
      | Some Type -> (
        let (arg_eff, arg_pre_typ) = reduce_to_computation_type ctx arg_typ in
        if conv ctx domain arg_pre_typ then
            ComputationType (
                MaxEffect (top_subst arg body_eff, MaxEffect (func_eff, arg_eff)),
                top_subst arg body_pre_typ
            )
        else failwith "domain type and arg type are not convertible"
      )
      | Some Proposition -> (
        if conv ctx domain arg_typ then
            ComputationType (
                MaxEffect (top_subst arg body_eff, func_eff),
                top_subst arg body_pre_typ
            )
        else failwith "domain type and arg type are not convertible"
      )
      | _ -> failwith "arg has an illegal kind"
    )
    | Proposition | Predicate | TypeBuilder
    | Kind 0 | Kind 1 | Kind 2 -> (
      let (s, domain, range) = reduce_to_product_type ctx func_typ in
      let _ = tc_function_kind ctx s domain range in
      match arg_typ |> tc ctx |> find_nf ctx with
      | Some Type -> (
        let (arg_eff, arg_pre_typ) = reduce_to_computation_type ctx arg_typ in
        if conv ctx domain arg_pre_typ && conv ctx arg_eff Total then top_subst arg range
        else failwith "domain type and arg type are not convertible or the arguemnt is not toal"
      )
      | Some Proposition | Some ComputationKind | Some PreType | Some Predicate -> (
        if conv ctx domain arg_typ then top_subst arg range
        else failwith "domain type and arg type are not convertible"
      )
      | _ -> failwith "arg has an illegal kind"
    )
    | _ -> failwith "The callee has an illegal kind"
  )
  | Total | Divergent -> wf ctx; ComputationKind
  | Bool -> wf ctx; PreType
  | Unit -> wf ctx; PreType
  | IntegerType -> wf ctx; PreType
  | IntegerConst _ -> wf ctx; ComputationType (Total, IntegerType)
  | True | False -> wf ctx; ComputationType (Total, Bool)
  | Nil -> wf ctx; ComputationType (Total, Unit)
  | FunctionPointer x -> wf ctx; ComputationType (Total, FnPtrType (type_of_func ctx x))
  | Predicate | Proposition | Type | PreType | ComputationKind | TypeBuilder -> wf ctx; Kind 0
  | Kind _ -> failwith "Kind is an illegal expression"
  | ComputationType (eff, typ) -> (
    if conv ctx (tc ctx eff) ComputationKind then (
      if conv ctx (tc ctx typ) PreType then Type
      else failwith "Computation type second component is not a pretype"
    ) else failwith "Computation type first component is not a computation kind"
  )
  | Opposite x -> (
    let (x_eff, x_typ) = reduce_to_computation_type ctx (tc ctx x) in
    if conv ctx x_typ IntegerType then ComputationType (x_eff, IntegerType)
    else failwith "opposite op got a non integer type"
  )
  | Add (l, r) | Subtract (l, r) | Multiply (l, r) -> (
    let (l_eff, l_typ) = reduce_to_computation_type ctx (tc ctx l)
    and (r_eff, r_typ) = reduce_to_computation_type ctx (tc ctx r) in
    if conv ctx l_typ IntegerType && conv ctx r_typ IntegerType then ComputationType (MaxEffect (l_eff, r_eff), IntegerType)
    else failwith "arithmetic operation got non-integer values"
  )
  | Recursion (recs, chosen) -> (
    wf ctx;
    let (ret_typ, args) = (
      let f = chosen |> List.nth recs |> List.nth ctx.lib |> snd in
      (f.ret_type, firstn f.args (List.length recs))
    ) in
    let (eff, ret_typ) = reduce_to_computation_type ctx ret_typ in
    ComputationType (Total, build_product args (ComputationType (MaxEffect (Divergent, eff), ret_typ)))
  )
  | Product (s, domain, range) -> tc_function_kind ctx s domain range
  | Sequence (head, tail) -> (
    let t' = tc ctx head
    and t = tc ctx tail in
    let (eff', _) = reduce_to_computation_type ctx t'
    and (eff, typ) = reduce_to_computation_type ctx t in
    ComputationType (MaxEffect(eff', eff), typ)
  )
  | MaxEffect (l, r) -> (
    if conv ctx (tc ctx l) ComputationKind && conv ctx (tc ctx r) ComputationKind then ComputationKind
    else failwith "arithmetic operation got non-integer values"
  )
  | And (l, r) | Or (l, r) -> (
    if conv ctx (tc ctx l) Proposition && conv ctx (tc ctx r) Proposition then Proposition
    else failwith "Some of parts are not propositions"
  )
  | AndIntroduction (l_proof, r_proof) -> (
    let l_prop = tc ctx l_proof
    and r_prop = tc ctx r_proof in
    if conv ctx (tc ctx l_prop) Proposition && conv ctx (tc ctx r_prop) Proposition then And (l_prop, r_prop)
    else failwith "args are not propositions"
  )
  | OrIntroductionL (l_proof, r_prop) -> (
    let l_prop = tc ctx l_proof in
    if conv ctx (tc ctx l_prop) Proposition && conv ctx (tc ctx r_prop) Proposition then Or (l_prop, r_prop)
    else failwith "args ar not propositions"
  )
  | OrIntroductionR (r_proof, l_prop) -> (
    let r_prop = tc ctx r_proof in
    if conv ctx (tc ctx l_prop) Proposition && conv ctx (tc ctx r_prop) Proposition then Or (l_prop, r_prop)
    else failwith "args ar not propositions"
  )
  | OrElimination (on_left, on_right, proof) -> (
    let (_, on_left_domain, on_left_range) = on_left |> tc ctx |> reduce_to_product_type ctx
    and (_, on_right_domain, on_right_range) = on_right |> tc ctx |> reduce_to_product_type ctx
    and (l_prop, r_prop) = proof |> tc ctx |> reduce_to_or_type ctx in
    if mem_var 0 on_left_range || mem_var 0 on_right_range then failwith "or_elim's result can't depend on input";
    let (on_left_range, on_right_range) = (lower1 on_left_range, lower1 on_right_range) in
    if
      conv ctx (tc ctx l_prop) Proposition && conv ctx (tc ctx r_prop) Proposition &&
      conv ctx on_left_domain l_prop && conv ctx on_right_domain r_prop &&
      conv ctx on_left_range on_right_range
    then on_left_range
    else failwith "or_elim's constraints not satisfied"
  )
  | DerefFnPtr x -> (
    let x_typ = tc ctx x in
    let x_typ_typ = tc ctx x_typ in
    if conv ctx x_typ_typ Type then (
      let (eff, x_typ) = reduce_to_computation_type ctx x_typ in
      let x_typ = reduce_to_function_pointer_type ctx x_typ in
      let _ = reduce_to_product_type ctx x_typ in
      ComputationType (eff, x_typ)
    ) else failwith "Illegal kind"
  )
  | FnPtrType t -> (
    if conv ctx (tc ctx t) PreType then (
      let _ = reduce_to_product_type ctx t in
      PreType
    )
    else failwith "Illegal kind"
  )
  | AndEliminationL (proj, proof) -> (
    let (l_prop, _) = reduce_to_and_type ctx (tc ctx proof)
    and (_, domain, range) = reduce_to_product_type ctx (tc ctx proj) in
    if mem_var 0 range then failwith "range can't depend on input"
    else (
      let range = lower1 range in
      if conv ctx (tc ctx range) Proposition && conv ctx domain l_prop then range
      else failwith "Proofs can only be eliminated to produce proofs or the domain mismatches the left prop"
    )
  )
  | AndEliminationR (proj, proof) -> (
    let (_, r_prop) = reduce_to_and_type ctx (tc ctx proof)
    and (_, domain, range) = reduce_to_product_type ctx (tc ctx proj) in
    if mem_var 0 range then failwith "range can't depend on input"
    else (
      let range = lower1 range in
      if conv ctx (tc ctx range) Proposition && conv ctx domain r_prop then range
      else failwith "Proofs can only be eliminated to produce proofs or the domain mismatches the right prop"
    )
  )
  | Eq (l, r, typ) -> (
    let l_typ = tc ctx l
    and r_typ = tc ctx r
    and typ_typ = tc ctx typ in
    let (l_eff, l_typ) = reduce_to_computation_type ctx l_typ
    and (r_eff, r_typ) = reduce_to_computation_type ctx r_typ in
    if
      conv ctx l_typ typ &&
      conv ctx r_typ typ &&
      conv ctx typ_typ PreType &&
      conv ctx l_eff Total &&
      conv ctx r_eff Total
    then Proposition
    else failwith "Eq typing constraints not satisfied"
  )
  | EqIntro (value, typ) -> (
    let value_typ = tc ctx value
    and typ_typ = tc ctx typ in
    let (value_eff, value_typ) = reduce_to_computation_type ctx value_typ in
    if
      conv ctx value_typ typ &&
      conv ctx typ_typ PreType &&
      conv ctx value_eff Total
    then Eq (value, value, typ)
    else failwith "EqIntro typing contraints not satisfied"
  )
  | Truth -> wf ctx; Proposition
  | ProofOfTruth -> wf ctx; Truth
  | Falsity -> wf ctx; Proposition
  | EqElim (pred, proof, eq_proof) -> (
    let (l, r, typ) = eq_proof |> tc ctx |> reduce_to_eq_type ctx
    and (_, domain, range) = pred |> tc ctx |> reduce_to_product_type ctx
    and proof_typ = proof |> tc ctx in
    if
      conv ctx typ domain &&
      conv ctx range Proposition
    then (
      if conv ctx proof_typ (App (pred, l)) then App (pred, r)
      else failwith "predicate constraint not satisfied"
    )
    else failwith "eq_elim constraints are not satisfied"
  )
  | FalsityEliminationProposition (prop, proof) -> (
    let proof_typ = tc ctx proof
    and prop_kind = tc ctx prop in
    if
      conv ctx proof_typ Falsity &&
      conv ctx prop_kind Proposition
    then prop
    else failwith "falsity elimination constraints not satisfied"
  )
  | FalsityEliminationType (typ, proof) -> (
    let proof_typ = tc ctx proof
    and typ_kind = tc ctx typ in
    if
      conv ctx proof_typ Falsity &&
      conv ctx typ_kind PreType
    then ComputationType (Total, typ)
    else failwith "falsity elimination constraints not satisfied"
  )
  | BoolRec (choice, cond, on_true, on_false) -> (
        let cond_pre_type = tc_is_total ctx cond in
        let (_, domain, range) = tc ctx choice |> reduce_to_product_type ctx in
        if not (conv ctx cond_pre_type Bool && conv ctx domain cond_pre_type) then failwith "bool range check failed";
        if
          conv ctx (tc ctx on_true) (App (choice, True)) &&
          conv ctx (tc ctx on_false) (App (choice, False))
        then (
          if mem_var 0 range then failwith "range can't depend on input"
          else (
            let range = lower1 range in
            if conv ctx range Type || conv ctx range Proposition || conv ctx range (Kind 0) then (App (choice, cond))
            else failwith "BoolRec can build only Types, Propositions and Kind[0]s"
          )
        ) else failwith "BoolRec constraints not satisfied"
  )
  | BoolRecIndep (cond, on_true, on_false) -> (
        let (cond_eff, cond_pre_type) = tc ctx cond |> reduce_to_computation_type ctx in
        let on_true_typ = tc ctx on_true in
        if not (conv ctx cond_pre_type Bool) then failwith "bool range check failed";
        if
          conv ctx on_true_typ (tc ctx on_false)
        then (
          if conv ctx on_true_typ Proposition || conv ctx on_true_typ Type then (
            if conv ctx cond_eff Total then on_true_typ
            else failwith "Condition of an if which constructs a `Prop` or `Type`, must be total"
          )
          else if conv ctx (tc ctx on_true_typ) Type then (
             let (on_true_eff, on_true_pre_typ) = reduce_to_computation_type ctx on_true_typ in
             ComputationType (MaxEffect (cond_eff, on_true_eff), on_true_pre_typ)
          )
          else failwith "range can only be Prop, Type or a Type"
        ) else failwith "BoolRecIndep constraints not satisfied"
  )
and tc_function_kind ctx s domain range =
  let range_typ = tc (add_var ctx (s, domain)) range |> find_nf ctx |> Option.get
  and domain = domain |> find_nf ctx |> Option.get in
  match (domain, range_typ) with
  (* User functions *)
  | (_, Type) when conv ctx (tc ctx domain) PreType -> PreType
  | (_, Type) when conv ctx (tc ctx domain) Proposition -> PreType
  | (PreType, Type) -> Kind 1
  | (PreType, Kind 1) -> Kind 1
  | (ComputationKind, Type) -> Kind 2
  | (ComputationKind, Kind 1) -> Kind 2
  | (ComputationKind, Kind 2) -> Kind 2
  (* Propositions *)
  | (Proposition, Kind 0) when conv (add_var ctx (s, domain)) range Proposition -> Proposition
  | (Proposition, Proposition) -> Proposition
  | (_, Proposition) when conv ctx (tc ctx domain) PreType -> Proposition
  | (PreType, Proposition) -> Proposition
  | (_, Proposition) when conv ctx (tc ctx domain) Proposition -> Proposition
  | (_ , Proposition) when conv ctx (tc ctx domain) Predicate -> Proposition
  (* Predicates *)
  | (_, _) when conv ctx (tc ctx domain) PreType && conv ctx range Proposition -> Predicate
  | (PreType, Predicate) -> Predicate
  | (_, Predicate) when conv ctx (tc ctx domain) PreType -> Predicate
  (* Type builders *)
  | (_, _) when conv ctx (tc ctx domain) PreType && conv ctx range Type -> TypeBuilder
  | (_, TypeBuilder) when conv ctx (tc ctx domain) PreType -> TypeBuilder
  | (PreType, TypeBuilder) -> TypeBuilder
  | _ -> failwith "Untypable function"
and tc_is_program_value_type ctx t = conv ctx (tc ctx t) PreType
and tc_is_program_function ctx s domain range = (tc_function_kind ctx s domain range = PreType)
and wf _ = ()
and tc_is_total ctx t =
  let typ = tc ctx t in
  let (eff, typ) = reduce_to_computation_type ctx typ in
  if conv ctx eff Total then typ
  else failwith "The term is not total"
