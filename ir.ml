(*
	The basic facilities for dealing with
	the intermidiate representation of Rust programs.
	The repr is using De Brujin indices
*)

type term_ast =
| NatO | NatSucc | BoolTrue | BoolFalse | Nil | Var of int
| Bool | Nat | Unit | Forall of string ref * term_ast * term_ast | Refine of term_ast * term_ast
| Abs of string ref * term_ast * term_ast | App of term_ast * term_ast
| NatRec of term_ast * term_ast * term_ast * term_ast (* type choice, zero, step, number *)
| BoolRec of term_ast * term_ast * term_ast * term_ast (* type choice, false, true, bool *)
| Type of int | Small | Prop
| Convert of term_ast * term_ast (* reason, term *)
| Membership of term_ast * term_ast * term_ast * term_ast (* type, predicate, proof, term *)
| SubTrans of term_ast * term_ast * term_ast * term_ast * term_ast (* typ1, typ2, typ3, sub1, sub2 *)
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
| SumboolRec of term_ast * term_ast * term_ast * term_ast * term_ast * term_ast (* l_prop, r_prop, type, left, right, arg *)

(*
	We define a special equality to ignore the string pointers
*)
let rec eq_terms l r =
	match (l, r) with
	| (NatO, NatO) -> true
	| (NatSucc, NatSucc) -> true
	| (BoolTrue, BoolTrue) -> true
	| (BoolFalse, BoolFalse) -> true
	| (Nil, Nil) -> true
	| (Var x, Var y) -> x = y
	| (Bool, Bool) -> true
	| (Nat, Nat) -> true
	| (Unit, Unit) -> true
	| (Forall (_, l_typ, l_body), Forall (_, r_typ, r_body)) -> eq_terms l_typ r_typ && eq_terms l_body r_body
	| (Refine (l1, l2), Refine (r1, r2)) -> eq_terms l1 r1 && eq_terms l2 r2
	| (Abs (_, l_type, l_body), Abs (_, r_type, r_body)) -> eq_terms l_type r_type && eq_terms l_body r_body
	| (App (l_x, l_y), App (r_x, r_y)) -> eq_terms l_x r_x && eq_terms l_y r_y
	| (NatRec (l1, l2, l3, l4), NatRec (r1, r2, r3, r4)) -> eq_terms l1 r1 && eq_terms l2 r2 && eq_terms l3 r3 && eq_terms l4 r4
	| (BoolRec (l1, l2, l3, l4), BoolRec (r1, r2, r3, r4)) -> eq_terms l1 r1 && eq_terms l2 r2 && eq_terms l3 r3 && eq_terms l4 r4
	| (Type x, Type y) -> x = y
	| (Small, Small) -> true
	| (Prop, Prop) -> true
	| (Convert (l1, l2), Convert (r1, r2)) -> eq_terms l1 r1 && eq_terms l2 r2
	| (Membership (l1, l2, l3, l4), Membership (r1, r2, r3, r4)) -> eq_terms l1 r1 && eq_terms l2 r2 && eq_terms l3 r3 && eq_terms l4 r4
	| (SubTrans (l1, l2, l3, l4, l5), SubTrans (r1, r2, r3, r4, r5)) -> eq_terms l1 r1 && eq_terms l2 r2 && eq_terms l3 r3 && eq_terms l4 r4 && eq_terms l5 r5
	| (SubSub (l1, l2, l3, l4), SubSub (r1, r2, r3, r4)) -> eq_terms l1 r1 && eq_terms l2 r2 && eq_terms l3 r3 && eq_terms l4 r4
	| (SubRefl l, SubRefl r) -> eq_terms l r
	| (SubProd (l1, l2, l3, l4, l5, l6), SubProd (r1, r2, r3, r4, r5, r6)) -> eq_terms l1 r1 && eq_terms l2 r2 && eq_terms l3 r3 && eq_terms l4 r4 && eq_terms l5 r5 && eq_terms l6 r6
	| (SubUnrefine (l1, l2), SubUnrefine (r1, r2)) -> eq_terms l1 r1 && eq_terms l2 r2
	| (SubGen (l1, l2, l3), SubGen (r1, r2, r3)) -> eq_terms l1 r1 && eq_terms l2 r2 && eq_terms l3 r3
	| (Extract (l1, l2, l3, l4, l5), Extract (r1, r2, r3, r4, r5)) -> eq_terms l1 r1 && eq_terms l2 r2 && eq_terms l3 r3 && eq_terms l4 r4 && eq_terms l5 r5
	| (Subtyping (l1, l2), Subtyping (r1, r2)) -> eq_terms l1 r1 && eq_terms l2 r2
	| (SBLeft (l1, l2), SBLeft (r1, r2)) -> eq_terms l1 r1 && eq_terms l2 r2
	| (SBRight (l1, l2), SBRight (r1, r2)) -> eq_terms l1 r1 && eq_terms l2 r2
	| (Sumbool (l1, l2), Sumbool (r1, r2)) -> eq_terms l1 r1 && eq_terms l2 r2
	| (SumboolRec (l1, l2, l3, l4, l5, l6), SumboolRec (r1, r2, r3, r4, r5, r6)) -> eq_terms l1 r1 && eq_terms l2 r2 && eq_terms l3 r3 && eq_terms l4 r4 && eq_terms l5 r5 && eq_terms l6 r6
	| _ -> false

(*t |^d_c*)
let rec lift t c d =
	match t with
	| NatO -> NatO
	| NatSucc -> NatSucc
	| BoolTrue -> BoolTrue
	| BoolFalse -> BoolFalse
	| Nil -> Nil
	| Var x -> if x < c then Var x else Var (x + d)
	| Bool -> Bool
	| Nat -> Nat
	| Unit -> Unit
	| Forall (str, typ, body) -> Forall (str, lift typ c d, lift body (c + 1) d)
	| Refine (x, y) -> Refine (lift x c d, lift y c d)
	| Abs (str, typ, body) -> Abs (str, lift typ c d, lift body (c + 1) d)
	| App (l, r) -> App (lift l c d, lift r c d)
	| NatRec (x1, x2, x3, x4) -> NatRec (lift x1 c d, lift x2 c d, lift x3 c d, lift x4 c d)
	| BoolRec (x1, x2, x3, x4) -> BoolRec (lift x1 c d, lift x2 c d, lift x3 c d, lift x4 c d)
	| Type x -> Type x
	| Small -> Small
	| Prop -> Prop
	| Convert (x, y) -> Convert (lift x c d, lift y c d)
	| Membership (x1, x2, x3, x4) -> Membership (lift x1 c d, lift x2 c d, lift x3 c d, lift x4 c d)
	| SubTrans (x1, x2, x3, x4, x5) -> SubTrans (lift x1 c d, lift x2 c d, lift x3 c d, lift x4 c d, lift x5 c d)
	| SubSub (x1, x2, x3, x4) -> SubSub (lift x1 c d, lift x2 c d, lift x3 c d, lift x4 c d)
	| SubRefl x -> SubRefl (lift x c d)
	| SubProd (x1, x2, x3, x4, x5, x6) -> SubProd (lift x1 c d, lift x2 c d, lift x3 c d, lift x4 c d, lift x5 c d, lift x6 c d)
	| SubUnrefine (x1, x2) -> SubUnrefine (lift x1 c d, lift x2 c d)
	| SubGen (x1, x2, x3) -> SubGen (lift x1 c d, lift x2 c d, lift x3 c d)
	| Extract (x1, x2, x3, x4, x5) -> Extract (lift x1 c d, lift x2 c d, lift x3 c d, lift x4 c d, lift x5 c d)
	| Subtyping (x1, x2) -> Subtyping (lift x1 c d, lift x2 c d)
	| Sumbool (x1, x2) -> Sumbool (lift x1 c d, lift x2 c d)
	| SBLeft (x1, x2) -> SBLeft (lift x1 c d, lift x2 c d)
	| SBRight (x1, x2) -> SBRight (lift x1 c d, lift x2 c d)
	| SumboolRec (x1, x2, x3, x4, x5, x6) -> SumboolRec (lift x1 c d, lift x2 c d, lift x3 c d, lift x4 c d, lift x5 c d, lift x6 c d)
;;

let clean_after_unbind t = lift t 0 (-1);;

let lift1 t = lift t 0 1;;


(*t[v:=x]*)
let rec subst t v x =
	match t with
	| NatO -> NatO
	| NatSucc -> NatSucc
	| BoolTrue -> BoolTrue
	| BoolFalse -> BoolFalse
	| Nil -> Nil
	| Var v' -> if v = v' then x else Var v'
	| Bool -> Bool
	| Nat -> Nat
	| Unit -> Unit
	| Forall (str, typ, body) -> Forall (str, subst typ v x, subst body (v + 1) (lift1 x))
	| Refine (l, r) -> Refine (subst l v x, subst r v x)
	| Abs (str, typ, body) -> Abs (str, subst typ v x, subst body (v + 1) (lift1 x))
	| App (l, r) -> App (subst l v x, subst r v x)
	| NatRec (x1, x2, x3, x4) -> NatRec (subst x1 v x, subst x2 v x, subst x3 v x, subst x4 v x)
	| BoolRec (x1, x2, x3, x4) -> BoolRec (subst x1 v x, subst x2 v x, subst x3 v x, subst x4 v x)
	| Type x -> Type x
	| Small -> Small
	| Prop -> Prop
	| Convert (x1, x2) -> Convert (subst x1 v x, subst x2 v x)
	| Membership (x1, x2, x3, x4) -> Membership (subst x1 v x, subst x2 v x, subst x3 v x, subst x4 v x)
	| SubTrans (x1, x2, x3, x4, x5) -> SubTrans (subst x1 v x, subst x2 v x, subst x3 v x, subst x4 v x, subst x5 v x)
	| SubSub (x1, x2, x3, x4) -> SubSub (subst x1 v x, subst x2 v x, subst x3 v x, subst x4 v x)
	| SubRefl x1 -> SubRefl (subst x1 v x)
	| SubProd (x1, x2, x3, x4, x5, x6) -> SubProd (subst x1 v x, subst x2 v x, subst x3 v x, subst x4 v x, subst x5 v x, subst x6 v x)
	| SubUnrefine (x1, x2) -> SubUnrefine (subst x1 v x, subst x2 v x)
	| SubGen (x1, x2, x3) -> SubGen (subst x1 v x, subst x2 v x, subst x3 v x)
	| Extract (x1, x2, x3, x4, x5) -> Extract (subst x1 v x, subst x2 v x, subst x3 v x, subst x4 v x, subst x5 v x)
	| Subtyping (x1, x2) -> Subtyping (subst x1 v x, subst x2 v x)
	| Sumbool (x1, x2) -> Sumbool (subst x1 v x, subst x2 v x)
	| SBLeft (x1, x2) -> SBLeft (subst x1 v x, subst x2 v x)
	| SBRight (x1, x2) -> SBRight (subst x1 v x, subst x2 v x)
	| SumboolRec (x1, x2, x3, x4, x5, x6) -> SumboolRec (subst x1 v x, subst x2 v x, subst x3 v x, subst x4 v x, subst x5 v x, subst x6 v x)

let top_subst target subst_value = clean_after_unbind (subst target 0 (lift1 subst_value))

let rec reduction_step t =
	match t with
	| BoolTrue -> BoolTrue
	| BoolFalse -> BoolFalse
	| Nil -> Nil
	| NatO -> NatO
	| NatSucc -> NatSucc
	| Var v -> Var v
	| Bool -> Bool
	| Nat -> Nat
	| Unit -> Unit
	| Forall (str, typ, body) -> (
		let typ' = reduction_step typ in
		if eq_terms typ typ' then Forall (str, typ, reduction_step body)
		else Forall (str, typ', body)
	)
	| Refine (l, r) -> (
		let l' = reduction_step l in
		if eq_terms l l' then Refine (l, reduction_step r)
 		else Refine (l', r)
	)
	| Abs (str, typ, body) -> (
		let typ' = reduction_step typ in
		if eq_terms typ typ' then Abs (str, typ, reduction_step body)
		else Abs (str, typ, body)
	)
	| App (Abs (str, typ, body), arg) -> (
		let abs = Abs (str, typ, body) in
		let abs' = reduction_step abs in
		if eq_terms abs abs' then top_subst body arg
		else App (abs', arg)
	)
	| App (l, r) -> (
		let l' = reduction_step l in
		if eq_terms l l' then App (l, reduction_step r)
		else App (l', r)
	)
	| NatRec (x1, x2, x3, App (NatSucc, n)) -> App (x3, NatRec (x1, x2, x3, n))
	| NatRec (x1, x2, x3, x4) -> NatRec (x1, x2, x3, reduction_step x4)
	| BoolRec (x1, x2, x3, BoolFalse) -> x2
	| BoolRec (x1, x2, x3, BoolTrue) -> x3
	| BoolRec (x1, x2, x3, x4) -> BoolRec (x1, x2, x3, reduction_step x4)
	| Type x -> Type x
	| Small -> Small
	| Prop -> Prop
	| Convert (SubTrans (_, _, _, x1, x2), x3) -> Convert (x2, Convert (x1, x3))
	| Convert (SubSub (x1, _, x2, x3), Membership (_, _, x4, x5)) -> Membership (x1, x2, App (App (x3, x5), x4), x5)
	| Convert (SubRefl _, x) -> x
	| Convert (SubProd (_, x1, _, _, x2, x3), x4) -> 
		Abs (
			ref "x", 
			x1, 
			Convert (
				App (lift1 x3, Var 0), 
				App (lift1 x4, Convert (lift1 x2, Var 0))
			)
		)
	| Convert (SubUnrefine _, Membership (_, _, _, x)) -> x
	| Convert (SubGen (_, _, x1), x2) -> 
		Abs (
			ref "x",
			Small,
			Convert (
				App (lift1 x1, Var 0),
				App (lift1 x2, Var 0)
			)
		)
	| Convert (x1, x2) -> (
		let x1' = reduction_step x1 in
		if eq_terms x1 x1' then Convert (x1', x2)
		else Convert (x1, reduction_step x2)
	)
	| Extract (_, _, _, x1, Membership (_, _, x2, x3)) -> App (App (x1, x3), x2)
	| Extract (x1, x2, x3, x4, x5) -> Extract (x1, x2, x3, x4, reduction_step x5)
	| Subtyping (x1, x2) -> (
		let x1' = reduction_step x1 in
		if eq_terms x1 x1' then Subtyping (x1, reduction_step x2)
		else Subtyping (x1', x2)
	)
	| Sumbool (x1, x2) -> (
		let x1' = reduction_step x1 in
		if eq_terms x1 x1' then Subtyping (x1, reduction_step x2)
		else Subtyping (x1', x2)
	)
	| SBLeft (x1, x2) -> (
		let x1' = reduction_step x1 in
		if eq_terms x1 x1' then Subtyping (x1, reduction_step x2)
		else Subtyping (x1', x2)
	)
	| SBRight (x1, x2) -> (
		let x1' = reduction_step x1 in
		if eq_terms x1 x1' then Subtyping (x1, reduction_step x2)
		else Subtyping (x1', x2)             
	)
	| SumboolRec (_, _, x1, x2, x3, SBLeft (x4, _)) -> App (x2, x4)
	| SumboolRec (_, _, x1, x2, x3, SBRight (_, x4)) -> App (x3, x4)
	| SumboolRec (x1, x2, x3, x4, x5, x6) -> SumboolRec (x1, x2, x3, x4, x5, reduction_step x6)
	| Membership (x1, x2, x3, x4) -> Membership (x1, x2, x3, reduction_step x4)
	| SubTrans _ -> t
	| SubSub _ -> t
	| SubRefl _ -> t
	| SubProd _ -> t
	| SubUnrefine _ -> t
	| SubGen _ -> t

let rec find_normal_form x =
	let x' = reduction_step x in
	if eq_terms x x' then x 
	else find_normal_form x'

let beta_eq x y = eq_terms (find_normal_form x) (find_normal_form y)

type context = {
	mem : (term_ast * string ref) array;
}

let create_empty_context () = { mem = Array.make 0 (Small, ref "I AM A CAT"); }

let lift_context ctx = { mem = Array.map (fun (typ, str) -> (lift1 typ, str)) ctx.mem }

(* fetch_var : context -> int -> term_ast option *)
let fetch_var ctx v =
	if (0 <= v) && (v < Array.length ctx.mem) then Some (fst (Array.get ctx.mem v))
	else None           

let push_var v t ctx = { mem = Array.init (Array.length ctx.mem + 1) (fun x -> if x = 0 then (t, v) else Array.get ctx.mem (x - 1)) } |> lift_context                                                                                                    


(*
(*counts amount of times `n` occurs in `m`*)
let rec count_subterms_term n m =
	if eq_terms m n then 1
	else (
		match m with
		| App (l, r) -> (count_subterms_term n l) + (count_subterms_term n r)
		| TApp (x, _) -> count_subterms_term n x
		| Tuple l -> l |> List.map (count_subterms_term n) |> List.fold_left (+) 0
		| Proj (x, _) -> count_subterms_term n x
		| Ite (a, b, c, _) -> (count_subterms_term n a) + (count_subterms_term n b) + (count_subterms_term n c)
		| For (a, b, c, _) -> (count_subterms_term n a) + (count_subterms_term n b) + (count_subterms_term n c)
		| _ -> 0
	)
and count_subterms_prop n p =
	match p with
	| Eq (l, r, _) -> (count_subterms_term n l) + (count_subterms_term n r)
	| Conjunction (l, r) -> (count_subterms_prop n l) + (count_subterms_prop n r)
	| Disjunction (l, r) -> (count_subterms_prop n l) + (count_subterms_prop n r)
	| Implication (l, r) -> (count_subterms_prop n l) + (count_subterms_prop n r)
	| _ -> 0
;;

(* replaces `n`th' occurance of `x` with `x'` in `y` *)
let rec swap_occurance_term' n x x' y =
	if eq_terms x y then (
		if n = 0 then (x', -1)
		else if n > 0 then (y, n - 1)
		else (y, n)
	) else (
		match y with
		| App (l, r) -> swap_occurance_term' n x x' l |> fun (l', n) -> swap_occurance_term' n x x' r |> fun (r', n) -> (App (l', r'), n)
		| TApp (l, r) -> swap_occurance_term' n x x' l |> fun (l', n) -> (TApp (l', r), n)
		| Proj (l, i) -> swap_occurance_term' n x x' l |> fun (l', n) -> (Proj (l', i), n)
		| Ite (a, b, c, d) -> swap_occurance_term' n x x' a |> fun (a', n) -> swap_occurance_term' n x x' b |> fun (b', n) -> swap_occurance_term' n x x' c |> fun (c', n) -> (Ite (a', b', c', d), n)  
		| For (a, b, c, d) -> swap_occurance_term' n x x' a |> fun (a', n) -> swap_occurance_term' n x x' b |> fun (b', n) -> swap_occurance_term' n x x' c |> fun (c', n) -> (For (a', b', c', d), n)
		| _ -> (y, n)  
	)
and swap_occurance_prop' n x x' y =
	match y with
	| Eq (l, r, t) -> swap_occurance_term' n x x' l |> fun (l', n) -> swap_occurance_term' n x x' r |> fun (r', n) -> (Eq (l', r', t), n)
	| Conjunction (l, r) -> swap_occurance_prop' n x x' l |> fun (l', n) -> swap_occurance_prop' n x x' r |> fun (r', n) -> (Conjunction (l', r'), n)
	| Disjunction (l, r) -> swap_occurance_prop' n x x' l |> fun (l', n) -> swap_occurance_prop' n x x' r |> fun (r', n) -> (Disjunction (l', r'), n)
	| Implication (l, r) -> swap_occurance_prop' n x x' l |> fun (l', n) -> swap_occurance_prop' n x x' r |> fun (r', n) -> (Implication (l', r'), n)
	| _ -> (y, n)
;;

let swap_occurance_term n x x' y = swap_occurance_term' n x x' y |> fst;;
let swap_occurance_prop n x x' p = swap_occurance_prop' n x x' p |> fst;;
*) 