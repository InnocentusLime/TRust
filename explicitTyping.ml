open Ir

(*TODO unification or something like that for prettier impl*)


let (>>=) x f = 
	match x with
	| Some x -> f x
	| None -> None

let solve_universe_problem l r =
	match (l, r) with
	| (Small, Small) -> Some Small
	| (Small, Type x) -> Some (Type x)
	| (Type x, Small) -> Some (Type x)
	| (Type x, Type y) -> Some (Type (max x y))
	| (Prop, Small) -> Some Small
	| (Small, Prop) -> Some Prop
	| (Type x, Prop) -> Some Prop
	| (Prop, Prop) -> Some Prop
	| _ -> None

let solve_refine_problem x x_type y =
	match (x_type, y) with
	| (Small, Forall (_, domain, Prop)) when eq_terms x domain -> Some Small
	| (Type 1, Forall (_, domain, Prop)) when eq_terms x domain -> Some (Type 1)
	| _ -> None

let solve_app_problem l r x =
	match (l, r) with
	| (Forall (_, domain, range), app) when eq_terms domain app -> Some (top_subst range x)
	| _ -> None

let solve_nat_rec_problem n t_choice t_choice_t zero_t step_t n_t =
	let base = App (t_choice, NatO)
	and step =
		Forall (
			ref "n", 
			Nat, 
			Forall (
				ref "_", 
				App (lift1 t_choice, Var 0), 
				App (lift1 t_choice, App (NatSucc, Var 0))
			)
		)
	in
	if 
		eq_terms zero_t (find_normal_form base) 
		&& eq_terms step_t (find_normal_form step)
	then 
		match (t_choice_t, n_t) with
		| (Forall (_, Nat, Type 1), Nat) -> Some (App (t_choice, n))
		| (Forall (_, Nat, Prop), Nat) -> Some (App (t_choice, n))
		| (Forall (_, Nat, Small), Nat) -> Some (App (t_choice, n)) 
		| _ -> None
	else None

let solve_bool_rec_problem t_choice t_choice_t false_t true_t b_t =
	let f = App (t_choice, BoolFalse)
	and t = App (t_choice, BoolTrue)
	in
	if 
		eq_terms false_t (find_normal_form f) 
		&& eq_terms true_t (find_normal_form t)
	then 
		match (t_choice_t, b_t) with
		| (Forall (_, Bool, Type 1), Bool) -> Some false_t
		| (Forall (_, Bool, Prop), Bool) -> Some false_t
		| (Forall (_, Bool, Small), Bool) -> Some false_t 
		| _ -> None
	else None

let solve_convert_problem why what =
	match why with
	| Subtyping (l, r) when eq_terms l what -> Some r 
	| _ -> None

let solve_membership_problem refined_type_t predicate_t proof_t term_t refined_type predicate proof term =
	if 
		beta_eq (Forall (ref "_", refined_type, Prop)) predicate_t &&
		beta_eq (App (predicate, term)) proof_t &&
		beta_eq refined_type term_t &&
		(beta_eq refined_type_t Small || beta_eq refined_type_t (Type 1)) &&
		beta_eq proof_t (App (predicate, term))
	then Some (Refine (term_t, predicate))
	else None

let solve_subtrans_problem x1 x2 x3 x1_type x2_type x3_type x4_type x5_type =
	match (x1_type, x2_type, x3_type, x4_type, x5_type) with
	| (Small, Small, Small, Subtyping (l, o1), Subtyping (o2, r)) when eq_terms x1 l && eq_terms x2 o1 && eq_terms x2 o2 && eq_terms x3 r && eq_terms o1 o2 -> Some (Subtyping (l, r)) 	
	| (Type 1, Type 1, Type 1, Subtyping (l, o1), Subtyping (o2, r)) when eq_terms x1 l && eq_terms x2 o1 && eq_terms x2 o2 && eq_terms x3 r && eq_terms o1 o2 -> Some (Subtyping (l, r))
	| _ -> None

let solve_subunrefine_problem x1 x2 x1_type x2_type =
	if beta_eq x2_type (Forall (ref "_", x1_type, Prop)) then Some (Subtyping (Refine (x1, x2), x1))
	else None

let solve_sumbool_problem l r l_type r_type =
	if beta_eq l_type Prop && beta_eq r_type Prop then Some Small
	else None

let solve_subtype_problem l r =
	match (l, r) with
	| (Small, Small) -> Some Prop
	| (Type 1, Type 1) -> Some Prop
	| _ -> None 

let solve_subgen_problem x1 x2 x3 x1_type x2_type x3_type =
	let f1 = lift1 x1 
	and f2 = lift1 x2 in
	match (find_normal_form x1_type, find_normal_form x2_type) with
	| (Forall (_, Small, Small), Forall (_, Small, Small)) -> 
		if 
			beta_eq 
			x3_type 
			(
				Forall (
					ref "T", 
					Small, 
					Subtyping (App (f1, Var 0), App (f2, Var 0))
				)
			)
		then Some (
			Subtyping (
				Forall (ref "T", Small, App (f1, Var 0)),
				Forall (ref "T", Small, App (f2, Var 0))
			)
		)
		else None
	| (Forall (_, Small, Type 1), Forall (_, Small, Type 1)) ->
		if 
			beta_eq 
			x3_type 
			(
				Forall (
					ref "T", 
					Small, 
					Subtyping (App (f1, Var 0), App (f2, Var 0))
				)
			)
		then Some (
			Subtyping (
				Forall (ref "T", Small, App (f1, Var 0)),
				Forall (ref "T", Small, App (f2, Var 0))
			)
		)
		else None
	| _ -> None

let solve_extract_problem x1 x2 x3 x4 x5 type_x1 type_x2 type_x3 type_x4 type_x5 =
	let x1' = lift1 (lift1 x1)
	and x2' = lift1 x2
	and x3' = lift1 (lift1 x3) 
	and refined_x1 = Refine (x1, x2)
	in
	if 
		beta_eq type_x2 (Forall (ref "_", x1, Prop)) &&
		beta_eq type_x3 (Forall (ref "_", refined_x1, Prop)) &&
		(beta_eq type_x1 (Type 1) || beta_eq type_x1 Small) &&
		beta_eq 
			type_x4 
			(
				Forall (
					ref "x", 
					x1, 
					Forall (
						ref "p",
						App (x2', Var 0),
						App (x3', Membership (x1', lift1 x2', Var 0, Var 1))
					)
				)
			)
		&&
		beta_eq type_x5 refined_x1
	then Some (App (x3, x5))
	else None

let solve_sbleft_problem r l_type r_type l_type_type =
	if 
		beta_eq r_type Prop &&
		beta_eq l_type_type Prop
	then Some (Sumbool (l_type, r))
	else None			

let solve_sbright_problem l l_type r_type r_type_type =
	if 
		beta_eq l_type Prop &&
		beta_eq r_type_type Prop
	then Some (Sumbool (l, r_type))
	else None

let solve_sumbool_rec_problem x1 x2 x3 x6 x1_type x2_type x3_type x4_type x5_type x6_type =
	if			
		beta_eq x1_type Prop &&
		beta_eq x2_type Prop &&
		(beta_eq x3_type (Forall (ref "_", Sumbool (x1, x2), Type 1)) || beta_eq x3_type (Forall (ref "_", Sumbool (x1, x2), Small)) || beta_eq x3_type (Forall (ref "_", Sumbool (x1, x2), Prop))) &&
		beta_eq 
			x4_type 
			(
				Forall (
					ref "p", 
					x1, 
					App (
						lift1 x3, 
						SBLeft (Var 0, lift1 x2)
					)
				)
			)
		&&
		beta_eq 
			x5_type 
			(
				Forall (
					ref "p", 
					x2, 
					App (
						lift1 x3, 
						SBLeft (lift1 x1, Var 0)
					)
				)
			)
		&& beta_eq x6_type (Sumbool (x1, x2))
	then Some (App (x3, x6))
	else None

let solve_subsub_problem x1 x2 x3 x1_type x2_type x3_type x4_type =
	if
		(beta_eq x1_type Small || beta_eq x1_type (Type 1)) &&
		beta_eq x2_type (Forall (ref "_", x1, Prop)) &&
		beta_eq x3_type (Forall (ref "_", x1, Prop)) &&
		beta_eq 
			x4_type 
			(
				Forall (
					ref "x",
					x1,
					Forall (
						ref "_",
						App (lift1 x2, Var 1),
						App (lift1 x3, Var 1)
					)
				)
			) 
	then Some (Subtyping (Refine (x1, x2), Refine (x1, x3)))
	else None

let solve_subrefl_problem x x_type =
	if beta_eq x_type Small || beta_eq x_type (Type 1) then Some (Subtyping (x, x))
	else None

let solve_subprod_problem x1 x2 x3 x4 x5 x1_type x2_type x3_type x4_type x5_type x6_type =
	if
		beta_eq x1_type Small &&
		beta_eq x2_type Small &&
		beta_eq x3_type (Forall (ref "_", x1, Small)) &&
		beta_eq x4_type (Forall (ref "_", x2, Small)) &&
		beta_eq x5_type (Subtyping (x2, x1)) &&
		beta_eq
			x6_type
			(
				Forall (
					ref "x",
					x2,
					Subtyping (
						App (lift1 x3, Convert (x5, Var 0)),
						App (lift1 x4, Var 0)
					)
				) 
			)
	then Some (
		Subtyping (
			Forall (ref "x", x1, App (lift1 x3, Var 0)),
			Forall (ref "x", x2, App (lift1 x4, Var 0))
		)
	)
	else None

let solve_conjunction_problem l_type r_type =
	match (l_type, r_type) with
	| (Prop, Prop) -> Some Prop
	| _ -> None		

let solve_disjunction_problem l_type r_type =
	match (l_type, r_type) with
	| (Prop, Prop) -> Some Prop
	| _ -> None		

let solve_or_introl_problem l_type lt_type rt_type lt rt =
	match (lt_type, rt_type) with
	| (Prop, Prop) when beta_eq l_type lt -> Some (Disjunction (lt, rt))
	| _ -> None

let solve_or_intror_problem r_type lt_type rt_type lt rt =
	match (lt_type, rt_type) with
	| (Prop, Prop) when beta_eq r_type rt -> Some (Disjunction (lt, rt))
	| _ -> None

let solve_eq_problem l_type r_type typ =
	if beta_eq l_type typ && beta_eq r_type typ then Some Prop
	else None

let solve_and_intro_problem l_type r_type lt_type rt_type lt rt =
	if 
		beta_eq lt_type Prop && 
		beta_eq lt_type Prop &&
		beta_eq l_type lt &&
		beta_eq r_type rt
	then Some (Conjunction (lt, rt))
	else None

let solve_eq_refl_problem x x_type typ =	
	if beta_eq x_type typ then Some (Eq (x, x, typ))
	else None

let solve_exists_problem body_type =
	match body_type with
	| Prop -> Some Prop
	| _ -> None

let solve_exist_problem term typ predicate predicate_type term_type proof_type =
	if
		beta_eq typ term_type &&
		beta_eq (Forall (ref "_", typ, Prop)) predicate_type &&
		beta_eq (App (predicate, term)) proof_type
	then Some (Exists (ref "x", typ, App (lift1 predicate, Var 0)))
	else None

let rec typecheck t ctx =
	match t with
	| NatO -> Some Nat
	| NatSucc -> Some (Forall (ref "_", Nat, Nat))
	| BoolTrue -> Some Bool
	| BoolFalse -> Some Bool
	| Nil -> Some Nil
	| Var x -> fetch_var ctx x
	| Bool -> Some Small
	| Nat -> Some Small
	| Unit -> Some Small
	| Forall (str, l, r) -> 
		typecheck l ctx >>= fun l_type ->
		typecheck r (push_var str l_type ctx) >>= fun r_type ->
		solve_universe_problem (find_normal_form l_type) (find_normal_form r_type) 
	| Refine (x, y) ->
		typecheck x ctx >>= fun x_type -> 
		typecheck y ctx >>= fun y_type ->
		solve_refine_problem (find_normal_form x) (find_normal_form x_type) (find_normal_form y_type)
	| Abs (str, l, r) ->
		typecheck l ctx >>= fun l_type ->
		typecheck r (push_var str l ctx) >>= fun r_type ->
		Some (Forall (str, l, r_type))
	| App (l, r) ->
		typecheck l ctx >>= fun l_type ->
		typecheck r ctx >>= fun r_type ->
		solve_app_problem (find_normal_form l_type) (find_normal_form r_type) r
	| NatRec (x1, x2, x3, x4) ->
		typecheck x1 ctx >>= fun x1_type ->
		typecheck x2 ctx >>= fun x2_type ->
		typecheck x3 ctx >>= fun x3_type ->
		typecheck x4 ctx >>= fun x4_type ->
		solve_nat_rec_problem x4 x1 (find_normal_form x1_type) (find_normal_form x2_type) (find_normal_form x3_type) (find_normal_form x4_type)
	| BoolRec (x1, x2, x3, x4) ->
		typecheck x1 ctx >>= fun x1_type ->
		typecheck x2 ctx >>= fun x2_type ->
		typecheck x3 ctx >>= fun x3_type ->
		typecheck x4 ctx >>= fun x4_type ->
		solve_bool_rec_problem x1 (find_normal_form x1_type) (find_normal_form x2_type) (find_normal_form x3_type) (find_normal_form x4_type)
	| Type x -> Some (Type (x + 1))
	| Small -> Some (Type 1)
	| Prop -> Some (Type 1)
	| Convert (why, what) ->
		typecheck why ctx >>= fun why_type ->
		typecheck what ctx >>= fun what_type ->
		solve_convert_problem (find_normal_form why_type) (find_normal_form what_type)
	| Membership (x1, x2, x3, x4) ->
		typecheck x1 ctx >>= fun x1_type ->
		typecheck x2 ctx >>= fun x2_type ->
		typecheck x3 ctx >>= fun x3_type ->
		typecheck x4 ctx >>= fun x4_type ->
		solve_membership_problem x1_type x2_type x3_type x4_type x1 x2 x3 x4
	| SubTrans (x1, x2, x3, x4, x5) ->
		typecheck x1 ctx >>= fun x1_type ->
		typecheck x2 ctx >>= fun x2_type ->
		typecheck x3 ctx >>= fun x3_type ->
		typecheck x4 ctx >>= fun x4_type ->
		typecheck x5 ctx >>= fun x5_type ->
		solve_subtrans_problem (find_normal_form x1) (find_normal_form x2) (find_normal_form x3) (find_normal_form x1_type) (find_normal_form x2_type) (find_normal_form x3_type) (find_normal_form x4_type) (find_normal_form x5_type)
	| SubUnrefine (x1, x2) ->
		typecheck x1 ctx >>= fun x1_type ->
		typecheck x2 ctx >>= fun x2_type ->
		solve_subunrefine_problem x1 x2 x1_type x2_type
	| SubGen (x1, x2, x3) ->
		typecheck x1 ctx >>= fun x1_type ->
		typecheck x2 ctx >>= fun x2_type ->
		typecheck x3 ctx >>= fun x3_type ->
		solve_subgen_problem x1 x2 x3 x1_type x2_type x3_type
	| Subtyping (l, r) ->
		typecheck l ctx >>= fun l_type ->
		typecheck r ctx >>= fun r_type ->
		solve_subtype_problem (find_normal_form l_type) (find_normal_form r_type)
	| Extract (x1, x2, x3, x4, x5) ->
		typecheck x1 ctx >>= fun x1_type ->
		typecheck x2 ctx >>= fun x2_type ->
		typecheck x3 ctx >>= fun x3_type ->
		typecheck x4 ctx >>= fun x4_type ->
		typecheck x5 ctx >>= fun x5_type ->
		solve_extract_problem x1 x2 x3 x4 x5 x1_type x2_type x3_type x4_type x5_type
	| Sumbool (l, r) ->
		typecheck l ctx >>= fun l_type ->
		typecheck r ctx >>= fun r_type ->
		solve_sumbool_problem l r l_type r_type
	| SBLeft (l, r) ->
		typecheck l ctx >>= fun l_type ->
		typecheck r ctx >>= fun r_type ->
		typecheck l_type ctx >>= fun l_type_type ->
		solve_sbleft_problem r l_type r_type l_type_type
	| SBRight (l, r) ->
		typecheck l ctx >>= fun l_type ->
		typecheck r ctx >>= fun r_type ->
		typecheck r_type ctx >>= fun r_type_type ->
		solve_sbleft_problem l l_type r_type r_type_type
	| SumboolRec (x1, x2, x3, x4, x5, x6) ->
		typecheck x1 ctx >>= fun x1_type ->
		typecheck x2 ctx >>= fun x2_type ->
		typecheck x3 ctx >>= fun x3_type ->
		typecheck x4 ctx >>= fun x4_type ->
		typecheck x5 ctx >>= fun x5_type ->
		typecheck x6 ctx >>= fun x6_type ->
		solve_sumbool_rec_problem x1 x2 x3 x6 x1_type x2_type x3_type x4_type x5_type x6_type
	| SubSub (x1, x2, x3, x4) ->
		typecheck x1 ctx >>= fun x1_type ->
		typecheck x2 ctx >>= fun x2_type ->
		typecheck x3 ctx >>= fun x3_type ->
		typecheck x4 ctx >>= fun x4_type ->
		solve_subsub_problem x1 x2 x3 x1_type x2_type x3_type x4_type
	| SubRefl x ->
		typecheck x ctx >>= fun x_type -> solve_subrefl_problem x x_type
	| SubProd (x1, x2, x3, x4, x5, x6) ->
		typecheck x1 ctx >>= fun x1_type ->
		typecheck x2 ctx >>= fun x2_type ->
		typecheck x3 ctx >>= fun x3_type ->
		typecheck x4 ctx >>= fun x4_type ->
		typecheck x5 ctx >>= fun x5_type ->
		typecheck x6 ctx >>= fun x6_type ->
		solve_subprod_problem x1 x2 x3 x4 x5 x1_type x2_type x3_type x4_type x5_type x6_type
	| Conjunction (l, r) ->
		typecheck l ctx >>= fun l_type ->
		typecheck r ctx >>= fun r_type ->
		solve_conjunction_problem l_type r_type
	| Disjunction (l, r) ->
		typecheck l ctx >>= fun l_type ->
		typecheck r ctx >>= fun r_type ->
		solve_disjunction_problem l_type r_type
	| OrIntroL (l, lt, rt) ->
		typecheck l ctx >>= fun l_type ->
		typecheck lt ctx >>= fun lt_type ->
		typecheck rt ctx >>= fun rt_type ->
		solve_or_introl_problem l_type lt_type rt_type lt rt
	| OrIntroR (r, lt, rt) ->
		typecheck r ctx >>= fun r_type ->
		typecheck lt ctx >>= fun lt_type ->
		typecheck rt ctx >>= fun rt_type ->
		solve_or_intror_problem r_type lt_type rt_type lt rt
	| AndIntro (l, r, lt, rt) ->
		typecheck l ctx >>= fun l_type ->
		typecheck r ctx >>= fun r_type ->
		typecheck lt ctx >>= fun lt_type ->
		typecheck rt ctx >>= fun rt_type ->
		solve_and_intro_problem l_type r_type lt_type rt_type lt rt
	| Eq (l, r, typ) ->
		typecheck l ctx >>= fun l_type ->
		typecheck r ctx >>= fun r_type ->
		typecheck typ ctx >>= fun typ_type ->
		solve_eq_problem l_type r_type typ
	| EqRefl (x, typ) ->
		typecheck x ctx >>= fun x_type ->
		typecheck typ ctx >>= fun typ_type ->
		solve_eq_refl_problem x x_type typ
	| Exists (var, arg_typ, body) ->
		typecheck arg_typ ctx >>= fun arg_typ_type ->
		typecheck body (push_var var arg_typ ctx) >>= fun body_type ->
		solve_exists_problem body_type
	| Exist (typ, predicate, term, proof) ->
		typecheck typ ctx >>= fun typ_type ->
		typecheck predicate ctx >>= fun predicate_type ->
		typecheck term ctx >>= fun term_type ->
		typecheck proof ctx >>= fun proof_type ->
		solve_exist_problem term typ predicate predicate_type term_type proof_type
 
let typecheck_ctxless t = typecheck t (create_empty_context ())