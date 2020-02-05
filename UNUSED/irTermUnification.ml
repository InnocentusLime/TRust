open Ir

type unify_eqn = term_ast * term_ast
type unify_equation = unify_eqn list

let solve_eqn (l, r) =
	match (l, r) with
	| (Unknown, _) -> Some []
	| (_, Unknown) -> Some []
	| (NatO, NatO) -> Some []
	| (Nat, Nat) -> Some []
	| (Bool, Bool) -> Some []
	| (Unit, Unit) -> Some []
	| (NatSucc, NatSucc) -> Some []
	| (BoolFalse, BoolFalse) -> Some []
	| (Sumbool (l1, l2), Sumbool (r1, r2)) -> Some ((l1, r1) :: (l2, r2) :: [])
	| (Subtyping (l1, l2), Subtyping (r1, r2)) -> Some ((l1, r1) :: (l2, r2) :: [])
	| (Var l, Var r) -> if l = r then Some [] else None
	| (Forall (_, l1, l2), Forall (_, r1, r2)) -> Some ((l1, r1) :: (l2, r2) :: [])
	| (Refine l, Refine r) -> Some ((l, r) :: [])
	| (Abs (_, l1, l2), Abs (_, r1, r2)) -> Some ((l1, r1) :: (l2, r2) :: [])
	| (App (l1, l2), App (r1, r2)) -> Some ((l1, l2) :: (r1, r2) :: [])
	| (NatRec (l1, l2, l3, App (NatSucc, l4)), NatRec (r1, r2, r3, App (NatSucc, r4))) -> Some ((App (l3, NatRec (l1, l2, l3, l4)), App (r3, NatRec (r1, r2, r3, r4))) :: [])
	| (NatRec (l1, l2, l3, NatO), NatRec (r1, r2, r3, NatO)) -> Some ((l2, r2) :: [])
	| (NatRec (l1, l2, l3, l4), NatRec (r1, r2, r3, r4)) -> 
		let l4' = reduction_step l4 
		and r4' = reduction_step r4 in
		if eq_terms l4 l4' then (
			if eq_terms r4 r4' then Some ((l1, r1) :: (l2, r2) :: (l3, r3) :: (l4, r4) :: [])
			else Some ((NatRec (l1, l2, l3, l4), NatRec (r1, r2, r3, r4')) :: [])
		) else Some ((NatRec (l1, l2, l3, l4'), NatRec (r1, r2, r3, r4)) :: []) 
	| (BoolRec (l1, l2, l3, BoolFalse), BoolRec (r1, r2, r3, BoolFalse)) -> Some ((l2, r2) :: [])
	| (BoolRec (l1, l2, l3, BoolTrue), BoolRec (r1, r2, r3, BoolTrue)) -> Some ((l3, r3) :: [])
	| (BoolRec (l1, l2, l3, l4), BoolRec (r1, r2, r3, r4)) -> 
	    let l4' = reduction_step l4
		and r4' = reduction_step r4 in
		if eq_terms l4 l4' then (
			if eq_terms r4 r4' then Some ((l1, r1) :: (l2, r2) :: (l3, r3) :: (l4, r4) :: [])
			else Some ((BoolRec (l1, l2, l3, l4), BoolRec (r1, r2, r3, r4')) :: [])
		) else Some ((BoolRec (l1, l2, l3, l4'), BoolRec (r1, r2, r3, r4)) :: []) 
	| (SumboolRec (l1, l2, l3, SBLeft (l4, _)), SumboolRec (r1, r2, r3, SBLeft (r4, _))) -> Some ((App (l2, l4), App (r2, r4)) :: [])
	| (SumboolRec (l1, l2, l3, SBRight (_, l4)), SumboolRec (r1, r2, r3, SBRight (_, r4))) -> Some ((App (l2, l4), App (r2, r4)) :: [])
	| (SumboolRec (l1, l2, l3, l4), SumboolRec (r1, r2, r3, r4)) -> 
	    let l4' = reduction_step l4
		and r4' = reduction_step r4 in
		if eq_terms l4 l4' then (
			if eq_terms r4 r4' then Some ((l1, r1) :: (l2, r2) :: (l3, r3) :: (l4, r4) :: [])
			else Some ((SumboolRec (l1, l2, l3, l4), SumboolRec (r1, r2, r3, r4')) :: [])
		) else Some ((SumboolRec (l1, l2, l3, l4'), SumboolRec (r1, r2, r3, r4)) :: []) 
	| (Type l, Type r) -> if l = r then Some [] else None
	| (Small, Small) -> Some []
	| (Prop, Prop) -> Some []
	| (Convert (SubTrans (l1, l2), l3), Convert (SubTrans (r1, r2), r3)) -> Some ((Convert (l2, Convert (l1, l3)), Convert (r2, Convert (r1, r3))) :: [])
	| (Convert (SubSub (l1, _, l2, l3), Membership (_, _, l4, l5)), Convert (SubSub (r1, _, r2, r3), Membership (_, _, r4, r5))) -> Some((Membership (l1, l2, App (App (l3, l5), l4), l5), Membership (r1, r2, App (App (r3, r5), r4), r5)) :: [])
	| (Convert (SubRefl _, l), Convert (SubRefl _, r)) -> Some ((l, r) :: [])
	| (Convert (SubProd (_, l1, _, _, l2, l3), l4), Convert (SubProd (_, r1, _, _, r2, r3), r4)) ->
		Some ( 
			(Abs (
				ref "x", 
				l1, 
				Convert (
					App (lift1 l3, Var 0), 
					App (lift1 l4, Convert (lift1 l2, Var 0))
				)
			),
			Abs (
				ref "x", 
				r1, 
				Convert (
					App (lift1 r3, Var 0), 
					App (lift1 r4, Convert (lift1 r2, Var 0))
				)
			)) :: []
		)
	| (Convert (SubUnrefine, Membership (_, _, _, l)), Convert (SubUnrefine, Membership (_, _, _, r))) -> Some ((l, r) :: [])
	| (Convert (SubGen (_, _, l1), l2), Convert (SubGen (_, _, r1), r2)) -> 
		Some (
			(Abs (
				ref "x",
				Small,
				Convert (
					App (lift1 l1, Var 0),
					App (lift1 l2, Var 0)
				)
			),
			Abs (
				ref "x",
				Small,
				Convert (
					App (lift1 r1, Var 0),
					App (lift1 r2, Var 0)
				)
			)) :: []
		)	
	| (Convert (l1, l2), Convert (r1, r2)) -> (
		let l1' = reduction_step l1 
		and r1' = reduction_step r1 in
		if eq_terms l1 l1' then (
			if eq_terms r1 r1' then Some ((l1, r1) :: (l2, r2) :: [])
			else Some ((Convert (l1, l2), Convert (r1', r2)) :: [])
		)
		else Some ((Convert (l1', l2), Convert (r1, r2)) :: [])
	)
	| (Extract (_, _, _, l1, Membership (_, _, l2, l3)), Extract (_, _, _, r1, Membership (_, _, r2, r3))) -> Some ((App (App (l1, l3), l2), App (App (r1, r3), r2)) :: [])
	| (Extract (l1, l2, l3, l4, l5), Extract (r1, r2, r3, r4, r5)) -> (
		let l5' = reduction_step l5
		and r5' = reduction_step r5 in
		if eq_terms l5 l5' then (
			if eq_terms r5 r5' then Some ((l1, r1) :: (l2, r2) :: (l3, r3) :: (l4, r4) :: (l5, r5) :: [])
			else Some ((Extract (l1, l2, l3, l4, l5), Extract (r1, r2, r3, r4, r5')) :: [])
		)
		else Some ((Extract (l1, l2, l3, l4, l5'), Extract (r1, r2, r3, r4, r5)) :: [])
		
	)
	| (SubTrans (l1, l2), SubTrans (r1, r2)) -> Some ((l1, r1) :: (l2, r2) :: [])
	| (SubSub (l1, l2, l3, l4), SubSub (r1, r2, r3, r4)) -> Some ((l1, r1) :: (l2, r2) :: (l3, r3) :: (l4, r4) :: [])
	| (SubRefl l, SubRefl r) -> Some ((l, r) :: [])
	| (SubProd (l1, l2, l3, l4, l5, l6), SubProd (r1, r2, r3, r4, r5, r6)) -> Some ((l1, r1) :: (l2, r2) :: (l3, r3) :: (l4, r4) :: (l5, r5) :: (l6, r6) :: [])
	| (SubUnrefine, SubUnrefine) -> Some []
	| (SubGen (l1, l2, l3), SubGen (r1, r2, r3)) -> Some ((l1, r1) :: (l2, r2) :: (l3, r3) :: [])
	| (l, App (x, y)) -> (
		let app' = reduction_step (App (x, y)) in
		if eq_terms (App (x, y)) app' then None
		else Some ((l, app') :: [])
	)
	| (App (x, y), r) -> (
		let app' = reduction_step (App (x, y)) in
		if eq_terms (App (x, y)) app' then None
		else Some ((app', r) :: [])
	)
	| _ -> None

let rec unify u = 
	match u with
	| [] -> true
	| h :: t -> 
		match solve_eqn h with
		| Some t' -> unify (t' @ t)
		| None -> false

let similar_term l r = unify [(l, r)]