(*
	The basic facilities for dealing with
	the intermidiate representation of Rust programs.
	The repr is using De Brujin indices
*)

let (>>=) m f = 
	match m with
	| Some x -> f x
	| None -> None
;;

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
| TVar of int
| Refine of string * type_ast * prop_ast (* the type in the `refine` can't depende on introduced var *)
| Map of string * type_ast * type_ast
| Prod of type_ast list
| Gen of string * type_ast
and term_ast =
| True
| False
| Nil
| NatO
| NatSucc
| Var of int
| Abs of string * type_ast * term_ast
| Generic of string * term_ast
| App of term_ast * term_ast
| TApp of term_ast * type_ast
| Tuple of term_ast list
| Proj of term_ast * int
| Ite of term_ast * term_ast * term_ast * prop_ast
| For of term_ast * term_ast * term_ast * prop_ast  
;;

let rec eq_props l r =
    match (l, r) with
	| (Top, Top) -> true
	| (Bot, Bot) -> true
	| (Forall (_, lt, lp), Forall (_, rt, rp)) -> eq_types lt rt && eq_props lp rp
	| (ForallGen (_, lp), ForallGen (_, rp)) -> eq_props lp rp
	| (Exists (_, lt, lp), Exists (_, rt, rp)) -> eq_types lt rt && eq_props lp rp
	| (Eq (lx, ly, lt), Eq (rx, ry, rt)) -> eq_terms lx rx && eq_terms ly ry && eq_types lt rt
	| (Conjunction (lx, ly), Conjunction (rx, ry)) -> eq_props lx rx && eq_props ly ry
	| (Disjunction (lx, ly), Disjunction (rx, ry)) -> eq_props lx rx && eq_props ly ry
	| (Implication (lx, ly), Implication (rx, ry)) -> eq_props lx rx && eq_props ly ry	
	| _ -> false
and eq_types l r =
	let rec eq_prods l r =
		match (l, r) with
		| ([], []) -> true
		| (lh :: lt, rh :: rt) -> eq_types lh rh && eq_prods lt rt
		| _ -> false
	in
	match (l, r) with
	| (Unit, Unit) -> true
	| (Nat, Nat) -> true
	| (Bool, Bool) -> true
	| (TVar x, TVar y) -> x = y
	| (Refine (_, tx, px), Refine (_, ty, py)) -> eq_types tx ty && eq_props px py
	| (Map (_, lx, rx), Map (_, ly, ry)) -> eq_types lx ly && eq_types rx ry
	| (Prod l, Prod r) -> eq_prods l r
	| (Gen (_, l), Gen (_, r)) -> eq_types l r
	| _ -> false
and eq_terms l r =
	let rec eq_tuples l r =
		match (l, r) with
		| ([], []) -> true
		| (lh :: lt, rh :: rt) -> eq_terms lh rh && eq_tuples lt rt 
		| _ -> false
	in
	match (l, r) with
	| (True, True) -> true
	| (False, False) -> true
	| (Nil, Nil) -> true
	| (NatO, NatO) -> true
	| (NatSucc, NatSucc) -> true
	| (Var x, Var y) -> x = y
	| (Abs (_, lt, lbody), Abs (_, rt, rbody)) -> eq_types lt rt && eq_terms lbody rbody
	| (Generic (_, lbody), Generic (_, rbody)) -> eq_terms lbody rbody
	| (App (lx, ly), App (rx, ry)) -> eq_terms lx rx && eq_terms ly ry
	| (TApp (lx, ly), TApp (rx, ry)) -> eq_terms lx rx && eq_types ly ry
	| (Tuple l, Tuple r) -> eq_tuples l r
	| (Proj (lx, li), Proj (rx, ri)) -> eq_terms lx rx && li = ri
	| (Ite (la, lb, lc, ld), Ite (ra, rb, rc, rd)) -> eq_terms la ra && eq_terms lb rb && eq_terms lc rc && eq_props ld rd
	| (For (la, lb, lc, ld), For (ra, rb, rc, rd)) -> eq_terms la ra && eq_terms lb rb && eq_terms lc rc && eq_props ld rd
	| _ -> false
;;

(*t |^d_c*)
let rec lift_prop t c d =
	match t with
	| Top -> Top
	| Bot -> Bot
	| Forall (str, typ, prp) -> Forall (str, lift_type typ c d, lift_prop prp (c + 1) d)
	| ForallGen (str, prp) -> ForallGen (str, lift_prop prp (c + 1) d)
	| Exists (str, typ, prp) -> Exists (str, lift_type typ c d, lift_prop prp (c + 1) d)
	| Eq (l, r, typ) -> Eq (lift_term l c d, lift_term r c d, lift_type typ c d)
	| Conjunction (l, r) -> Conjunction (lift_prop l c d, lift_prop r c d)
	| Disjunction (l, r) -> Disjunction (lift_prop l c d, lift_prop r c d)
	| Implication (l, r) -> Implication (lift_prop l c d, lift_prop r c d)
and lift_type t c d =
	match t with
	| Unit -> Unit
	| Nat -> Nat
	| Bool -> Bool
	| TVar x -> if x < c then TVar x else TVar (x + d)
	| Refine (v, typ, prp) -> Refine (v, lift_type typ (c + 1) d, lift_prop prp (c + 1) d)
	| Map (v, l, r) -> Map (v, lift_type l c d, lift_type r (c + 1) d)
	| Prod l -> Prod (List.map (fun x -> lift_type x c d) l)
	| Gen (v, sub) -> Gen (v, lift_type sub (c + 1) d)
and lift_term t c d =
	match t with
	| True -> True
	| False -> False
	| Nil -> Nil
	| NatO -> NatO
	| NatSucc -> NatSucc
	| Var x -> if x < c then Var x else Var (x + d)
	| Abs (str, typ, body) -> Abs (str, lift_type typ c d, lift_term body (c + 1) d)
	| Generic (str, body) -> Generic (str, lift_term body (c + 1) d)
	| App (l, r) -> App (lift_term l c d, lift_term r c d)
	| TApp (l, r) -> TApp (lift_term l c d, lift_type r c d)
	| Tuple l -> Tuple (List.map (fun x -> lift_term x c d) l)
	| Proj (x, id) -> Proj (lift_term x c d, id)
	| Ite (cond, on_true, on_false, prp) -> Ite (lift_term cond c d, lift_term on_true c d, lift_term on_false c d, lift_prop prp c d)
	| For (head, step, terminator, prp) -> For (lift_term head c d, lift_term step c d, lift_term terminator c d, lift_prop prp c d)
;;

type subst_data =
| SubstData of term_ast
| SubstType of type_ast
;;

let lift_subst_data t =
	match t with
	| SubstData t -> SubstData (lift_term t 0 1)
	| SubstType t -> SubstType (lift_type t 0 1)
;;

let clean_after_unbind_term t = lift_term t 0 (-1);;
let clean_after_unbind_type t = lift_type t 0 (-1);;
let clean_after_unbind_prop p = lift_prop p 0 (-1);;

(*t[v:=x]*)
let rec subst_prop t v x =
	match t with
	| Top -> Top
	| Bot -> Bot
	| Forall (str, typ, prp) -> Forall (str, subst_type typ v x, subst_prop prp (v + 1) (lift_subst_data x))
	| ForallGen (str, prp) -> ForallGen (str, subst_prop prp (v + 1) (lift_subst_data x))
	| Exists (str, typ, prp) -> Exists (str, subst_type typ v x, subst_prop prp (v + 1) (lift_subst_data x))
	| Eq (l, r, typ) -> Eq (subst_term l v x, subst_term r v x, subst_type typ v x)
	| Conjunction (l, r) -> Conjunction (subst_prop l v x, subst_prop r v x)
	| Disjunction (l, r) -> Disjunction (subst_prop l v x, subst_prop r v x)
	| Implication (l, r) -> Implication (subst_prop l v x, subst_prop r v x)
and subst_type t v x =
	match t with
	| Unit -> Unit
	| Nat -> Nat
	| Bool -> Bool
	| TVar v' -> (
		if v' = v then (
			match x with
			| SubstData _ -> failwith "bad substitution (tried to put data instead of type)"
			| SubstType x -> x
		) else TVar v'
	)
	| Refine (str, typ, prp) -> Refine (str, subst_type typ v x, subst_prop prp (v + 1) (lift_subst_data x))
	| Map (str, l, r) -> Map (str, subst_type l v x, subst_type r (v + 1) (lift_subst_data x))
	| Prod l -> Prod (List.map (fun t -> subst_type t v x) l)
	| Gen (str, sub) -> Gen (str, subst_type sub (v + 1) (lift_subst_data x))	 
and subst_term t v x =
	match t with
	| True -> True
	| False -> False
	| Nil -> Nil
	| NatO -> NatO
	| NatSucc -> NatSucc
	| Var v' -> (
		if v' = v then (
			match x with
			| SubstData x -> x 
			| SubstType _ -> failwith "bad substitution (tried to put a type instead of data)"
		) else Var v'
	)
	| Abs (str, typ, body) -> Abs (str, subst_type typ v x, subst_term body (v + 1) (lift_subst_data x))
	| Generic (str, body) -> Generic (str, subst_term body (v + 1) (lift_subst_data x))
	| App (l, r) -> App (subst_term l v x, subst_term r v x)
	| TApp (l, r) -> TApp (subst_term l v x, subst_type r v x)
	| Tuple l -> Tuple (List.map (fun l -> subst_term l v x) l)
	| Proj (l, id) -> Proj (subst_term l v x, id)
	| Ite (cond, on_true, on_false, prp) -> Ite (subst_term cond v x, subst_term on_true v x, subst_term on_false v x, subst_prop prp v x)
	| For (head, step, terminator, prp) -> For (subst_term head v x, subst_term step v x, subst_term terminator v x, subst_prop prp v x) 
;;

let top_subst_prop target subst_value = clean_after_unbind_prop (subst_prop target 0 (lift_subst_data subst_value));;
let top_subst_type target subst_value = clean_after_unbind_type (subst_type target 0 (lift_subst_data subst_value));;
let top_subst_term target subst_value = clean_after_unbind_term (subst_term target 0 (lift_subst_data subst_value));;

let rec reduction_step t =
	let rec tuple_reduction l =
		match l with
		| [] -> []
		| h :: t -> 
			let h' = reduction_step h in 
			if h = h' then h :: tuple_reduction t else h' :: t	
	in
	match t with
	| True -> True
	| False -> False
	| Nil -> Nil
	| NatO -> NatO
	| NatSucc -> NatSucc
	| Var v -> Var v
	| Abs (v, typ, body) -> Abs (v, typ, body)
	| Generic (v, body) -> Generic (v, body)
	| App (Abs (_, t, body), r) -> top_subst_term body (SubstData r)
	| App (l, r) -> (
		let l' = reduction_step l in
		if l = l' then App (l, reduction_step r)
		else App (l', r)
	)
	| TApp (Generic (_, body), r) -> top_subst_term body (SubstType r)
	| TApp (l, r) -> TApp (reduction_step l, r)	
	| Tuple l -> Tuple (tuple_reduction l)
	| Proj (Tuple l, id) -> List.nth l id
	| Proj (l, id) -> Proj (reduction_step l, id)
	| Ite (True, on_true, _, _) -> on_true
	| Ite (False, _, on_false, _) -> on_false
	| Ite (cond, on_true, on_false, inv) -> Ite (reduction_step cond, on_true, on_false, inv)
	| For (NatO, _, terminator, _) -> terminator
	| For (App (NatSucc, n), step, terminator, inv) -> App (step, For (n, step, terminator, inv))
	| For (n, step, terminator, inv) -> For (reduction_step n, step, terminator, inv)
;;

type var_val =
| Data of type_ast
| Type
;;

type context = {
	mem : (var_val * string) array;
};;

let create_empty_context () = { mem = Array.make 0 (Type, "I AM A CAT"); };;

let lift_ctx_data x =
	match x with
	| (Data x, v) -> (Data (lift_type x 0 1), v)
	| _ -> x
;;
let lift_context ctx = { mem = Array.map lift_ctx_data ctx.mem };;

(* fetch_var : context -> int -> type_ast option *)
let fetch_var ctx v =
	if (0 <= v) && (v < Array.length ctx.mem) then Some (fst (Array.get ctx.mem v))
	else None
;;           

let push_var v t ctx = { mem = Array.init (Array.length ctx.mem + 1) (fun x -> if x = 0 then (t, v) else Array.get ctx.mem (x - 1)) } |> lift_context;;

let rec erase_exterior_refines typ =
	match typ with
	| Unit -> Unit
	| Nat -> Nat
	| Bool -> Bool
	| TVar x -> TVar x
	| Refine (_, t, _) -> erase_exterior_refines (clean_after_unbind_type t)
	| Map (v, s, t) -> Map (v, s, t)
	| Prod l -> Prod l
	| Gen (v, t) -> Gen (v, t)
;;

(*erase `all` refines*)
let rec erase_refines typ =
	match typ with
	| Unit -> Unit
	| Nat -> Nat
	| Bool -> Bool
	| TVar x -> TVar x
	| Refine (_, t, _) -> erase_refines (clean_after_unbind_type t)
	| Map (_, s, t) -> Map ("_", erase_refines s, erase_refines t)
	| Prod l -> Prod (List.map erase_refines l)
	| Gen (v, t) -> Gen (v, erase_refines t)
;;

(*checks if `s =t t`*)
let rec are_types_from_same_family s t = (erase_refines s = erase_refines t);;

(*check if the type is a small one*)
let rec is_type_small t =
	match t with
	| Unit -> true
	| Nat -> true
	| Bool -> true
	| TVar _ -> true (*assumption: vars are small*)
	| Refine (_, t, _) -> is_type_small t
	| Map (_, s, t) -> is_type_small s && is_type_small t
	| Prod l -> List.fold_left (fun acc x -> acc && is_type_small x) true l
	| Gen _ -> false
;;

let cons_opt h t = h >>= fun h -> (t >>= fun t -> Some (h :: t));;

(*a typecheck without any verification; the context may become corrupted, don't use it after calling the function*)
let rec simply_typed_typecheck' term ctx =
	match term with
	| True -> Some Bool
	| False -> Some Bool
	| Nil -> Some Unit
	| NatO -> Some Nat
	| NatSucc -> Some (Map ("_", Nat, Nat))
	| Var v -> let t = fetch_var ctx v in 
	(
		match t with
		| Some (Data x) when is_type_small x -> Some x
		| _ -> None
	)
	| Abs (v, arg_t, body) -> 
		(*we also have to lift the context *)
		if is_type_small arg_t then ctx |> push_var v (Data arg_t) |> simply_typed_typecheck' body >>= fun t -> Some (Map ("_", arg_t, t))
		else None
	| Generic (v, body) -> ctx |> push_var v Type |> simply_typed_typecheck' body >>= fun t -> Some (Gen (v, t))
	| App (l, r) -> ctx |> simply_typed_typecheck' l >>= fun lt -> ctx |> simply_typed_typecheck' r >>= (fun rt ->
		match lt with
		| Map (_, x, y) when eq_types x rt && is_type_small rt -> Some (top_subst_type y (SubstData r))
		| _ -> None
	) 
	| TApp (gen, typ) -> ctx |> simply_typed_typecheck' gen >>= (fun t ->
		match t with
		| Gen (_, t_bod) when is_type_small typ -> Some (top_subst_type t_bod (SubstType typ))
		| _ -> None
	)
	| Tuple l -> List.fold_right (fun x acc -> cons_opt x acc) (List.map (fun x -> simply_typed_typecheck' x ctx) l) (Some []) >>= (fun x -> Some (Prod x))
	| Proj (t, i) -> ctx |> simply_typed_typecheck' t >>= (fun x ->
		match x with
		| Prod l -> Some (List.nth l i)
		| _ -> None
	) 
	| Ite (cond, on_true, on_false, _) -> (
		match (simply_typed_typecheck' cond ctx, simply_typed_typecheck' on_true ctx, simply_typed_typecheck' on_false ctx) with
		| (Some t_cond, Some t_ontrue, Some t_onfalse) -> if eq_types t_cond Bool && eq_types t_ontrue t_onfalse then Some t_ontrue else None
		| _ -> None
	)
	| For (head, step, terminate, _) -> (
		match (simply_typed_typecheck' head ctx, simply_typed_typecheck' step ctx, simply_typed_typecheck' terminate ctx) with
		| (Some t_head, Some t_step, Some t_terminate) -> if eq_types t_head Nat && eq_types t_step (Map ("_", t_terminate, t_terminate)) then Some t_terminate else None
		| _ -> None
	)
;;

let rec simply_typed_typecheck_preprocess term =
	match term with
	| True -> True
	| False -> False
	| Nil -> Nil
	| NatO -> NatO
	| NatSucc -> NatSucc
	| Var v -> Var v
	| Abs (v, arg_t, body) -> Abs (v, erase_refines arg_t, simply_typed_typecheck_preprocess body)
	| Generic (v, body) -> Generic (v, simply_typed_typecheck_preprocess body)
	| App (l, r) -> App (simply_typed_typecheck_preprocess l, simply_typed_typecheck_preprocess r)
	| TApp (l, r) -> TApp (simply_typed_typecheck_preprocess l, erase_refines r)
	| Tuple l -> Tuple (List.map simply_typed_typecheck_preprocess l)
	| Proj (x, i) -> Proj (simply_typed_typecheck_preprocess x, i)
	| Ite (a, b, c, d) -> Ite (simply_typed_typecheck_preprocess a, simply_typed_typecheck_preprocess b, simply_typed_typecheck_preprocess c, d)
	| For (a, b, c, d) -> For (simply_typed_typecheck_preprocess a, simply_typed_typecheck_preprocess b, simply_typed_typecheck_preprocess c, d)
;;

(* the really basic type inference without any tricks *)
let rec basic_type_check ctx term = ();;                                   

let simply_typed_typecheck t = (
	match simply_typed_typecheck' (simply_typed_typecheck_preprocess t) (create_empty_context ()) with
	| Some t -> Some t
	| None -> None
);;                                    

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
        
