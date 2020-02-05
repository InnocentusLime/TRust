Require Export Arith.
Require Export Compare_dec.
Require Export Relations.
Require Export MyList.

(*
    Here we define TRust's terms. They are used by our
    veification proecedure.
*)

Section Termes.

  Inductive sort : Set :=
  | set : sort
  | prop : sort
  .

  Inductive term : Set :=
  | Srt : sort -> term
  | U8 : term
  | Fn : list term -> term -> term
  | NumConst : nat -> term
  | Add : term -> term -> term
  | Sub : term -> term -> term
  | Ref : nat -> term 
  | Func : list term -> term -> term -> term
  | Rec : term -> term
  | Call : term -> list term -> term
  .

  Inductive item : Set :=
  | FnDef : term -> item
  .

  (* The lifting of terms. *)
  Fixpoint lift_rec n t {struct t} : nat -> term :=
    fun k =>
    match t with
    | Srt s => Srt s
    | U8 => U8
    | Fn args range => (
      Fn
      (
        (
          fix lift_rec_args n (l : list term) {struct l} : nat -> list term :=
          fun k =>
          match l with
          | nil => nil
          | h :: t => (lift_rec n h k) :: (lift_rec_args n t (S k))
          end
        ) n args k
      )
      (lift_rec n range (length args + k))
    )
    | NumConst x => NumConst x
    | Add l r => Add (lift_rec n l k) (lift_rec n r k)
    | Sub l r => Sub (lift_rec n l k) (lift_rec n r k)
    | Ref i =>
        match le_gt_dec k i with
        | left _ => Ref (n + i)
        | right _ => Ref i
        end
    | Func args ret range => (
      Func
      (
        (
          fix lift_rec_args n (l : list term) {struct l} : nat -> list term :=
          fun k =>
          match l with
          | nil => nil
          | h :: t => (lift_rec n h k) :: (lift_rec_args n t (S k))
          end
        ) n args k
      )
      (lift_rec n ret (length args + k))
      (lift_rec n range (length args + k))
    )
    | Rec recursor => Rec (lift_rec n recursor (S k))
    | Call callee args => (
      Call
      (lift_rec n callee k)
      (
        (
          fix lift_rec_args n (l : list term) {struct l} : nat -> list term :=
          fun k =>
          match l with
          | nil => nil
          | h :: t => (lift_rec n h k) :: (lift_rec_args n t k)
          end
        ) n args k
      )
    )
    end
  .

  (* Shortcut *)
  Definition lift n t := lift_rec n t 0.

  (* 
    Substitution.
  *)
  Fixpoint subst_rec N M {struct M} : nat -> term :=
    fun k =>
    match M with
    | Srt s => Srt s
    | U8 => U8
    | Fn args range => (
      Fn
      (
        (
          fix subst_rec_args N (l : list term) {struct l} : nat -> list term :=
          fun k =>
          match l with
          | nil => nil
          | h :: t => (subst_rec N h k) :: (subst_rec_args N t (S k))
          end
        ) N args k
      )
      (subst_rec N range (length args + k))
    )
    | NumConst x => NumConst x
    | Add l r => Add (subst_rec N l k) (subst_rec N r k)
    | Sub l r => Sub (subst_rec N l k) (subst_rec N r k)
    | Ref i =>
        match lt_eq_lt_dec k i with
        | inleft C =>
            match C with
            | left _ => Ref (pred i)
            | right _ => lift k N
            end
        | inright _ => Ref i
        end
    | Func args ret range => (
      Func
      (
        (
          fix subst_rec_args N (l : list term) {struct l} : nat -> list term :=
          fun k =>
          match l with
          | nil => nil
          | h :: t => (subst_rec N h k) :: (subst_rec_args N t (S k))
          end
        ) N args k
      )
      (subst_rec N ret (length args + k))
      (subst_rec N range (length args + k))
    )
    | Rec recursor => Rec (subst_rec N recursor (S k))
    | Call callee args => (
      Call
      (subst_rec N callee k)
      (
        (
          fix subst_rec_args N (l : list term) {struct l} : nat -> list term :=
          fun k =>
          match l with
          | nil => nil
          | h :: t => (subst_rec N h k) :: (subst_rec_args N t k)
          end
        ) N args k
      )
    )
    end
  .

  (* Shortuct *)
  Definition subst N M := subst_rec N M 0.

  (* For list subst *)
  Fixpoint subst_list l {struct l} : term -> term :=
    fun M =>
    match l with
    | nil => M
    | h :: t => subst_list t (subst h M)
    end
  .
End Termes.

Section Beta_Reduction.

  Inductive
  .

  (* One-step reduction *)
  Inductive red1 : term -> term -> Prop :=
  | fn_arg_red : 
    forall range arg arg' l r,
    red1 arg arg' ->
    red1 (Fn (l ++ arg :: r) range) (Fn (l ++ arg' :: r) range)
  | add_l_red :
    forall l l' r,
    red1 l l' ->
    red1 (Add l r) (Add l' r)
  | add_r_red :
    forall l r r',
    red1 r r' ->
    red1 (Add l r) (Add l r')
  | red_add :
    forall n m,
    red1 (Add (NumConst n) (NumConst m)) (NumConst (n + m))
  | sub_l_red :
    forall l l' r,
    red1 l l' ->
    red1 (Sub l r) (Sub l' r)
  | sub_r_red :
    forall l r r',
    red1 r r' ->
    red1 (Sub l r) (Sub l r')
  | red_sub :
    forall n m,
    red1 (Sub (NumConst n) (NumConst m)) (NumConst (n - m))
  | func_arg_red :
    forall arg arg' l r body ret,
    red1 arg arg' ->
    red1 (Func (l ++ arg :: r) ret body) (Func (l ++ arg' :: r) ret body)
  | func_ret_red : 
    forall args ret ret' body,
    red1 ret ret' ->
    red1 (Func args ret body) (Func args ret' body)
  | func_body_red : 
    forall args ret body body',
    red1 body body' ->
    red1 (Func args ret body) (Func args ret body')
  | func_call :
    forall args ret body app_args,
    red1 (Call (Func args ret body) app_args) (subst_list app_args body)
  | rec_red_body :
    forall body body',
    red1 (Rec body) (Rec body')
  | red_rec :
    forall body,
    red1 (Rec body) (subst (Rec body) body)
  | call_red_callee :
    forall callee callee' args,
    red1 (Call callee args) (Call callee' args)
  | call_red_args :
    forall callee arg arg' l r,
    red1 arg arg' ->
    red1 (Call callee (l ++ arg :: r)) (Call callee (l ++ arg' :: r))
  .

  (* The `non-strict` multistep reduction *)
  Inductive red M : term -> Prop :=
  | refl_red : red M M
  | trans_red : forall (P : term) N, red M P -> red1 P N -> red M N
  .

  (* The convertibility relation *)
  Inductive conv M : term -> Prop :=
  | refl_conv : conv M M
  | trans_conv_red : forall (P : term) N, conv M P -> red1 P N -> conv M N
  | trans_conv_exp : forall (P : term) N, conv M P -> red1 N P -> conv M N
  .

  (* parallel one-step reduction *)
  Inductive par_red1 : term -> term -> Prop :=
  | sort_par_red : forall s, par_red1 (Srt s) (Srt s)
  | u8_par_red : par_red1 U8 U8
  | fn_par_red :
    forall args args',
    par_red1_list args args' ->
    forall range range',
    par_red1 range range' ->
    par_red1 (Fn args range) (Fn args' range')
  | num_const_par_red :
    forall n n',
    par_red1 (NumConst n) (NumConst n')
  | add_par_red_args :
    forall l l',
    par_red1 l l' ->
    forall r r',
    par_red1 r r' ->
    par_red1 (Add l r) (Add l' r')
  | add_par_red_exec :
    forall n m,
    par_red1 (Add (NumConst n) (NumConst m)) (NumConst (n + m))
  | sub_par_red_args :
    forall l l',
    par_red1 l l' ->
    forall r r',
    par_red1 r r' ->
    par_red1 (Sub l r) (Sub l' r')
  | sub_par_red_exec :
    forall n m,
    par_red1 (Sub (NumConst n) (NumConst m)) (NumConst (n - m))
  | ref_par_red :
    forall n,
    par_red1 (Ref n) (Ref n)
  | func_par_red :
    forall args args',
    par_red1_list args args' ->
    forall range range',
    par_red1 range range' ->
    forall body body',
    par_red1 body body' ->
    par_red1 (Func args range body) (Func args' range' body')
  | func_call_red :
    forall body body',
    par_red1 body body' ->
    forall call_args call_args',
    par_red1_list call_args call_args' ->
    forall args range, par_red1 (Call (Func args range body) call_args) (subst_list call_args' body')
  | rec_par_red :
    forall body body',
    par_red1 body body' ->
    par_red1 (Rec body) (Rec body')
  | rec_par_red_expand :
    forall body body',
    par_red1 body body' ->
    par_red1 (Rec body) (subst (Rec body') body')
  | call_par_red :
    forall callee callee',
    par_red1 callee callee' ->
    forall args args',
    par_red1_list args args' ->
    par_red1 (Call callee args) (Call callee' args')
  with par_red1_list : list term -> list term -> Prop :=
  | list_nil_par_red : par_red1_list nil nil
  | list_cons_par_red : 
    forall hl l hr r,
    par_red1 hl hr ->
    par_red1_list l r ->
    par_red1_list (hl :: l) (hr :: r)
  .

  (* Induction scheme when the simple induction won't do the trick *)
  Scheme par_red1_mut := Induction for 
  par_red1 Sort Prop
  with par_red1_list_mut := Induction for 
  par_red1_list Sort Prop.

  (* Multistep parallel reduction *)
  Definition par_red := clos_trans term par_red1.

End Beta_Reduction.

Section Normalisation_Forte.

  (* Irreducable term *)
  Definition normal t : Prop := forall u, ~ red1 t u.

  (* 
    Strongly normalizing term. 
    It's a term which is accassible with 
    transitively closed one-step reduction 
  *)
  Definition sn : term -> Prop := Acc (transp _ red1).

End Normalisation_Forte.