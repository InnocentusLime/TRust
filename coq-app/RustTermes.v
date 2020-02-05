Require Export Arith.
Require Export Compare_dec.
Require Export Relations.
Require Export MyList.

(*
    Here we define rust terms without any aim at verification
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
  (* | Unrechable : term *)
  .

  Definition term_list_mut_ind :=
  fun
  (P : term -> Prop)
  (H : forall s, P (Srt s))
  (H0 : P U8)
  (H1 : forall args range, Forall P args -> P range -> P (Fn args range))
  (H2 : forall n, P (NumConst n))
  (H3 : forall l r, P l -> P r -> P (Add l r))
  (H4 : forall l r, P l -> P r -> P (Sub l r))
  (H5 : forall n, P (Ref n))
  (H6 : forall args range body, Forall P args -> P range -> P body -> P (Func args range body))
  (H7 : forall body, P body -> P (Rec body))
  (H8 : forall callee args, P callee -> Forall P args -> P (Call callee args)) =>
  fix F (M : term) {struct M} : P M :=
    match M as M0 return (P M0) with
    | Srt s => H s
    | U8 => H0
    | Fn args range => (
      H1 args range
      (
        (
          fix G (L : list term) {struct L} : Forall P L :=
            match L as L0 return (Forall P L0) with
            | nil => Forall_nil P
            | h :: t => Forall_cons h (F h) (G t)
            end
        ) args
      ) (F range)
    )
    | NumConst n => H2 n
    | Add l r => H3 l r (F l) (F r)
    | Sub l r => H4 l r (F l) (F r)
    | Ref n => H5 n
    | Func args range body => (
      H6 args range body
      (
        (
          fix G (L : list term) {struct L} : Forall P L :=
            match L as L0 return (Forall P L0) with
            | nil => Forall_nil P
            | h :: t => Forall_cons h (F h) (G t)
            end
        ) args
      ) (F range) (F body)
    )
    | Rec x => H7 x (F x)
    | Call callee args => (
      H8 callee args
      (F callee)
      (
        (
          fix G (L : list term) {struct L} : Forall P L :=
            match L as L0 return (Forall P L0) with
            | nil => Forall_nil P
            | h :: t => Forall_cons h (F h) (G t)
            end
        ) args
      )
    )
    end
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
    forall n,
    par_red1 (NumConst n) (NumConst n)
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

Hint Resolve fn_arg_red add_l_red add_r_red red_add sub_l_red sub_r_red 
  red_sub func_arg_red func_ret_red func_call rec_red_body red_rec call_red_callee 
  call_red_args : rust.
Hint Resolve refl_red refl_conv: rust.
Hint Resolve sort_par_red u8_par_red fn_par_red num_const_par_red  
  add_par_red_args add_par_red_exec sub_par_red_args sub_par_red_exec
  ref_par_red func_par_red func_call_red rec_par_red rec_par_red_expand 
  call_par_red list_nil_par_red list_cons_par_red : rust.
Hint Unfold par_red: rust.

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

Hint Unfold sn: coc.
 
(*
ALGEBRAIC LIFT AND SUBST LEMMAS
===================================================================================
*)

Lemma lift_ref_ge :
  forall k n p, p <= n -> lift_rec k (Ref n) p = Ref (k + n).
Proof.
  intros; simpl in |- *.
  elim (le_gt_dec p n); auto with rust core arith sets.
  intro; absurd (p <= n); auto with rust core arith sets.
Qed.


Lemma lift_ref_lt : forall k n p, p > n -> lift_rec k (Ref n) p = Ref n.
Proof.
  intros; simpl in |- *.
  elim (le_gt_dec p n); auto with rust core arith sets.
  intro; absurd (p <= n); auto with rust core arith sets.
Qed.


Lemma subst_ref_lt : forall u n k, k > n -> subst_rec u (Ref n) k = Ref n.
Proof.
  simpl in |- *; intros.
  elim (lt_eq_lt_dec k n); [ intro a | intro b; auto with rust core arith sets ].
  elim a; clear a; [ intro a | intro b ].
  absurd (k <= n); auto with rust core arith sets.

  inversion_clear b in H.
  elim gt_irrefl with n; auto with rust core arith sets.
Qed.


Lemma subst_ref_gt : forall u n k, n > k -> subst_rec u (Ref n) k = Ref (pred n).
Proof.
  simpl in |- *; intros.
  elim (lt_eq_lt_dec k n); [ intro a | intro b ].
  elim a; clear a; [ intro a; auto with rust core arith sets | intro b ].
  inversion_clear b in H.
  elim gt_irrefl with n; auto with rust core arith sets.

  absurd (k <= n); auto with rust core arith sets.
Qed.


Lemma subst_ref_eq : forall u n, subst_rec u (Ref n) n = lift n u.
Proof.
  intros; simpl in |- *.
  elim (lt_eq_lt_dec n n); [ intro a | intro b ].
  elim a; intros; auto with rust core arith sets.
  elim lt_irrefl with n; auto with rust core arith sets.

  elim gt_irrefl with n; auto with rust core arith sets.
Qed.



Lemma lift_rec0 : forall M k, lift_rec 0 M k = M.
Proof.
  induction M using term_list_mut_ind; simpl in |- *; intros; auto with core sets arith.

  rewrite IHM; f_equal.
  generalize k; clear k.
  induction args; intros; auto with core sets.
  inversion_clear H.
  rewrite IHargs; auto with core sets.
  rewrite H0; auto with core sets.

  rewrite IHM1; rewrite IHM2; auto with core sets.

  rewrite IHM1; rewrite IHM2; auto with core sets.

  destruct (le_gt_dec k n); auto with core sets.

  rewrite IHM1; rewrite IHM2; f_equal.
  generalize k; clear k.
  induction args; intros; auto with core sets.
  inversion_clear H.
  rewrite IHargs; auto with core sets.
  rewrite H0; auto with core sets.

  rewrite IHM; auto with core sets.

  rewrite IHM; f_equal.
  generalize k; clear k.
  induction args; intros; auto with core sets.
  inversion_clear H.
  rewrite IHargs; auto with core sets.
  rewrite H0; auto with core sets.
Qed.

Lemma lift0 : forall M, lift 0 M = M.
Proof.
  intros; unfold lift in |- *.
  apply lift_rec0; auto with rust core arith sets.
Qed.

Lemma simpl_lift_rec :
  forall M n k p i,
  i <= k + n ->
  k <= i -> lift_rec p (lift_rec n M k) i = lift_rec (p + n) M k
.
Proof.
  induction M using term_list_mut_ind; simpl in |- *; intros; auto with core sets arith.

  rewrite IHM; auto with core arith sets.
  f_equal.
  generalize k i H0 H1; clear H1 H0 k i.
  induction args; intros; auto with core sets.
  inversion_clear H.
  rewrite IHargs; auto with core sets arith.
  rewrite H2; auto with core arith sets.
  simpl in |- *; auto with arith.
  cut (forall X Y, X = Y -> X + i <= Y + k + n); intros.
  apply H2.
  clear H; clear IHM.
  generalize k.
  induction args; intros; auto with core sets arith.
  simpl in |- *; rewrite IHargs; auto with core sets arith.
  subst Y; rewrite <- Nat.add_assoc; auto with core arith sets.
  cut (forall X Y, X = Y -> X + k <= Y + i); intros.
  apply H2.
  clear H; clear IHM.
  generalize k.
  induction args; intros; auto with core sets arith.
  simpl in |- *; rewrite <- IHargs; auto with core sets arith.
  subst Y; auto with core arith sets.

  rewrite IHM1; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.

  rewrite IHM1; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.

  elim (le_gt_dec k n); intros.
  rewrite lift_ref_ge; auto with rust core arith sets.
  rewrite plus_comm; apply le_trans with (k + n0);
  auto with rust core arith sets.
  rewrite lift_ref_lt; auto with rust core arith sets.
  apply le_gt_trans with k; auto with rust core arith sets.

  rewrite IHM1; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.
  f_equal.
  generalize k i H0 H1; clear H1 H0 k i.
  induction args; intros; auto with core sets.
  inversion_clear H.
  rewrite IHargs; auto with core sets arith.
  rewrite H2; auto with core arith sets.
  simpl in |- *; auto with arith.
  cut (forall X Y, X = Y -> X + i <= Y + k + n); intros.
  apply H2.
  clear H; clear IHM1; clear IHM2.
  generalize k.
  induction args; intros; auto with core sets arith.
  simpl in |- *; rewrite IHargs; auto with core sets arith.
  subst Y; rewrite <- Nat.add_assoc; auto with core arith sets.
  cut (forall X Y, X = Y -> X + k <= Y + i); intros.
  apply H2.
  clear H; clear IHM1; clear IHM2.
  generalize k.
  induction args; intros; auto with core sets arith.
  simpl in |- *; rewrite <- IHargs; auto with core sets arith.
  subst Y; auto with core arith sets.
  cut (forall X Y, X = Y -> X + i <= Y + k + n); intros.
  apply H2.
  clear H; clear IHM1; clear IHM2.
  generalize k.
  induction args; intros; auto with core sets arith.
  simpl in |- *; rewrite IHargs; auto with core sets arith.
  subst Y; rewrite <- Nat.add_assoc; auto with core arith sets.
  cut (forall X Y, X = Y -> X + k <= Y + i); intros.
  apply H2.
  clear H; clear IHM1; clear IHM2.
  generalize k.
  induction args; intros; auto with core sets arith.
  simpl in |- *; rewrite <- IHargs; auto with core sets arith.
  subst Y; auto with core arith sets.

  rewrite IHM; simpl in |- *; auto with core sets arith.

  rewrite IHM; auto with core arith sets.
  f_equal.
  generalize k i H0 H1; clear H1 H0 k i.
  induction args; intros; auto with core sets.
  inversion_clear H.
  rewrite IHargs; auto with core sets arith.
  rewrite H2; auto with core arith sets.
Qed.

Lemma simpl_lift : forall M n, lift (S n) M = lift 1 (lift n M).
Proof.
  intros; unfold lift in |- *.
  rewrite simpl_lift_rec; auto with rust core arith sets.
Qed.

Lemma permute_lift_rec :
  forall M n k p i,
  i <= k ->
  lift_rec p (lift_rec n M k) i = lift_rec n (lift_rec p M i) (p + k)
.
Proof.
  induction M using term_list_mut_ind; simpl in |- *; intros; auto with core sets arith.

  f_equal.
  generalize i k H0; clear H0 k i; induction args; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H1; auto with core arith sets.
  rewrite plus_n_Sm.
  rewrite IHargs; auto with core arith sets.
  rewrite IHM; auto with core arith.
  f_equal.
  f_equal.
  apply Nat.add_cancel_r.
  clear H0 H; generalize k; clear k.
  induction args; simpl in |- *; intros; auto with core arith sets.
  rewrite Nat.add_assoc; rewrite (Nat.add_comm p (length args)); rewrite <- Nat.add_assoc.
  apply Nat.add_cancel_r.
  clear H0 H; generalize i; clear i.
  induction args; simpl in |- *; intros; auto with core arith sets.
  cut (forall X Y, X = Y -> X + i <= Y + k); intros.
  apply H1.
  clear H0 H H1; generalize k; clear k.
  induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; auto with core arith sets.

  rewrite IHM1; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.

  rewrite IHM1; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.

  elim (le_gt_dec k n); elim (le_gt_dec i n); intros.
  rewrite lift_ref_ge; auto with rust core arith sets.
  rewrite lift_ref_ge; auto with rust core arith sets.
  elim plus_assoc_reverse with p n0 n.
  elim plus_assoc_reverse with n0 p n.
  elim plus_comm with p n0; auto with rust core arith sets.
  apply le_trans with n; auto with rust core arith sets.
  absurd (i <= n); auto with rust core arith sets.
  apply le_trans with k; auto with rust core arith sets.
  rewrite lift_ref_ge; auto with rust core arith sets.
  rewrite lift_ref_lt; auto with rust core arith sets.
  rewrite lift_ref_lt; auto with rust core arith sets.
  rewrite lift_ref_lt; auto with rust core arith sets.
  apply le_gt_trans with k; auto with rust core arith sets.

  f_equal.
  generalize i k H0; clear H0 k i; induction args; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H1; auto with core arith sets.
  rewrite plus_n_Sm.
  rewrite IHargs; auto with core arith sets.

  rewrite IHM1; auto with core arith.
  f_equal.
  f_equal.
  apply Nat.add_cancel_r.
  clear H0 H; generalize k; clear k.
  induction args; simpl in |- *; intros; auto with core arith sets.
  rewrite Nat.add_assoc; rewrite (Nat.add_comm p (length args)); rewrite <- Nat.add_assoc.
  apply Nat.add_cancel_r.
  clear H0 H; generalize i; clear i.
  induction args; simpl in |- *; intros; auto with core arith sets.
  cut (forall X Y, X = Y -> X + i <= Y + k); intros.
  apply H1.
  clear H0 H H1; generalize k; clear k.
  induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; auto with core arith sets.

  rewrite IHM2; auto with core arith.
  f_equal.
  f_equal.
  apply Nat.add_cancel_r.
  clear H0 H; generalize k; clear k.
  induction args; simpl in |- *; intros; auto with core arith sets.
  rewrite Nat.add_assoc; rewrite (Nat.add_comm p (length args)); rewrite <- Nat.add_assoc.
  apply Nat.add_cancel_r.
  clear H0 H; generalize i; clear i.
  induction args; simpl in |- *; intros; auto with core arith sets.
  cut (forall X Y, X = Y -> X + i <= Y + k); intros.
  apply H1.
  clear H0 H H1; generalize k; clear k.
  induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; auto with core arith sets.

  rewrite IHM; auto with core arith sets.
  f_equal; auto with core arith sets.

  rewrite IHM; auto with core arith sets.
  f_equal.

  induction args; simpl in |- *; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H1; auto with core arith sets.
  rewrite IHargs; auto with core arith sets.
Qed.

Lemma permute_lift : forall M k, lift 1 (lift_rec 1 M k) = lift_rec 1 (lift 1 M) (S k).
Proof.
  intros.
  change (lift_rec 1 (lift_rec 1 M k) 0 = lift_rec 1 (lift_rec 1 M 0) (1 + k))
  in |- *.
  apply permute_lift_rec; auto with rust core arith sets.
Qed.

Lemma simpl_subst_rec :
  forall N M n p k,
  p <= n + k ->
  k <= p -> subst_rec N (lift_rec (S n) M k) p = lift_rec n M k
.
Proof.
  induction M using term_list_mut_ind; simpl in |- *; intros; auto with core sets arith.

  f_equal.
  generalize p n k H0 H1; clear H1 H0 p n k; induction args; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H2; auto with core arith sets.
  rewrite IHargs; auto with core arith sets.
  rewrite <- plus_n_Sm; auto with core arith sets.
  rewrite IHM; auto with core arith sets.
  cut (forall X Y, X = Y -> X + p <= n + (Y + k)); intros.
  apply H2.
  clear H; generalize n k; induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; rewrite Nat.add_assoc; rewrite (Nat.add_comm n X); rewrite <- Nat.add_assoc; auto with core arith sets.
  cut (forall X Y, X = Y -> X + k <= Y + p); intros.
  apply H2.
  clear H; generalize n k; induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; auto with core arith sets.

  rewrite IHM1; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.

  rewrite IHM1; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.

  elim (le_gt_dec k n); intros.
  rewrite subst_ref_gt; auto with rust core arith sets.
  red in |- *; red in |- *.
  apply le_trans with (S (n0 + k)); auto with rust core arith sets.
  rewrite subst_ref_lt; auto with rust core arith sets.
  apply le_gt_trans with k; auto with rust core arith sets.

  rewrite IHM1.
  rewrite IHM2.
  f_equal.
  generalize k n p H H0 H1; clear H H0 H1 n k p.
  induction args; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H2; auto with core arith sets.
  rewrite IHargs; auto with core arith sets.
  rewrite <- plus_n_Sm; auto with core arith sets.
  cut (forall X Y, X = Y -> X + p <= n + (Y + k)); intros.
  apply H2.
  clear H; generalize n k; induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; rewrite Nat.add_assoc; rewrite (Nat.add_comm n X); rewrite <- Nat.add_assoc; auto with core arith sets.
  cut (forall X Y, X = Y -> X + k <= Y + p); intros.
  apply H2.
  clear H; generalize n k; induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; auto with core arith sets.
  cut (forall X Y, X = Y -> X + p <= n + (Y + k)); intros.
  apply H2.
  clear H; generalize n k; induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; rewrite Nat.add_assoc; rewrite (Nat.add_comm n X); rewrite <- Nat.add_assoc; auto with core arith sets.
  cut (forall X Y, X = Y -> X + k <= Y + p); intros.
  apply H2.
  clear H; generalize n k; induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; auto with core arith sets.

  rewrite IHM; auto with core arith sets.
  rewrite <- plus_n_Sm; auto with core arith sets.

  rewrite IHM; auto with core arith sets.
  f_equal.
  generalize k n p H H0 H1; clear H H0 H1 n k p.
  induction args; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H2; auto with core arith sets.
  rewrite IHargs; auto with core arith sets.
Qed.

Lemma simpl_subst :
  forall N M n p, p <= n -> subst_rec N (lift (S n) M) p = lift n M
.
Proof.
  intros; unfold lift in |- *.
  apply simpl_subst_rec; auto with rust core arith sets.
Qed.

Lemma commut_lift_subst_rec :
  forall M N n p k,
  k <= p ->
  lift_rec n (subst_rec N M p) k = subst_rec N (lift_rec n M k) (n + p).
Proof.
  induction M using term_list_mut_ind; simpl in |- *; intros; auto with core sets arith.

  f_equal.
  generalize n k p H H0; clear H0 H p k n; induction args; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H1; auto with core arith sets.
  rewrite IHargs; auto with core arith sets.
  rewrite plus_n_Sm; auto with core arith sets.
  rewrite IHM; auto with core arith sets.
  f_equal.
  f_equal.
  clear H; generalize n k p; induction args; simpl in |- *; intros; auto with core arith sets.
  clear H; generalize n k p; induction args; simpl in |- *; intros; auto with core arith sets.
  rewrite <- plus_n_Sm.
  rewrite <- IHargs; auto with core arith sets.
  cut (forall X Y, X = Y -> X + k <= Y + p); intros.
  apply H1.
  clear H; generalize p; induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; auto with core arith sets.

  rewrite IHM1; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.

  rewrite IHM1; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.

  elim (lt_eq_lt_dec p n);
  [ intro Hlt_eq; elim (le_gt_dec k n); [ intro Hle | intro Hgt ]
  | intro Hlt; elim (le_gt_dec k n); [ intro Hle | intro Hgt ] ].
  elim Hlt_eq; clear Hlt_eq.
  case n; [ intro Hlt | intros ].
  inversion_clear Hlt.
  unfold pred in |- *.
  rewrite lift_ref_ge; auto with rust core arith sets.
  rewrite subst_ref_gt; auto with rust core arith sets.
  elim plus_n_Sm with n0 n1.
  auto with rust core arith sets.
  apply le_trans with p; auto with rust core arith sets.
  simple induction 1.
  rewrite subst_ref_eq.
  unfold lift in |- *.
  rewrite simpl_lift_rec; auto with rust core arith sets.
  absurd (k <= n); auto with rust core arith sets.
  apply le_trans with p; auto with rust core arith sets.
  elim Hlt_eq; auto with rust core arith sets.
  simple induction 1; auto with rust core arith sets.
  rewrite lift_ref_ge; auto with rust core arith sets.
  rewrite subst_ref_lt; auto with rust core arith sets.
  rewrite lift_ref_lt; auto with rust core arith sets.
  rewrite subst_ref_lt; auto with rust core arith sets.
  apply le_gt_trans with p; auto with rust core arith sets.

  f_equal.
  generalize n k p H H0; clear H0 H n k p; induction args; simpl in |- *; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H1; auto with core arith sets.
  rewrite IHargs; auto with core arith sets.
  rewrite <- plus_n_Sm; auto with core arith sets.
  rewrite IHM1; auto with core arith sets.
  f_equal.
  f_equal.
  clear H; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.
  clear H; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.
  rewrite <- IHargs; auto with core arith sets.
  cut (forall X Y, X = Y -> X + k <= Y + p); intros.
  apply H1.
  clear H; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.
  f_equal.
  f_equal.
  clear H; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.
  clear H; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.
  rewrite <- IHargs; auto with core arith sets.
  cut (forall X Y, X = Y -> X + k <= Y + p); intros.
  apply H1.
  clear H; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.
  subst Y; auto with core arith sets.

  rewrite IHM; auto with core arith sets.
  f_equal; auto with core arith sets.

  rewrite IHM; auto with core arith sets.
  f_equal.
  generalize n k p H H0; clear H0 H p k n; induction args; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H1; auto with core arith sets.
  rewrite IHargs; auto with core arith sets.
Qed.

Lemma commut_lift_subst :
   forall M N k, subst_rec N (lift 1 M) (S k) = lift 1 (subst_rec N M k).
Proof.
  intros; unfold lift in |- *.
  rewrite commut_lift_subst_rec; auto with rust core arith sets.
Qed.


Lemma distr_lift_subst_rec :
  forall M N n p k,
  lift_rec n (subst_rec N M p) (p + k) =
  subst_rec (lift_rec n N k) (lift_rec n M (S (p + k))) p.
Proof.
  induction M using term_list_mut_ind; intros; auto with core sets arith.

  simpl in |- *.
  f_equal.
  generalize n p k H; clear H k p n; induction args; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H0; auto with core arith sets.
  change (S (p + k)) with (S p + k).
  rewrite IHargs; auto with core arith sets.
  cut (
    length (
      (
        fix
        F (N0 : term) (l : list term) (k0 : nat) {struct l} : list term :=
        match l with
        | nil => nil
        | h :: t => subst_rec N0 h k0 :: F N0 t (S k0)
        end
      ) N args p
    ) = length args
  ); intros.
  rewrite H0.
  cut (
    length (
      (
        fix
        F (n0 : nat) (l : list term) (k0 : nat) {struct l} : list term :=
        match l with
        | nil => nil
        | h :: t => lift_rec n0 h k0 :: F n0 t (S k0)
        end
      ) n args (S (p + k))
    ) = length args
  ); intros.
  rewrite H1.
  rewrite Nat.add_assoc.
  rewrite IHM.
  f_equal; f_equal.
  repeat rewrite plus_n_Sm.
  rewrite Nat.add_assoc; reflexivity.
  clear H H0; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.
  rewrite plus_n_Sm; rewrite IHargs; auto with core arith sets.
  clear H; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.

  simpl in |- *.
  rewrite IHM1; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.

  simpl in |- *.
  rewrite IHM1; auto with core arith sets.
  rewrite IHM2; auto with core arith sets.

  unfold subst_rec at 1 in |- *.
  elim (lt_eq_lt_dec p n); [ intro a | intro b ].
  elim a; clear a.
  case n; [ intro a | intros n1 b ].
  inversion_clear a.
  unfold pred, lift_rec at 1 in |- *.
  elim (le_gt_dec (p + k) n1); intro.
  rewrite lift_ref_ge; auto with rust core arith sets.
  elim plus_n_Sm with n0 n1.
  rewrite subst_ref_gt; auto with rust core arith sets.
  red in |- *; red in |- *; apply le_n_S.
  apply le_trans with (n0 + (p + k)); auto with rust core arith sets.
  apply le_trans with (p + k); auto with rust core arith sets.
  rewrite lift_ref_lt; auto with rust core arith sets.
  rewrite subst_ref_gt; auto with rust core arith sets.
  simple induction 1.
  unfold lift in |- *.
  rewrite <- permute_lift_rec; auto with rust core arith sets.
  rewrite lift_ref_lt; auto with rust core arith sets.
  rewrite subst_ref_eq; auto with rust core arith sets.
  rewrite lift_ref_lt; auto with rust core arith sets.
  rewrite lift_ref_lt; auto with rust core arith sets.
  rewrite subst_ref_lt; auto with rust core arith sets.

  simpl in |- *; f_equal.
  generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H0; auto with core arith sets.
  change (S (p0 + k0)) with (S p0 + k0).
  rewrite IHargs; auto with core arith sets.
  cut (
    length (
      (
        fix
        F (N0 : term) (l : list term) (k0 : nat) {struct l} : list term :=
        match l with
        | nil => nil
        | h :: t => subst_rec N0 h k0 :: F N0 t (S k0)
        end
      ) N args p
    ) = length args
  ); intros.
  rewrite H0.
  cut (
    length (
      (
        fix
        F (n0 : nat) (l : list term) (k0 : nat) {struct l} : list term :=
        match l with
        | nil => nil
        | h :: t => lift_rec n0 h k0 :: F n0 t (S k0)
        end
      ) n args (S (p + k))
    ) = length args
  ); intros.
  rewrite H1.
  rewrite Nat.add_assoc.
  rewrite IHM1.
  f_equal; f_equal.
  repeat rewrite plus_n_Sm.
  rewrite Nat.add_assoc; reflexivity.
  clear H H0; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.
  rewrite plus_n_Sm; rewrite IHargs; auto with core arith sets.
  clear H; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.
  cut (
    length (
      (
        fix
        F (N0 : term) (l : list term) (k0 : nat) {struct l} : list term :=
        match l with
        | nil => nil
        | h :: t => subst_rec N0 h k0 :: F N0 t (S k0)
        end
      ) N args p
    ) = length args
  ); intros.
  rewrite H0.
  cut (
    length (
      (
        fix
        F (n0 : nat) (l : list term) (k0 : nat) {struct l} : list term :=
        match l with
        | nil => nil
        | h :: t => lift_rec n0 h k0 :: F n0 t (S k0)
        end
      ) n args (S (p + k))
    ) = length args
  ); intros.
  rewrite H1.
  rewrite Nat.add_assoc.
  rewrite IHM2.
  f_equal; f_equal.
  repeat rewrite plus_n_Sm.
  rewrite Nat.add_assoc; reflexivity.
  clear H H0; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.
  rewrite plus_n_Sm; rewrite IHargs; auto with core arith sets.
  clear H; generalize n p k; induction args; simpl in |- *; intros; auto with core arith sets.

  simpl in |- *.
  change (S (p + k)) with (S p + k); rewrite <- IHM; auto with core arith sets.

  simpl in |- *.
  rewrite IHM; auto with core arith sets.
  f_equal.
  generalize n p k H; clear H k p n; induction args; simpl in |- *; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H0; f_equal.
  rewrite IHargs; auto with core arith sets.
Qed.

Lemma distr_lift_subst :
  forall M N n k,
  lift_rec n (subst N M) k = subst (lift_rec n N k) (lift_rec n M (S k))
.
Proof.
  intros; unfold subst in |- *.
  pattern k at 1 3 in |- *.
  replace k with (0 + k); auto with rust core arith sets.
  apply distr_lift_subst_rec.
Qed.

Lemma distr_subst_rec :
  forall M N (P : term) n p,
  subst_rec P (subst_rec N M p) (p + n) =
  subst_rec (subst_rec P N n) (subst_rec P M (S (p + n))) p
.
Proof.
  induction M using term_list_mut_ind; auto with core arith sets.

  simpl in |- *; intros.
  cut (
    length (
      (
        fix F (N : term) (l : list term) (k : nat) {struct l} : list term :=
        match l with
        | nil => nil
        | h :: t => subst_rec N h k :: F N t (S k)
        end
      ) N args p
    ) = length args
  ); intros.
  rewrite H0.
  cut (
    length (
      (
        fix F (N : term) (l : list term) (k : nat) {struct l} : list term :=
        match l with
        | nil => nil
        | h :: t => subst_rec N h k :: F N t (S k)
        end
      ) P args (S (p + n))
    ) = length args
  ); intros.
  rewrite H1.
  rewrite Nat.add_assoc.
  rewrite IHM.
  rewrite <- (plus_n_Sm (length args) (p + n)).
  rewrite Nat.add_assoc.
  f_equal.
  clear H0 H1; generalize n p H; clear H p n; induction args; simpl in |- *; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H0.
  change (S (p + n)) with (S p + n).
  rewrite IHargs; auto with core arith sets.
  generalize n p; clear H0 H n p; induction args; simpl in |- *; intros; auto with core arith sets.
  change (S (p + n)) with (S p + n); rewrite IHargs; auto with core arith sets.
  generalize n p; clear H; induction args; simpl in |- *; intros; auto with core arith sets.

  simpl in |- *; intros.
  rewrite IHM1; rewrite IHM2; auto with core arith sets.

  simpl in |- *; intros.
  rewrite IHM1; rewrite IHM2; auto with core arith sets.

  intros.
  unfold subst_rec at 2 in |- *.
  elim (lt_eq_lt_dec p n); [ intro Hlt_eq | intro Hlt ].
  elim Hlt_eq; clear Hlt_eq.
  case n; [ intro Hlt | intros n1 Heq1 ].
  inversion_clear Hlt.
  unfold pred, subst_rec at 1 in |- *.
  elim (lt_eq_lt_dec (p + n0) n1); [ intro Hlt_eq | intro Hlt ].
  elim Hlt_eq; clear Hlt_eq.
  case n1; [ intro Hlt | intros n2 Heq2 ].
  inversion_clear Hlt.
  rewrite subst_ref_gt; auto with rust core arith sets.
  rewrite subst_ref_gt; auto with rust core arith sets.
  apply gt_le_trans with (p + n0); auto with rust core arith sets.
  simple induction 1.
  rewrite subst_ref_eq; auto with rust core arith sets.
  rewrite simpl_subst; auto with rust core arith sets.
  rewrite subst_ref_lt; auto with rust core arith sets.
  rewrite subst_ref_gt; auto with rust core arith sets.
  simple induction 1.
  rewrite subst_ref_lt; auto with rust core arith sets.
  rewrite subst_ref_eq.
  unfold lift in |- *.
  rewrite commut_lift_subst_rec; auto with rust core arith sets.
  do 3 (rewrite subst_ref_lt; auto with rust core arith sets).

  simpl in |- *; intros.
  cut (
    length (
      (
        fix F (N : term) (l : list term) (k : nat) {struct l} : list term :=
        match l with
        | nil => nil
        | h :: t => subst_rec N h k :: F N t (S k)
        end
      ) N args p
    ) = length args
  ); intros.
  rewrite H0.
  cut (
    length (
      (
        fix F (N : term) (l : list term) (k : nat) {struct l} : list term :=
        match l with
        | nil => nil
        | h :: t => subst_rec N h k :: F N t (S k)
        end
      ) P args (S (p + n))
    ) = length args
  ); intros.
  rewrite H1.
  rewrite Nat.add_assoc; rewrite IHM1; rewrite IHM2; f_equal.
  generalize p n H; clear H1 H0 H n p; induction args; simpl in |- *; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H0.
  change (S (p + n)) with (S p + n); rewrite IHargs; auto with core arith sets.
  rewrite <- plus_n_Sm; rewrite Nat.add_assoc; auto with core arith sets.
  rewrite <- plus_n_Sm; rewrite Nat.add_assoc; auto with core arith sets.
  clear H0 H; generalize n p; clear n p; induction args; simpl in |- *; intros; auto with core arith sets.
  change (S (p + n)) with (S p + n); rewrite IHargs; auto with core arith sets.
  clear H; generalize n p; clear n p; induction args; simpl in |- *; intros; auto with core arith sets.

  simpl in |- *; intros.
  change (S (p + n)) with (S p + n); rewrite IHM; auto with core arith sets.

  simpl in |- *; intros.
  rewrite IHM.
  f_equal.
  generalize n p H; clear n p H; induction args; simpl in |- *; intros; auto with core arith sets.
  inversion_clear H.
  rewrite H0.
  rewrite IHargs; auto with core arith sets.
Qed.

Lemma distr_subst :
  forall (P : term) N M k,
  subst_rec P (subst N M) k = subst (subst_rec P N k) (subst_rec P M (S k))
.
Proof.
  intros; unfold subst in |- *.
  pattern k at 1 3 in |- *.
  replace k with (0 + k); auto with rust core arith sets.
  apply distr_subst_rec.
Qed.

(*
LEMMAS ABOUT BETA REDUCTION
===================================================================================
*)


Lemma one_step_red : forall M N, red1 M N -> red M N.
Proof.
  intros.
  apply trans_red with M; auto with rust core arith sets.
Qed.

Hint Resolve one_step_red: coc.


Lemma red1_red_ind :
  forall N (P : term -> Prop),
  P N ->
  (forall M (R : term), red1 M R -> red R N -> P R -> P M) ->
  forall M, red M N -> P M
.
Proof.
  cut (
    forall M N,
    red M N ->
    forall P : term -> Prop,
    P N -> (forall M (R : term), red1 M R -> red R N -> P R -> P M) -> P M
  ).
  intros.
  apply (H M N); auto with rust core arith sets.

  simple induction 1; intros; auto with rust core arith sets.
  apply H1; auto with rust core arith sets.
  apply H4 with N0; auto with rust core arith sets.

  intros.
  apply H4 with R; auto with rust core arith sets.
  apply trans_red with P; auto with rust core arith sets.
Qed.

Lemma trans_red_red : forall M N (P : term), red M N -> red N P -> red M P.
Proof.
  intros.
  generalize H0 M H.
  simple induction 1; auto with rust core arith sets.
  intros.
  apply trans_red with P0; auto with rust core arith sets.
Qed.
 
(*)
(* lifting preserves one-step reduction *)
Lemma red1_lift :
  forall u v, red1 u v -> forall n k, red1 (lift_rec n u k) (lift_rec n v k)
.
Proof.
  simple induction 1; simpl in |- *; intros; auto with rust core arith sets.
  rewrite distr_lift_subst; auto with rust core arith sets.
Qed.

Hint Resolve red1_lift: coc.

(* substituition respects one step reduction V1 *)
Lemma red1_subst_r :
  forall t u,
  red1 t u -> forall (a : term) k, red1 (subst_rec a t k) (subst_rec a u k)
.
Proof.
  simple induction 1; simpl in |- *; intros; auto with rust core arith sets.
  rewrite distr_subst; auto with rust core arith sets.
Qed.


(* substituition respects one step reduction V2 *)
Lemma red1_subst_l :
  forall (a : term) t u k,
  red1 t u -> red (subst_rec t a k) (subst_rec u a k)
.
Proof.
  simple induction a; simpl in |- *; auto with rust core arith sets.

  intros.
  elim (lt_eq_lt_dec k n);
  [ intro a0 | intro b; auto with rust core arith sets ].
  elim a0; auto with rust core arith sets.
  unfold lift in |- *; auto with rust core arith sets.
Qed.

Hint Resolve red1_subst_l red1_subst_r: coc.


(* A logical lemma when we have to reason about reduction on product *)
Lemma red_prod_prod :
  forall u v t,
  red (Prod u v) t ->
  forall P : Prop,
  (forall a b : term, t = Prod a b -> red u a -> red v b -> P) -> P
.
Proof.
  simple induction 1; intros.
  apply H0 with u v; auto with rust core arith sets.

  apply H1; intros.
  inversion_clear H4 in H2.
  inversion H2.
  apply H3 with N1 b; auto with rust core arith sets.
  apply trans_red with a; auto with rust core arith sets.

  apply H3 with a N2; auto with rust core arith sets.
  apply trans_red with b; auto with rust core arith sets.
Qed.


(* A sort doesn't reduce to anything than itself *)
Lemma red_sort_sort : forall s t, red (Srt s) t -> t <> Srt s -> False.
Proof.
  simple induction 1; intros; auto with rust core arith sets.
  apply H1.
  generalize H2.
  case P; intros; try discriminate.
  inversion_clear H4.
Qed.

(* relation between one-step reduction and convertibility *)
Lemma one_step_conv_exp : forall M N, red1 M N -> conv N M.
Proof.
  intros.
  apply trans_conv_exp with N; auto with rust core arith sets.
Qed.


(* relation between reduction and convertability *)
Lemma red_conv : forall M N, red M N -> conv M N.
Proof.
  simple induction 1; auto with rust core arith sets.
  intros; apply trans_conv_red with P; auto with rust core arith sets.
Qed.

Hint Resolve one_step_conv_exp red_conv: coc.


(* Convertability is symmetric *)
Lemma sym_conv : forall M N, conv M N -> conv N M.
Proof.
  simple induction 1; auto with rust core arith sets.
  simple induction 2; intros; auto with rust core arith sets.
  apply trans_conv_red with P0; auto with rust core arith sets.

  apply trans_conv_exp with P0; auto with rust core arith sets.

  simple induction 2; intros; auto with rust core arith sets.
  apply trans_conv_red with P0; auto with rust core arith sets.

  apply trans_conv_exp with P0; auto with rust core arith sets.
Qed.

Hint Immediate sym_conv: coc.


(* Convertability is transitive *)
Lemma trans_conv_conv :
  forall M N (P : term), conv M N -> conv N P -> conv M P
.
Proof.
  intros.
  generalize M H; elim H0; intros; auto with rust core arith sets.
  apply trans_conv_red with P0; auto with rust core arith sets.

  apply trans_conv_exp with P0; auto with rust core arith sets.
Qed.


(* Convertability and product *)
Lemma conv_conv_prod :
  forall a b c d : term, conv a b -> conv c d -> conv (Prod a c) (Prod b d).
Proof.
  intros.
  apply trans_conv_conv with (Prod a d).
  elim H0; intros; auto with rust core arith sets.
  apply trans_conv_red with (Prod a P); auto with rust core arith sets.

  apply trans_conv_exp with (Prod a P); auto with rust core arith sets.

  elim H; intros; auto with rust core arith sets.
  apply trans_conv_red with (Prod P d); auto with rust core arith sets.

  apply trans_conv_exp with (Prod P d); auto with rust core arith sets.
Qed.


Lemma conv_conv_lift :
  forall (a b : term) n k,
  conv a b -> conv (lift_rec n a k) (lift_rec n b k)
.
Proof.
  intros.
  elim H; intros; auto with rust core arith sets.
  apply trans_conv_red with (lift_rec n P k); auto with rust core arith sets.

  apply trans_conv_exp with (lift_rec n P k); auto with rust core arith sets.
Qed.
 

Lemma conv_conv_subst :
  forall (a b c d : term) k,
  conv a b -> conv c d -> conv (subst_rec a c k) (subst_rec b d k)
.
Proof.
  intros.
  apply trans_conv_conv with (subst_rec a d k).
  elim H0; intros; auto with rust core arith sets.
  apply trans_conv_red with (subst_rec a P k); auto with rust core arith sets.

  apply trans_conv_exp with (subst_rec a P k); auto with rust core arith sets.

  elim H; intros; auto with rust core arith sets.
  apply trans_conv_conv with (subst_rec P d k); auto with rust core arith sets.

  apply trans_conv_conv with (subst_rec P d k); auto with rust core arith sets.
  apply sym_conv; auto with rust core arith sets.
Qed.

Hint Resolve conv_conv_prod conv_conv_lift conv_conv_subst: coc.


Lemma refl_par_red1 : forall M, par_red1 M M.
Proof.
  simple induction M; auto with rust core arith sets.
Qed.

Hint Resolve refl_par_red1: coc.


Lemma red1_par_red1 : forall M N, red1 M N -> par_red1 M N.
Proof.
  simple induction 1; auto with rust core arith sets; intros.
Qed.

Hint Resolve red1_par_red1: coc.


Lemma red_par_red : forall M N, red M N -> par_red M N.
Proof.
  red in |- *; simple induction 1; intros; auto with rust core arith sets.
  apply t_trans with P; auto with rust core arith sets.
Qed.


Lemma par_red_red : forall M N, par_red M N -> red M N.
Proof.
  simple induction 1.
  simple induction 1; intros; auto with rust core arith sets.
  apply trans_red with (App (Abs T M') N'); auto with rust core arith sets.

  intros.
  apply trans_red_red with on_zero; auto with rust core arith sets.

  intros.
  apply trans_red_red with (App on_succ num); auto with rust core arith sets.

  intros.
  apply trans_red_red with on_zero; auto with rust core arith sets.

  intros.
  apply trans_red_red with (App on_succ num); auto with rust core arith sets.

  intros.
  apply trans_red_red with on_zero; auto with rust core arith sets.

  intros.
  apply trans_red_red with (App (App on_succ num) (NatRec choice on_zero on_succ num)); auto with rust core arith sets.

  intros.
  apply trans_red_red with on_zero; auto with rust core arith sets.

  intros.
  apply trans_red_red with (App (App on_succ num) (NatInd choice on_zero on_succ num)); auto with rust core arith sets.  

  intros.
  apply trans_red_red with y; auto with rust core arith sets.
Qed.

Hint Resolve red_par_red par_red_red: coc.


Lemma par_red1_lift :
  forall n (a b : term),
  par_red1 a b -> forall k, par_red1 (lift_rec n a k) (lift_rec n b k)
.
Proof.
  simple induction 1; simpl in |- *; auto with rust core arith sets.
  intros.
  rewrite distr_lift_subst; auto with rust core arith sets.
Qed.


Lemma par_red1_subst :
  forall c d : term,
  par_red1 c d ->
  forall a b : term,
  par_red1 a b -> forall k, par_red1 (subst_rec a c k) (subst_rec b d k)
.
Proof.
  simple induction 1; simpl in |- *; auto with rust core arith sets; intros.
  rewrite distr_subst; auto with rust core arith sets.

  elim (lt_eq_lt_dec k n); auto with rust core arith sets; intro a0.
  elim a0; intros; auto with rust core arith sets.
  unfold lift in |- *.
  apply par_red1_lift; auto with rust core arith sets.
Qed.


Lemma inv_par_red_abs :
  forall (P : Prop) T (U x : term),
  par_red1 (Abs T U) x ->
  (forall T' (U' : term), x = Abs T' U' -> par_red1 U U' -> P) -> P
.
Proof.
  do 5 intro.
  inversion_clear H; intros.
  apply H with T' M'; auto with rust core arith sets.
Qed.

Hint Resolve par_red1_lift par_red1_subst: coc.

(* A term which the normal form reduces to is the normal form itself *)
Lemma red_normal : forall u v, red u v -> normal u -> u = v.
Proof.
  simple induction 1; auto with rust core arith sets; intros.
  absurd (red1 u N); auto with rust core arith sets.
  absurd (red1 P N); auto with rust core arith sets.
  elim (H1 H3).
  unfold not in |- *; intro; apply (H3 N); auto with rust core arith sets.
Qed.

(*  
  Let x, y and z be three terms.
  If
    y is a subterm of x and z reduces to y
  Then
    exists y' such that z is a subterm of y'
    and y' reduces to x
  Basically subterm and red1 relations commute.
*)
Lemma commut_red1_subterm : commut _ subterm (transp _ red1).
Proof.
  red in |- *.
  simple induction 1; intros.
  inversion_clear H0.
  exists (Abs t z); auto with rust core arith sets.

  exists (Prod t z); auto with rust core arith sets.

  inversion_clear H0.
  exists (Abs z n); auto with rust core arith sets.

  exists (App z v); auto with rust core arith sets.

  exists (App u z); auto with rust core arith sets.

  exists (Prod z n); auto with rust core arith sets.

  exists (NatDestruct z a2 a3 a4); auto with rust core arith sets.

  exists (NatDestruct a1 z a3 a4); auto with rust core arith sets.

  exists (NatDestruct a1 a2 z a4); auto with rust core arith sets.

  exists (NatDestruct a1 a2 a3 z); auto with rust core arith sets.

  exists (NatCases z a2 a3 a4); auto with rust core arith sets.

  exists (NatCases a1 z a3 a4); auto with rust core arith sets.

  exists (NatCases a1 a2 z a4); auto with rust core arith sets.
  
  exists (NatCases a1 a2 a3 z); auto with rust core arith sets.

  exists (NatSucc z); auto with rust core arith sets.

  exists (NatRec z a2 a3 a4); auto with rust core arith sets.

  exists (NatRec a1 z a3 a4); auto with rust core arith sets.

  exists (NatRec a1 a2 z a4); auto with rust core arith sets.

  exists (NatRec a1 a2 a3 z); auto with rust core arith sets.

  exists (NatInd z a2 a3 a4); auto with rust core arith sets.

  exists (NatInd a1 z a3 a4); auto with rust core arith sets.

  exists (NatInd a1 a2 z a4); auto with rust core arith sets.
  
  exists (NatInd a1 a2 a3 z); auto with rust core arith sets.
Qed.
*)