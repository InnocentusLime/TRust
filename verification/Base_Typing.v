(*
    Here the typing rules of the system are defined. We also define some
    main facts, but don't prove them here. For proofs see `TypingAndReduction.v`
*)
Require Import Program.Equality.

Require List.
Require Import Term.
Require Import String.
Require Import Context.
Require Import ListLemmas.
Require Import TermReduction.

Reserved Notation "G |- x := y" (at level 85, no associativity).

(* Typing rules of the `base system` *)
Inductive typing : context -> term -> term -> Prop :=
(* Core typing *)
| TNat :
    forall (ctx : context),
    WF ctx ->
    ctx |- Nat := SmallKind
| TNatO : 
    forall (ctx : context),
    WF ctx ->
    ctx |- NatO := Nat
| TNatSucc : 
    forall (ctx : context),
    WF ctx ->
    ctx |- NatSucc := Forall "_"%string Nat Nat
| TNatRec : 
    forall (ctx : context),
    forall choice zero step num : term,
    ctx |- choice := Nat ===> SmallKind -> 
    ctx |- zero := App choice NatO ->
    ctx |- step := Forall "n"%string Nat (App (lift choice 0 1) (Var 0) ===> App (lift choice 0 2) (App NatSucc (Var 1))) ->
    ctx |- num := Nat ->
    ctx |- NatRec choice zero step num := App choice num
| TApp : 
    forall (ctx : context),
    forall (str : string) (domain range : term) (l r : term),
    ctx |- l := Forall str domain range ->
    ctx |- r := domain ->
    ctx |- App l r := top_subst range r
| TAbsSmall : 
    forall (ctx : context),
    forall (str : string) (range : term) (arg_type body : term),
    ctx |- arg_type := SmallKind ->
    push_var ctx str arg_type |- body := range ->
    ctx |- Abs str arg_type body := Forall str arg_type range
| TAbsType : 
    forall (ctx : context),
    forall (str : string) (range : term) (arg_type body : term) (i : nat),
    ctx |- arg_type := TypeKind i ->
    { str == arg_type } :: ctx |- body := range ->
    ctx |- Abs str arg_type body := Forall str arg_type range
| TAbsProp : 
    forall (ctx : context),
    forall (str : string) (range : term) (arg_type body : term),
    ctx |- arg_type := PropKind ->
    { str == arg_type } :: ctx |- body := range ->
    ctx |- Abs str arg_type body := Forall str arg_type range
| TVar : 
    forall (ctx : context),
    forall (n : nat) (t : term), 
    WF ctx -> 
    ctx[n] := t -> 
    ctx |- Var n := t
| TSmallKind : 
    forall (ctx : context),
    WF ctx -> 
    ctx |- SmallKind := TypeKind 0
| TPropKind :
    forall (ctx : context),
    WF ctx -> 
    ctx |- PropKind := TypeKind 0
| TTypeKind : 
    forall (ctx : context),
    WF ctx -> 
    forall n : nat, ctx |- TypeKind n := TypeKind (S n)
| TForallType : 
    forall (ctx : context),
    forall (str : string) (domain range : term) (universe : nat),
    ctx |- domain := TypeKind universe ->
    { str == domain } :: ctx |- range := TypeKind universe ->
    ctx |- Forall str domain range := TypeKind universe
| TForallPropSmall : 
    forall (ctx : context),
    forall (str : string) (domain range : term),
    ctx |- domain := SmallKind ->
    { str == domain } :: ctx |- range := PropKind ->
    ctx |- Forall str domain range := PropKind
| TForallPropProp : 
    forall (ctx : context),
    forall (str : string) (domain range : term),
    ctx |- domain := PropKind ->
    { str == domain } :: ctx |- range := PropKind ->
    ctx |- Forall str domain range := PropKind
| TForallPropType : 
    forall (ctx : context),
    forall (str : string) (domain range : term),
    forall (i : nat), ctx |- domain := TypeKind i ->
    { str == domain } :: ctx |- range := PropKind ->
    ctx |- Forall str domain range := PropKind
| TForallSmallSmall : 
    forall (ctx : context),
    forall (str : string) (domain range : term),
    ctx |- domain := SmallKind ->
    { str == domain } :: ctx |- range := SmallKind ->
    ctx |- Forall str domain range := SmallKind
| TForallSmallProp : 
    forall (ctx : context),
    forall (str : string) (domain range : term),
    ctx |- domain := PropKind ->
    { str == domain } :: ctx |- range := SmallKind ->
    ctx |- Forall str domain range := SmallKind
(* Universe transition rules *)
| JumpToTypeUniverseSmall :
    forall (ctx : context),
    forall (t : term),
    ctx |- t := SmallKind ->
    ctx |- t := TypeKind 0
| JumpToTypeUniverseProp :
    forall (ctx : context),
    forall (t : term),
    ctx |- t := PropKind ->
    ctx |- t := TypeKind 0
| RaiseUniverse : 
    forall (ctx : context),
    forall (t : term) (universe : nat),
    ctx |- t := TypeKind universe ->
    ctx |- t := TypeKind (S universe)
(* Conversion axioms *)
| ConversionSmallL : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |- t := type ->
    ctx |- type := SmallKind ->
    type ->b type' ->
    ctx |- type' := SmallKind ->
    ctx |- t := type'
| ConversionPropL : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |- t := type ->
    ctx |- type := PropKind ->
    type ->b type' ->
    ctx |- type' := PropKind ->
    ctx |- t := type'
| ConversionTypeL : 
    forall (ctx : context),
    forall (t : term) (type type' : term) (i : nat),
    ctx |- t := type ->
    ctx |- type := TypeKind i ->
    type ->b type' ->
    ctx |- type' := TypeKind i ->
    ctx |- t := type'
| ConversionSmallR : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |- t := type ->
    ctx |- type := SmallKind ->
    type' ->b type ->
    ctx |- type' := SmallKind ->
    ctx |- t := type'
| ConversionPropR : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |- t := type ->
    ctx |- type := PropKind ->
    type' ->b type ->
    ctx |- type' := PropKind ->
    ctx |- t := type'
| ConversionTypeR : 
    forall (ctx : context),
    forall (t : term) (type type' : term) (i : nat),
    ctx |- t := type ->
    ctx |- type := TypeKind i ->
    type' ->b type ->
    ctx |- type' := TypeKind i ->
    ctx |- t := type'
| ConversionSmallRename : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |- t := type ->
    ctx |- type := SmallKind ->
    type =a type' ->
    ctx |- type' := SmallKind ->
    ctx |- t := type'
| ConversionPropRename : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |- t := type ->
    ctx |- type := PropKind ->
    type =a type' ->
    ctx |- type' := PropKind ->
    ctx |- t := type'
| ConversionTypeRename : 
    forall (ctx : context),
    forall (t : term) (type type' : term) (i : nat),
    ctx |- t := type ->
    ctx |- type := TypeKind i ->
    type =a type' ->
    ctx |- type' := TypeKind i ->
    ctx |- t := type'
(* Well formed context axioms *)
with WF : context -> Prop :=
| WF_empty : WF nil
| WF_assum_small : 
    forall (ctx : context) (str : string) (t : term),
    WF ctx ->
    ctx |- t := SmallKind ->
    WF (push_var ctx str t)
| WF_assum_prop :
    forall (ctx : context) (str : string) (t : term),
    WF ctx ->
    ctx |- t := PropKind ->
    WF (push_var ctx str t)
| WF_assum_type :
    forall (ctx : context) (str : string) (t : term) (i : nat),
    WF ctx ->
    ctx |- t := TypeKind i ->
    WF (push_var ctx str t)
| WF_dummy_assum :
    forall (ctx : context),
    WF ctx ->
    WF (push_dummy ctx)

where "G |- x := y" := (typing G x y)
.

(* Induction scheme when the simple induction won't do the trick *)
Scheme typing_ind_mut := Induction for 
typing Sort Prop
with wf_ind_mut := Induction for 
WF Sort Prop.

Definition typable (ctx : context) (t : term) := exists type : term, ctx |- t := type.
Notation "G |- x := ?" := (typable G x) (at level 85, no associativity).

Theorem typable_wf : forall (ctx : context) (t type : term),
    ctx |- t := type ->
    WF ctx
.
Proof.
    intros.
    induction H; try easy.
Qed.

Lemma wf_ctx_slot_lt_var : forall (ctx : context),
    WF ctx ->
    (
        forall (slot : nat) (t : term),
        ctx[slot] := t ->
        (forall v, var_occurs t v -> slot < v)
    )
.
Proof.
    intros ctx H.
    induction H; intros.

    unfold has_type in H.
    destruct slot; easy.

    destruct slot.
    unfold has_type in H1; simpl in H1.
    subst t0.
    destruct v.
    exfalso; generalize H2; apply (lifting_destroys _ _ _ _ (Le.le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply PeanoNat.Nat.lt_0_succ.
    change (({str == t} :: ctx)[S slot] := t0) with ((lift_context ctx 0 1)[slot] := t0) in H1.
    destruct (ctx_var_lifted_repr _ _ _ _ _ H1).
    subst t0.
    destruct v.
    exfalso; generalize H2; apply (lifting_destroys _ _ _ _ (Le.le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Lt.lt_n_S.
    rewrite <- (PeanoNat.Nat.add_1_r v) in H2.
    apply (lifting_respects_occurance_r _ _ _ _ (Le.le_0_n _)) in H2.
    apply lift_lemma_Some in H1.
    exact (IHWF _ _ H1 _ H2).

    destruct slot.
    unfold has_type in H1; simpl in H1.
    subst t0.
    destruct v.
    exfalso; generalize H2; apply (lifting_destroys _ _ _ _ (Le.le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply PeanoNat.Nat.lt_0_succ.
    change (({str == t} :: ctx)[S slot] := t0) with ((lift_context ctx 0 1)[slot] := t0) in H1.
    destruct (ctx_var_lifted_repr _ _ _ _ _ H1).
    subst t0.
    destruct v.
    exfalso; generalize H2; apply (lifting_destroys _ _ _ _ (Le.le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Lt.lt_n_S.
    rewrite <- (PeanoNat.Nat.add_1_r v) in H2.
    apply (lifting_respects_occurance_r _ _ _ _ (Le.le_0_n _)) in H2.
    apply lift_lemma_Some in H1.
    exact (IHWF _ _ H1 _ H2).

    destruct slot.
    unfold has_type in H1; simpl in H1.
    subst t0.
    destruct v.
    exfalso; generalize H2; apply (lifting_destroys _ _ _ _ (Le.le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply PeanoNat.Nat.lt_0_succ.
    change (({str == t} :: ctx)[S slot] := t0) with ((lift_context ctx 0 1)[slot] := t0) in H1.
    destruct (ctx_var_lifted_repr _ _ _ _ _ H1).
    subst t0.
    destruct v.
    exfalso; generalize H2; apply (lifting_destroys _ _ _ _ (Le.le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Lt.lt_n_S.
    rewrite <- (PeanoNat.Nat.add_1_r v) in H2.
    apply (lifting_respects_occurance_r _ _ _ _ (Le.le_0_n _)) in H2.
    apply lift_lemma_Some in H1.
    exact (IHWF _ _ H1 _ H2).

    destruct slot.
    unfold has_type in H1; simpl in H1; easy.
    change ((push_dummy ctx)[S slot] := t) with ((lift_context ctx 0 1)[slot] := t) in H0.
    destruct (ctx_var_lifted_repr _ _ _ _ _ H0).
    subst t.
    destruct v.
    exfalso; generalize H1; apply (lifting_destroys _ _ _ _ (Le.le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Lt.lt_n_S.
    rewrite <- (PeanoNat.Nat.add_1_r v) in H1.
    apply (lifting_respects_occurance_r _ _ _ _ (Le.le_0_n _)) in H1.
    apply lift_lemma_Some in H0.
    exact (IHWF _ _ H0 _ H1).
Qed.

Lemma var_used_ineq : forall (l r : context) (v : nat),
    WF (l ++ r)%list ->
    var_used r v -> List.length l <= v
.
Proof.
    intros l r v H.
    generalize v; clear v; dependent induction H; intros.

    symmetry in x; apply List.app_eq_nil in x.
    destruct x; subst r; simpl in H0; easy.

    destruct l.
    simpl; apply le_0_n.
    simpl in x; simpl.
    unfold push_var in x; simpl in x.
    injection x; intros.
    destruct v.
    assert (var_used (l ++ r)%list 0).
    apply var_used_cases; tauto.
    exfalso; generalize H4.
    rewrite <- H2.
    unfold lift1_context.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S.
    rewrite <- (lower_context_length l 0 1).
    apply (IHWF _ (lower_context r 0 1)).
    rewrite <- lower_context_split.
    rewrite <- H2.
    unfold lift1_context; now rewrite lift_lower_context_destruct.
    elim (lifted_context_repr r 0 1).
    intros; subst r.
    rewrite lift_lower_context_destruct.
    apply (lifting_context_respects_occurance_r _ _ 1 _ (le_0_n _)).
    now rewrite PeanoNat.Nat.add_1_r.
    intros.
    destruct v0.
    exfalso; cut (var_used (lift1_context ctx) 0).
    unfold lift1_context.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite H2; apply var_used_cases; tauto.
    right; apply Le.le_n_S; apply Le.le_0_n.

    destruct l.
    simpl; apply le_0_n.
    simpl in x; simpl.
    unfold push_var in x; simpl in x.
    injection x; intros.
    destruct v.
    assert (var_used (l ++ r)%list 0).
    apply var_used_cases; tauto.
    exfalso; generalize H4.
    rewrite <- H2.
    unfold lift1_context.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S.
    rewrite <- (lower_context_length l 0 1).
    apply (IHWF _ (lower_context r 0 1)).
    rewrite <- lower_context_split.
    rewrite <- H2.
    unfold lift1_context; now rewrite lift_lower_context_destruct.
    elim (lifted_context_repr r 0 1).
    intros; subst r.
    rewrite lift_lower_context_destruct.
    apply (lifting_context_respects_occurance_r _ _ 1 _ (le_0_n _)).
    now rewrite PeanoNat.Nat.add_1_r.
    intros.
    destruct v0.
    exfalso; cut (var_used (lift1_context ctx) 0).
    unfold lift1_context.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite H2; apply var_used_cases; tauto.
    right; apply Le.le_n_S; apply Le.le_0_n.

    destruct l.
    simpl; apply le_0_n.
    simpl in x; simpl.
    unfold push_var in x; simpl in x.
    injection x; intros.
    destruct v.
    assert (var_used (l ++ r)%list 0).
    apply var_used_cases; tauto.
    exfalso; generalize H4.
    rewrite <- H2.
    unfold lift1_context.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S.
    rewrite <- (lower_context_length l 0 1).
    apply (IHWF _ (lower_context r 0 1)).
    rewrite <- lower_context_split.
    rewrite <- H2.
    unfold lift1_context; now rewrite lift_lower_context_destruct.
    elim (lifted_context_repr r 0 1).
    intros; subst r.
    rewrite lift_lower_context_destruct.
    apply (lifting_context_respects_occurance_r _ _ 1 _ (le_0_n _)).
    now rewrite PeanoNat.Nat.add_1_r.
    intros.
    destruct v0.
    exfalso; cut (var_used (lift1_context ctx) 0).
    unfold lift1_context.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite H2; apply var_used_cases; tauto.
    right; apply Le.le_n_S; apply Le.le_0_n.

    destruct l.
    simpl; apply le_0_n.
    simpl in x; simpl.
    unfold push_var in x; simpl in x.
    injection x; intros.
    destruct v.
    assert (var_used (l ++ r)%list 0).
    apply var_used_cases; tauto.
    exfalso; generalize H3.
    rewrite <- H1.
    unfold lift1_context.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S.
    rewrite <- (lower_context_length l 0 1).
    apply (IHWF _ (lower_context r 0 1)).
    rewrite <- lower_context_split.
    rewrite <- H1.
    unfold lift1_context; now rewrite lift_lower_context_destruct.
    elim (lifted_context_repr r 0 1).
    intros; subst r.
    rewrite lift_lower_context_destruct.
    apply (lifting_context_respects_occurance_r _ _ 1 _ (le_0_n _)).
    now rewrite PeanoNat.Nat.add_1_r.
    intros.
    destruct v0.
    exfalso; cut (var_used (lift1_context ctx) 0).
    unfold lift1_context.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite H1; apply var_used_cases; tauto.
    right; apply Le.le_n_S; apply Le.le_0_n.
Qed.

Lemma wf_ctx_no_zero : forall (ctx : context),
    WF ctx ->
    var_used ctx 0 ->
    False
.
Proof.
    intros ctx H; destruct H.
    easy.
    unfold push_var.
    unfold lift1_context; simpl.
    intro H1; destruct H1.
    generalize H1; apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    generalize H1; apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    unfold push_var.
    unfold lift1_context; simpl.
    intro H1; destruct H1.
    generalize H1; apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    generalize H1; apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    unfold push_var.
    unfold lift1_context; simpl.
    intro H1; destruct H1.
    generalize H1; apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    generalize H1; apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    unfold push_dummy.
    unfold lift1_context; simpl.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
Qed.
 
