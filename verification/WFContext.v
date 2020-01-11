Require Import Term.
Require Import Typing.

Theorem wf_var_cases : forall (ctx : context),
    WF ctx ->
    (
        forall (slot : nat) (t : term),
        ctx[slot] := t ->
        (lower_context (List.skipn (S slot) ctx) 0 (S slot) |- lower t 0 (S slot) := SmallKind) \/
        (lower_context (List.skipn (S slot) ctx) 0 (S slot) |- lower t 0 (S slot) := PropKind) \/
        (exists (i : nat), lower_context (List.skipn (S slot) ctx) 0 (S slot) |- lower t 0 (S slot) := TypeKind i)
    )
.
Proof.
    intros ctx H.
    induction H.

    intro slot; destruct slot; easy.

    intro slot; destruct slot.
    simpl.
    unfold has_type; simpl.
    intros; subst t0; unfold lift1_context; rewrite lift_lower_context_destruct.
    rewrite lift_lower_destruct.
    left; assumption.
    intro t0; change (({str == t} :: ctx)[S slot] := t0) with ((lift1_context ctx)[slot] := t0).
    change (List.skipn (S (S slot)) ({str == t} :: ctx)) with (List.skipn (S slot) (lift1_context ctx)).
    repeat rewrite <- (PeanoNat.Nat.add_1_l (S slot)).
    repeat rewrite <- lower_context_merge.
    repeat rewrite <- lower_skip_swap.
    unfold lift1_context.
    repeat rewrite lift_lower_context_destruct.
    intro H1.
    destruct (ctx_var_lifted_repr _ _ _ _ _ H1).
    subst t0.
    repeat rewrite <- lower_merge.
    repeat rewrite lift_lower_destruct. 
    rewrite lower_skip_swap.   
    apply IHWF.
    now apply lift_lemma_Some in H1.
    intros.
    destruct v.
    exfalso; generalize H2.
    apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S; apply le_0_n.
    unfold lift1_context.
    rewrite lift_skip_swap.
    intros.
    destruct v.
    exfalso; generalize H1.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S; apply le_0_n.

    intro slot; destruct slot.
    simpl.
    unfold has_type; simpl.
    intros; subst t0; unfold lift1_context; rewrite lift_lower_context_destruct.
    rewrite lift_lower_destruct.
    right; left; assumption.
    intro t0; change (({str == t} :: ctx)[S slot] := t0) with ((lift1_context ctx)[slot] := t0).
    change (List.skipn (S (S slot)) ({str == t} :: ctx)) with (List.skipn (S slot) (lift1_context ctx)).
    repeat rewrite <- (PeanoNat.Nat.add_1_l (S slot)).
    repeat rewrite <- lower_context_merge.
    repeat rewrite <- lower_skip_swap.
    unfold lift1_context.
    repeat rewrite lift_lower_context_destruct.
    intro H1.
    destruct (ctx_var_lifted_repr _ _ _ _ _ H1).
    subst t0.
    repeat rewrite <- lower_merge.
    repeat rewrite lift_lower_destruct. 
    rewrite lower_skip_swap. 
    apply IHWF.
    now apply lift_lemma_Some in H1.
    intros.
    destruct v.
    exfalso; generalize H2.
    apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S; apply le_0_n.
    unfold lift1_context.
    rewrite lift_skip_swap.
    intros.
    destruct v.
    exfalso; generalize H1.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S; apply le_0_n.

    intro slot; destruct slot.
    simpl.
    unfold has_type; simpl.
    intros; subst t0; unfold lift1_context; rewrite lift_lower_context_destruct.
    rewrite lift_lower_destruct.
    (*now exists (TypeKind i).*)
    right; right; exists i; assumption.
    intro t0; change (({str == t} :: ctx)[S slot] := t0) with ((lift1_context ctx)[slot] := t0).
    change (List.skipn (S (S slot)) ({str == t} :: ctx)) with (List.skipn (S slot) (lift1_context ctx)).
    repeat rewrite <- (PeanoNat.Nat.add_1_l (S slot)).
    repeat rewrite <- lower_context_merge.
    repeat rewrite <- lower_skip_swap.
    unfold lift1_context.
    repeat rewrite lift_lower_context_destruct.
    intro H1.
    destruct (ctx_var_lifted_repr _ _ _ _ _ H1).
    subst t0.
    repeat rewrite <- lower_merge.
    repeat rewrite lift_lower_destruct. 
    rewrite lower_skip_swap.    
    apply IHWF.
    now apply lift_lemma_Some in H1.
    intros.
    destruct v.
    exfalso; generalize H2.
    apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S; apply le_0_n.
    unfold lift1_context.
    rewrite lift_skip_swap.
    intros.
    destruct v.
    exfalso; generalize H1.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S; apply le_0_n.

    intro slot; destruct slot.
    unfold has_type; simpl.
    tauto.
    intro t; change ((push_dummy ctx)[S slot] := t) with ((lift1_context ctx)[slot] := t).
    change (List.skipn (S (S slot)) (push_dummy ctx)) with (List.skipn (S slot) (lift1_context ctx)).
    repeat rewrite <- (PeanoNat.Nat.add_1_l (S slot)).
    repeat rewrite <- lower_context_merge.
    repeat rewrite <- lower_skip_swap.
    unfold lift1_context.
    repeat rewrite lift_lower_context_destruct.
    intro H1.
    destruct (ctx_var_lifted_repr _ _ _ _ _ H1).
    subst t.
    repeat rewrite <- lower_merge.
    repeat rewrite lift_lower_destruct. 
    rewrite lower_skip_swap.   
    apply IHWF.
    now apply lift_lemma_Some in H1.
    intros.
    destruct v.
    exfalso; generalize H0.
    apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S; apply le_0_n.
    unfold lift1_context.
    rewrite lift_skip_swap.
    intros.
    destruct v.
    exfalso; generalize H0.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S; apply le_0_n.
Qed.

Corollary wf_extract : forall (ctx : context),
    WF ctx ->
    (
        forall (slot : nat) (t : term),
        ctx[slot] := t ->
        (lower_context (List.skipn (S slot) ctx) 0 (S slot) |- lower t 0 (S slot) := ?)
    )
.
Proof.
    intros.
    destruct (wf_var_cases _ H _ _ H0).
    now exists SmallKind.
    destruct H1.
    now exists PropKind.
    destruct H1.
    now exists (TypeKind x).
Qed.

