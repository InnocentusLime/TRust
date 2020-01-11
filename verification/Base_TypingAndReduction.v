
Require List.
Require Import Term.
Require Import String.
Require Import Context.
Require Import Relations.
Require Import Base_Typing.
Require Import TermReduction.
Require Import Base_InversionOfTyping.
Require Import Base_ContextManipulation.

Ltac subst_lemma_abs_like_goal SUBST_VALUE_TYPING ARG_TYPE_TYPING BODY_TYPING ARG_NAME SUBST_VALUE_NAME LEFT_PART RIGHT_PART SUBST_VALUE SUBST_VALUE_TYPE ARG_TYPE TYPING_RULE :=
    assert (
        SUBST_VALUE_TYPING_FOR_BODY :
        (List.repeat None (List.length ({ARG_NAME == ARG_TYPE} :: LEFT_PART)) ++ None :: lift1_context RIGHT_PART)%list |- lift1 SUBST_VALUE := lift1 SUBST_VALUE_TYPE
    ) by (
        unfold push_var; simpl; unfold lift1_context; rewrite lift_context_length; unfold lift1;
        change (
            None :: List.repeat None (List.length LEFT_PART) ++ None :: lift_context RIGHT_PART 0 1
        )%list with (
            (None :: nil) ++ (List.repeat None (List.length LEFT_PART) ++ lift_context (None :: RIGHT_PART) 0 1)
        )%list;
        rewrite <- (lift_none 0 1); rewrite <- lift_context_split;
        apply ctx_append_left; 
        (
            (exact SUBST_VALUE_TYPING; simpl) || 
            (apply WF_dummy_assum; exact (typable_wf _ _ _ SUBST_VALUE_TYPING))
        )
    );
    apply TYPING_RULE;
    (
        exact (ARG_TYPE_TYPING _ _ _ _ _ (eq_refl _) SUBST_VALUE_TYPING) ||
        (
            rewrite PeanoNat.Nat.add_1_r;
            assert (
                PUSH_VAR_LENGTH_EQ :
                S (List.length LEFT_PART) = List.length ({ARG_NAME == ARG_TYPE} :: LEFT_PART)
            ) by (
                unfold push_var; simpl; unfold lift1_context; 
                rewrite lift_context_length; reflexivity
            );
            assert (
                PUSH_VAR_SUBST_SWAP_EQ :
                ({ ARG_NAME == subst ARG_TYPE (List.length LEFT_PART) SUBST_VALUE} :: subst_context (LEFT_PART ++ None :: RIGHT_PART)%list (List.length LEFT_PART) SUBST_VALUE)
                =
                subst_context ({ ARG_NAME == ARG_TYPE} :: (LEFT_PART ++ None :: RIGHT_PART)%list) (S (List.length LEFT_PART)) (lift1 SUBST_VALUE)
            ) by (
                unfold push_var; unfold lift1_context;
                change (
                    Some (ARG_NAME, subst ARG_TYPE (List.length LEFT_PART) SUBST_VALUE) ::
                    subst_context (LEFT_PART ++ None :: RIGHT_PART) (List.length LEFT_PART) SUBST_VALUE
                )%list with (
                    subst_context (Some (ARG_NAME, ARG_TYPE) :: (LEFT_PART ++ None :: RIGHT_PART)) (List.length LEFT_PART) SUBST_VALUE
                )%list;
                rewrite <- (lift_subst_context_unfold _ _ _ _ _ (le_0_n _));
                now rewrite PeanoNat.Nat.add_1_r
            );
            rewrite PUSH_VAR_SUBST_SWAP_EQ; rewrite PUSH_VAR_LENGTH_EQ;
            assert (
                PUSH_VAR_EQ : 
                (({ARG_NAME == ARG_TYPE} :: (LEFT_PART ++ None :: RIGHT_PART)%list) = ({ARG_NAME == ARG_TYPE} :: LEFT_PART) ++ (None :: lift1_context RIGHT_PART))%list
            ) by (
                unfold push_var; simpl; unfold lift1_context; now rewrite lift_context_split
            );
            rewrite PUSH_VAR_EQ;
            refine (BODY_TYPING SUBST_VALUE_NAME _ _ _ _ _ SUBST_VALUE_TYPING_FOR_BODY);
            unfold push_var; unfold lift1_context; repeat rewrite lift_context_split;
            simpl; rewrite lift_context_split; simpl; reflexivity
        )
    )
.

(*
    The substitution lemma. It's quite more complex in a dependent setting,
    but shortly speaking it states the following.

    Let `v` be certain variable which lies on bounds of context `ctx` and
    has type `Ntype` and name `str` associatd with it. Then `ctx` can be
    represented as:
        l ++ Some (srt, Ntype) :: r
    Where `|l| = v`. If we have a term `N` has type `Ntype` under the context
    `ctx` where `v` was set be a dummy variable and the whole `l` wasn't taken
    into account ((List.repeat None |l|) ++ None :: r |- N := Ntype)
    and some term `t` has type `type` under the context `ctx` 
    (l ++ Some (str, Ntype) :: r |- t := type), then we can set `v` to be a
    dummy vairable, substitute `v` with `N` in both leftover parts of `ctx`,
    the term and its type, the typing gets preserved.
    =========================================================================
    NOTE
    This the strongest statement I could come up with :p
*)
Lemma subst_lemma : forall (l r : context) (str : string) (t type N Ntype : term),
    (l ++ Some (str, Ntype) :: r)%list |- t := type ->
    (List.repeat None (List.length l) ++ None :: r)%list |- N := Ntype ->
    subst_context (l ++ None :: r)%list (List.length l) N |- subst t (List.length l) N := subst type (List.length l) N
.
Proof.
    (* Same tricks as before *)
    intros l r str t type N Ntype H.
    generalize H; clear H.
    set (ctx := (l ++ Some (str, Ntype) :: r)%list).
    assert (ctx = (l ++ Some (str, Ntype) :: r)%list).
    now subst ctx.
    intro H0.
    generalize str l r N Ntype H.
    generalize ctx t type H0.
    clear H0 H ctx t type N Ntype str l r.
    apply (
        typing_ind_mut
        (
            fun ctx t type proof => 
            forall str l r N Ntype,
            ctx = (l ++ Some (str, Ntype) :: r)%list ->
            (List.repeat None (List.length l) ++ None :: r)%list |- N := Ntype ->
            subst_context (l ++ None :: r)%list (List.length l) N |- subst t (List.length l) N := subst type (List.length l) N
        ) 
        (
            fun ctx _ => 
            forall str l r N Ntype,
            ctx = (l ++ Some (str, Ntype) :: r)%list ->
            (List.repeat None (List.length l) ++ None :: r)%list |- N := Ntype ->
            WF (subst_context (l ++ None :: r)%list (List.length l) N)
        )
    ).

    simpl; intros.
    subst ctx.
    apply TNat.
    now apply (H _ _ _ _ _ (eq_refl _) H1).

    simpl; intros.
    subst ctx.
    apply TNatO.
    now apply (H _ _ _ _ _ (eq_refl _) H1).

    simpl; intros.
    subst ctx.
    apply TNatSucc.
    now apply (H _ _ _ _ _ (eq_refl _) H1).

    simpl; intros.
    subst ctx.
    apply TNatRec.
    exact (H _ _ _ _ _ (eq_refl _) H4).
    exact (H0 _ _ _ _ _ (eq_refl _) H4).
    generalize (H1 _ _ _ _ _ (eq_refl _) H4).
    assert (IF_ELIM : PeanoNat.Nat.eqb (List.length l + 1) 0 = false).
    apply PeanoNat.Nat.eqb_neq; repeat rewrite PeanoNat.Nat.add_1_r; congruence.
    rewrite IF_ELIM; clear IF_ELIM.
    assert (IF_ELIM : PeanoNat.Nat.eqb (List.length l + 1 + 1) 1 = false).
    apply PeanoNat.Nat.eqb_neq; repeat rewrite PeanoNat.Nat.add_1_r; congruence.
    rewrite IF_ELIM; clear IF_ELIM.
    unfold lift1; rewrite <- PeanoNat.Nat.add_assoc; rewrite lift_merge; simpl.
    now repeat rewrite (fun d => lift_subst_unfold _ _ _ d (List.length l) (le_0_n _)).
    exact (H2 _ _ _ _ _ (eq_refl _) H4).

    simpl; intros.
    subst ctx.
    rewrite <- top_subst_subst_swap.
    apply (TApp _ str (subst domain (List.length l0) N)).
    exact (H _ _ _ _ _ (eq_refl _) H2).
    exact (H0 _ _ _ _ _ (eq_refl _) H2).

    simpl; intros; subst ctx.
    subst_lemma_abs_like_goal H2 H H0 str str0 l r N Ntype arg_type TAbsSmall.

    simpl; intros; subst ctx.
    subst_lemma_abs_like_goal H2 H H0 str str0 l r N Ntype arg_type (fun a b c d e => TAbsType a b c d e i).

    simpl; intros; subst ctx.
    subst_lemma_abs_like_goal H2 H H0 str str0 l r N Ntype arg_type TAbsProp.

    simpl; intros.
    subst ctx.
    case_eq (PeanoNat.Nat.eqb (List.length l) n); intros.
    assert (var_occurs Ntype (List.length l) -> False) by (
        change (None :: r)%list with (List.repeat None 1 ++ r)%list in H1;
        intro H2; generalize (ctx_none_seq_type _ _ _ _ _ H1 (List.length l) H2);
        rewrite List.repeat_length;
        rewrite PeanoNat.Nat.add_1_r;
        intro H3; generalize (H3 (le_n _)); clear H3;
        apply Lt.lt_irrefl
    ).
    apply PeanoNat.Nat.eqb_eq in H0; subst n.
    assert (t = Ntype) by (
        generalize h;
        unfold has_type;
        rewrite (List.nth_error_app2 _ _ (le_n _));
        rewrite PeanoNat.Nat.sub_diag;
        now simpl
    ).
    subst t.
    assert (subst_context r (List.length l) N = r).
    rewrite ctx_subst_erase.
    reflexivity.
    intro H3.
    change (Some (str, Ntype) :: r)%list with ((Some (str, Ntype) :: nil) ++ r)%list in w.
    rewrite List.app_assoc in w.
    apply (var_used_ineq _ _ _ w) in H3.
    rewrite List.app_length in H3; simpl in H3; rewrite PeanoNat.Nat.add_1_r in H3.
    generalize H3; apply Lt.lt_irrefl.
    rewrite ctx_subst_split.
    simpl.
    rewrite H0.
    apply replace_none_left.
    rewrite ctx_subst_length.
    rewrite (subst_erase _ _ _ H2).
    exact H1.
    rewrite <- H0.
    change (
        None :: subst_context r (List.length l) N
    )%list with (
        subst_context (None :: r) (List.length l) N
    )%list.
    rewrite <- ctx_subst_split.
    apply (H _ _ _ _ _ (eq_refl _)).
    exact H1.
    apply PeanoNat.Nat.eqb_neq in H0.
    unfold has_type in h.
    apply TVar.
    exact (H _ _ _ _ _ (eq_refl _) H1).
    unfold has_type.
    rewrite ctx_subst_split.
    destruct (PeanoNat.Nat.lt_ge_cases n (List.length l)).
    rewrite (List.nth_error_app1 _ _ H2) in h.
    rewrite List.nth_error_app1.
    apply subst_context_Some.
    exact h.
    now rewrite ctx_subst_length.
    rewrite (List.nth_error_app2 _ _ H2) in h.
    rewrite List.nth_error_app2.
    apply Lt.le_lt_or_eq in H2.
    destruct H2; try easy.
    rewrite ctx_subst_length.
    assert (n - List.length l <> 0).
    now apply PeanoNat.Nat.sub_gt.
    destruct (n - List.length l).
    congruence.
    simpl; simpl in h.
    apply subst_context_Some.
    exact h.
    rewrite ctx_subst_length.
    exact H2.

    simpl; intros.
    subst ctx.
    apply TSmallKind.
    exact (H _ _ _ _ _ (eq_refl _) H1).

    simpl; intros.
    subst ctx.
    apply TPropKind.
    exact (H _ _ _ _ _ (eq_refl _) H1).

    simpl; intros.
    subst ctx.
    apply TTypeKind.
    exact (H _ _ _ _ _ (eq_refl _) H1).

    simpl; intros.
    subst ctx.
    subst_lemma_abs_like_goal H2 H H0 str str0 l r N Ntype domain TForallType.

    simpl; intros.
    subst ctx.
    subst_lemma_abs_like_goal H2 H H0 str str0 l r N Ntype domain TForallPropSmall.

    simpl; intros.
    subst ctx.
    subst_lemma_abs_like_goal H2 H H0 str str0 l r N Ntype domain TForallPropProp.

    simpl; intros.
    subst ctx.
    subst_lemma_abs_like_goal H2 H H0 str str0 l r N Ntype domain (fun a b c d => TForallPropType a b c d i).

    simpl; intros.
    subst ctx.
    subst_lemma_abs_like_goal H2 H H0 str str0 l r N Ntype domain TForallSmallSmall.

    simpl; intros.
    subst ctx.
    subst_lemma_abs_like_goal H2 H H0 str str0 l r N Ntype domain TForallSmallProp.

    simpl; intros.
    subst ctx.
    apply JumpToTypeUniverseSmall.
    exact (H _ _ _ _ _ (eq_refl _) H1).

    simpl; intros.
    subst ctx.
    apply JumpToTypeUniverseProp.
    exact (H _ _ _ _ _ (eq_refl _) H1).

    simpl; intros.
    subst ctx.
    apply RaiseUniverse.
    exact (H _ _ _ _ _ (eq_refl _) H1).

    simpl; intros.
    subst ctx.
    apply (ConversionSmallL _ _ (subst type (List.length l) N)).
    exact (H _ _ _ _ _ (eq_refl _) H3).
    exact (H0 _ _ _ _ _ (eq_refl _) H3).
    now apply subst_respects_one_step.
    exact (H1 _ _ _ _ _ (eq_refl _) H3).

    simpl; intros.
    subst ctx.
    apply (ConversionPropL _ _ (subst type (List.length l) N)).
    exact (H _ _ _ _ _ (eq_refl _) H3).
    exact (H0 _ _ _ _ _ (eq_refl _) H3).
    now apply subst_respects_one_step.
    exact (H1 _ _ _ _ _ (eq_refl _) H3).

    simpl; intros.
    subst ctx.
    apply (ConversionTypeL _ _ (subst type (List.length l) N) _ i).
    exact (H _ _ _ _ _ (eq_refl _) H3).
    exact (H0 _ _ _ _ _ (eq_refl _) H3).
    now apply subst_respects_one_step.
    exact (H1 _ _ _ _ _ (eq_refl _) H3).

    simpl; intros.
    subst ctx.
    apply (ConversionSmallR _ _ (subst type (List.length l) N)).
    exact (H _ _ _ _ _ (eq_refl _) H3).
    exact (H0 _ _ _ _ _ (eq_refl _) H3).
    now apply subst_respects_one_step.
    exact (H1 _ _ _ _ _ (eq_refl _) H3).

    simpl; intros.
    subst ctx.
    apply (ConversionPropR _ _ (subst type (List.length l) N)).
    exact (H _ _ _ _ _ (eq_refl _) H3).
    exact (H0 _ _ _ _ _ (eq_refl _) H3).
    now apply subst_respects_one_step.
    exact (H1 _ _ _ _ _ (eq_refl _) H3).

    simpl; intros.
    subst ctx.
    apply (ConversionTypeR _ _ (subst type (List.length l) N) _ i).
    exact (H _ _ _ _ _ (eq_refl _) H3).
    exact (H0 _ _ _ _ _ (eq_refl _) H3).
    now apply subst_respects_one_step.
    exact (H1 _ _ _ _ _ (eq_refl _) H3).

    simpl; intros.
    subst ctx.
    apply (ConversionSmallRename _ _ (subst type (List.length l) N)).
    exact (H _ _ _ _ _ (eq_refl _) H3).
    exact (H0 _ _ _ _ _ (eq_refl _) H3).
    now apply subst_respects_alpha_eq.
    exact (H1 _ _ _ _ _ (eq_refl _) H3).

    simpl; intros.
    subst ctx.
    apply (ConversionPropRename _ _ (subst type (List.length l) N)).
    exact (H _ _ _ _ _ (eq_refl _) H3).
    exact (H0 _ _ _ _ _ (eq_refl _) H3).
    now apply subst_respects_alpha_eq.
    exact (H1 _ _ _ _ _ (eq_refl _) H3).

    simpl; intros.
    subst ctx.
    apply (ConversionTypeRename _ _ (subst type (List.length l) N) _ i).
    exact (H _ _ _ _ _ (eq_refl _) H3).
    exact (H0 _ _ _ _ _ (eq_refl _) H3).
    now apply subst_respects_alpha_eq.
    exact (H1 _ _ _ _ _ (eq_refl _) H3).

    simpl; intros.
    symmetry in H; apply List.app_eq_nil in H.
    destruct H.
    congruence.

    simpl; intros.
    destruct l.
    simpl in H1.
    unfold push_var in H1; unfold lift1_context in H1; simpl in H1.
    injection H1.
    intros; subst str0; subst Ntype; subst r.
    simpl.
    rewrite ctx_subst_erase.
    apply WF_dummy_assum.
    exact w.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    unfold push_var in H1; unfold lift1_context in H1; simpl in H1; injection H1.
    intros; subst o.
    simpl.
    elim (lifted_context_repr l 0 1).
    elim (lifted_context_repr r 0 1).
    intros; subst l; subst r.
    elim (lifted_repr N 0 1).
    intros; subst N.
    elim (lifted_repr Ntype 0 1); intros.
    subst Ntype.
    change (None :: lift_context x 0 1)%list with (lift_context (None :: x)%list 0 1).
    rewrite <- lift_context_split.
    rewrite lift_context_length.
    rewrite <- (PeanoNat.Nat.add_1_r (List.length x0)).
    rewrite (lift_subst_context_unfold _ _ _ _ _ (le_0_n _)).
    rewrite (lift_subst_unfold _ _ _ _ _ (le_0_n _)).
    apply WF_assum_small.
    change (Some (str0, lift x2 0 1) :: lift_context x 0 1)%list with (lift_context (Some (str0, x2) :: x)%list 0 1) in H3.
    rewrite <- lift_context_split in H3.
    apply lift_context_inj in H3.
    subst ctx.
    apply (H _ _ _ _ _ (eq_refl _)).
    simpl in H2.
    apply (cut_none_l _ _ _ 1) in H2.
    rewrite lower_context_split in H2.
    rewrite lower_none in H2.
    rewrite lift_context_length in H2.
    simpl in H2.
    rewrite lift_lower_context_destruct in H2.
    rewrite lift_lower_destruct in H2.
    rewrite lift_lower_destruct in H2.
    exact H2.
    fold subst.
    change (Some (str0, lift x2 0 1) :: lift_context x 0 1)%list with (lift_context (Some (str0, x2) :: x)%list 0 1) in H3.
    rewrite <- lift_context_split in H3.
    apply lift_context_inj in H3.
    subst ctx.
    apply (H0 _ _ _ _ _ (eq_refl _)).
    simpl in H2.
    apply (cut_none_l _ _ _ 1) in H2.
    rewrite lower_context_split in H2.
    rewrite lower_none in H2.
    rewrite lift_context_length in H2.
    simpl in H2.
    rewrite lift_lower_context_destruct in H2.
    rewrite lift_lower_destruct in H2.
    rewrite lift_lower_destruct in H2.
    exact H2.
    simpl in H2.
    generalize (ctx_none_seq_type nil _ _ Ntype 1 H2 _ H4).
    intro H5.
    simpl in H5.
    right; exact (H5 (le_0_n _)).
    intros.
    simpl in H2.
    generalize (ctx_none_seq_term nil _ _ Ntype 1 H2 _ H4).
    intro H5.
    simpl in H5.
    right; exact (H5 (le_0_n _)).
    intros.
    assert (var_used (l ++ Some (str0, Ntype) :: r)%list v).
    apply var_used_cases; simpl.
    right; right; exact H4.
    rewrite <- H3 in H5.
    destruct v.
    exfalso; generalize H5.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.
    intros.
    assert (var_used (l ++ Some (str0, Ntype) :: r)%list v).
    apply var_used_cases; simpl.
    left; exact H4.
    rewrite <- H3 in H5.
    destruct v.
    exfalso; generalize H5.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.

    simpl; intros.
    destruct l.
    simpl in H1.
    unfold push_var in H1; unfold lift1_context in H1; simpl in H1.
    injection H1.
    intros; subst str0; subst Ntype; subst r.
    simpl.
    rewrite ctx_subst_erase.
    apply WF_dummy_assum.
    exact w.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    unfold push_var in H1; unfold lift1_context in H1; simpl in H1; injection H1.
    intros; subst o.
    simpl.
    elim (lifted_context_repr l 0 1).
    elim (lifted_context_repr r 0 1).
    intros; subst l; subst r.
    elim (lifted_repr N 0 1).
    intros; subst N.
    elim (lifted_repr Ntype 0 1); intros.
    subst Ntype.
    change (None :: lift_context x 0 1)%list with (lift_context (None :: x)%list 0 1).
    rewrite <- lift_context_split.
    rewrite lift_context_length.
    rewrite <- (PeanoNat.Nat.add_1_r (List.length x0)).
    rewrite (lift_subst_context_unfold _ _ _ _ _ (le_0_n _)).
    rewrite (lift_subst_unfold _ _ _ _ _ (le_0_n _)).
    apply WF_assum_prop.
    change (Some (str0, lift x2 0 1) :: lift_context x 0 1)%list with (lift_context (Some (str0, x2) :: x)%list 0 1) in H3.
    rewrite <- lift_context_split in H3.
    apply lift_context_inj in H3.
    subst ctx.
    apply (H _ _ _ _ _ (eq_refl _)).
    simpl in H2.
    apply (cut_none_l _ _ _ 1) in H2.
    rewrite lower_context_split in H2.
    rewrite lower_none in H2.
    rewrite lift_context_length in H2.
    simpl in H2.
    rewrite lift_lower_context_destruct in H2.
    rewrite lift_lower_destruct in H2.
    rewrite lift_lower_destruct in H2.
    exact H2.
    fold subst.
    change (Some (str0, lift x2 0 1) :: lift_context x 0 1)%list with (lift_context (Some (str0, x2) :: x)%list 0 1) in H3.
    rewrite <- lift_context_split in H3.
    apply lift_context_inj in H3.
    subst ctx.
    apply (H0 _ _ _ _ _ (eq_refl _)).
    simpl in H2.
    apply (cut_none_l _ _ _ 1) in H2.
    rewrite lower_context_split in H2.
    rewrite lower_none in H2.
    rewrite lift_context_length in H2.
    simpl in H2.
    rewrite lift_lower_context_destruct in H2.
    rewrite lift_lower_destruct in H2.
    rewrite lift_lower_destruct in H2.
    exact H2.
    simpl in H2.
    generalize (ctx_none_seq_type nil _ _ Ntype 1 H2 _ H4).
    intro H5.
    simpl in H5.
    right; exact (H5 (le_0_n _)).
    intros.
    simpl in H2.
    generalize (ctx_none_seq_term nil _ _ Ntype 1 H2 _ H4).
    intro H5.
    simpl in H5.
    right; exact (H5 (le_0_n _)).
    intros.
    assert (var_used (l ++ Some (str0, Ntype) :: r)%list v).
    apply var_used_cases; simpl.
    right; right; exact H4.
    rewrite <- H3 in H5.
    destruct v.
    exfalso; generalize H5.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.
    intros.
    assert (var_used (l ++ Some (str0, Ntype) :: r)%list v).
    apply var_used_cases; simpl.
    left; exact H4.
    rewrite <- H3 in H5.
    destruct v.
    exfalso; generalize H5.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.

    simpl; intros.
    destruct l.
    simpl in H1.
    unfold push_var in H1; unfold lift1_context in H1; simpl in H1.
    injection H1.
    intros; subst str0; subst Ntype; subst r.
    simpl.
    rewrite ctx_subst_erase.
    apply WF_dummy_assum.
    exact w.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    unfold push_var in H1; unfold lift1_context in H1; simpl in H1; injection H1.
    intros; subst o.
    simpl.
    elim (lifted_context_repr l 0 1).
    elim (lifted_context_repr r 0 1).
    intros; subst l; subst r.
    elim (lifted_repr N 0 1).
    intros; subst N.
    elim (lifted_repr Ntype 0 1); intros.
    subst Ntype.
    change (None :: lift_context x 0 1)%list with (lift_context (None :: x)%list 0 1).
    rewrite <- lift_context_split.
    rewrite lift_context_length.
    rewrite <- (PeanoNat.Nat.add_1_r (List.length x0)).
    rewrite (lift_subst_context_unfold _ _ _ _ _ (le_0_n _)).
    rewrite (lift_subst_unfold _ _ _ _ _ (le_0_n _)).
    apply (WF_assum_type _ _ _ i).
    change (Some (str0, lift x2 0 1) :: lift_context x 0 1)%list with (lift_context (Some (str0, x2) :: x)%list 0 1) in H3.
    rewrite <- lift_context_split in H3.
    apply lift_context_inj in H3.
    subst ctx.
    apply (H _ _ _ _ _ (eq_refl _)).
    simpl in H2.
    apply (cut_none_l _ _ _ 1) in H2.
    rewrite lower_context_split in H2.
    rewrite lower_none in H2.
    rewrite lift_context_length in H2.
    simpl in H2.
    rewrite lift_lower_context_destruct in H2.
    rewrite lift_lower_destruct in H2.
    rewrite lift_lower_destruct in H2.
    exact H2.
    fold subst.
    change (Some (str0, lift x2 0 1) :: lift_context x 0 1)%list with (lift_context (Some (str0, x2) :: x)%list 0 1) in H3.
    rewrite <- lift_context_split in H3.
    apply lift_context_inj in H3.
    subst ctx.
    apply (H0 _ _ _ _ _ (eq_refl _)).
    simpl in H2.
    apply (cut_none_l _ _ _ 1) in H2.
    rewrite lower_context_split in H2.
    rewrite lower_none in H2.
    rewrite lift_context_length in H2.
    simpl in H2.
    rewrite lift_lower_context_destruct in H2.
    rewrite lift_lower_destruct in H2.
    rewrite lift_lower_destruct in H2.
    exact H2.
    simpl in H2.
    generalize (ctx_none_seq_type nil _ _ Ntype 1 H2 _ H4).
    intro H5.
    simpl in H5.
    right; exact (H5 (le_0_n _)).
    intros.
    simpl in H2.
    generalize (ctx_none_seq_term nil _ _ Ntype 1 H2 _ H4).
    intro H5.
    simpl in H5.
    right; exact (H5 (le_0_n _)).
    intros.
    assert (var_used (l ++ Some (str0, Ntype) :: r)%list v).
    apply var_used_cases; simpl.
    right; right; exact H4.
    rewrite <- H3 in H5.
    destruct v.
    exfalso; generalize H5.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.
    intros.
    assert (var_used (l ++ Some (str0, Ntype) :: r)%list v).
    apply var_used_cases; simpl.
    left; exact H4.
    rewrite <- H3 in H5.
    destruct v.
    exfalso; generalize H5.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.

    simpl; intros.
    unfold push_dummy in H0.
    destruct l.
    simpl in H0.
    congruence.
    simpl in H0; injection H0.
    intros; subst o.
    simpl.
    elim (lifted_context_repr l 0 1).
    elim (lifted_context_repr r 0 1).
    intros; subst l; subst r.
    change (None :: lift_context x 0 1)%list with (lift_context (None :: x) 0 1)%list.
    rewrite <- lift_context_split.
    elim (lifted_repr N 0 1).
    intros; subst N.
    rewrite lift_context_length; rewrite <- (PeanoNat.Nat.add_1_r (List.length x0)).
    rewrite (lift_subst_context_unfold _ _ _ _ _ (le_0_n _)).
    apply WF_dummy_assum.
    elim (lifted_repr Ntype 0 1).
    intros; subst Ntype.
    simpl in H1.
    apply (cut_none_l _ _ _ 1) in H1.
    rewrite lower_context_split in H1.
    rewrite lower_none in H1.
    rewrite lift_context_length in H1.
    simpl in H1.
    rewrite lift_lower_context_destruct in H1.
    rewrite lift_lower_destruct in H1.
    rewrite lift_lower_destruct in H1.
    change (Some (str, lift x2 0 1) :: lift_context x 0 1)%list with (lift_context (Some (str, x2) :: x)%list 0 1) in H2.
    rewrite <- lift_context_split in H2.
    apply lift_context_inj in H2.
    exact (H _ _ _ _ _ H2 H1).
    intros.
    generalize (ctx_none_seq_type nil _ _ Ntype 1 H1 _ H3).
    intro H4.
    simpl in H4.
    right; exact (H4 (le_0_n _)).
    intros.
    generalize (ctx_none_seq_term nil _ _ Ntype 1 H1 _ H3).
    intro H4.
    simpl in H4.
    right; exact (H4 (le_0_n _)).
    intros.
    assert (var_used (l ++ Some (str, Ntype) :: r)%list v).
    apply var_used_cases; simpl.
    right; right; exact H3.
    rewrite <- H2 in H4.
    destruct v.
    exfalso; generalize H4.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.
    intros.
    assert (var_used (l ++ Some (str, Ntype) :: r)%list v).
    apply var_used_cases; simpl.
    left; exact H3.
    rewrite <- H2 in H4.
    destruct v.
    exfalso; generalize H4.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.
Qed.

(*
    A shortcut for `top_subst`
*)
Corollary top_subst_lemma : forall (ctx : context) (str : string) (arg domain func range : term),
    ctx |- arg := domain ->
    ({str == domain} :: ctx) |- func := range ->
    ctx |- (top_subst func arg) := (top_subst range arg)
.
Proof.
    intros.
    unfold top_subst.
    unfold clean_after_subst.
    rewrite <- (lift_lower_context_destruct _ 0 1).
    apply cut_none_l.
    unfold lift1.
    simpl.
    rewrite <- (List.app_nil_l (None :: lift_context ctx 0 1)%list).
    assert (nil ++ None :: lift_context ctx 0 1 = subst_context (nil ++ None :: lift_context ctx 0 1) 0 (lift arg 0 1))%list.
    simpl.
    apply f_equal.
    rewrite ctx_subst_erase.
    reflexivity.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite H1.
    apply (subst_lemma nil _ str _ _ (lift arg 0 1) (lift domain 0 1)).
    simpl.
    exact H0.
    simpl.
    apply (ctx_append_left (None :: nil)%list).
    exact H.
    simpl.
    apply WF_dummy_assum.
    exact (typable_wf _ _ _ H).
Qed.

(*
    A type with type `small` can have any type `Type[i]`

    Shouldn't it be somwhere else?
*)
Lemma small_everywhere : forall (ctx : context) (t : term) (i : nat),
    ctx |- t := SmallKind ->
    ctx |- t := TypeKind i
.
Proof.
    intros.
    induction i.
    now apply JumpToTypeUniverseSmall.
    now apply RaiseUniverse.
Qed.

(*
    A type with type `prop` can have any type `Type[i]`

    Shouldn't it be somwhere else?
*)
Lemma prop_everywhere : forall (ctx : context) (t : term) (i : nat),
    ctx |- t := PropKind ->
    ctx |- t := TypeKind i
.
Proof.
    intros.
    induction i.
    now apply JumpToTypeUniverseProp.
    now apply RaiseUniverse.
Qed.

(*
    A type with type `Type[i]` can have any type `Type[j]` where `i <= j`
*)
Lemma typing_universe_inclusion_delta : forall (ctx : context) (t : term) (i di : nat),
    ctx |- t := TypeKind i ->
    ctx |- t := TypeKind (i + di)
.
Proof.
    intros.
    induction di.
    now rewrite PeanoNat.Nat.add_0_r.
    rewrite PeanoNat.Nat.add_succ_r.
    now apply RaiseUniverse.
Qed.

Corollary typing_universe_inclusion : forall (ctx : context) (t : term) (i j : nat),
    i <= j ->
    ctx |- t := TypeKind i ->
    ctx |- t := TypeKind j
.
Proof.
    intros.
    rewrite (Minus.le_plus_minus _ _ H).
    now apply typing_universe_inclusion_delta.
Qed.

(*
    Here we state that type of a term is typable and we also
    describe which types the type may have
*)
Lemma type_of_type : forall (ctx : context) (t type : term),
    ctx |- t := type ->
    (ctx |- type := SmallKind) \/ (ctx |- type := PropKind) \/ (exists (i : nat), ctx |- type := TypeKind i)
.
Proof.
    intros.
    induction H.

    right; right; exists 0.
    now apply TSmallKind.

    left.
    now apply TNat.

    left.
    apply TForallSmallSmall.
    now apply TNat.
    apply TNat.
    apply WF_assum_small.
    exact H.
    now apply TNat.

    left.
    change SmallKind with (top_subst SmallKind num).
    apply (TApp _ "_"%string Nat).
    exact H.
    exact H2.

    assert (ctx |- Forall str domain range := ?).
    unfold typable.
    destruct IHtyping1; try eauto.
    destruct H1; try eauto.
    destruct H1; eauto.
    apply forall_typing in H1.
    destruct H1.
    destruct H1.
    destruct H1.
    right; right.
    exists x.
    change (TypeKind x) with (top_subst (TypeKind x) r).
    now apply (top_subst_lemma _ str _ domain).
    destruct H1.
    destruct H1.
    apply (top_subst_lemma _ _ r) in H2.
    now eauto.
    exact H0.
    destruct H1.
    destruct H1.
    apply (top_subst_lemma _ _ _ _ _ _ H0) in H2.
    eauto.
    destruct H1.
    destruct H1.
    destruct H1.
    apply (top_subst_lemma _ _ _ _ _ _ H0) in H2.
    eauto.
    destruct H1.
    destruct H1.
    apply (top_subst_lemma _ _ _ _ _ _ H0) in H2.
    eauto.
    destruct H1.
    apply (top_subst_lemma _ _ _ _ _ _ H0) in H2.
    eauto.

    destruct IHtyping2.
    left.
    now apply TForallSmallSmall.
    destruct H1.
    right; left.
    now apply TForallPropSmall.
    destruct H1.
    apply (small_everywhere _ _ x) in H.
    right; right; exists x.
    now apply TForallType.

    destruct IHtyping2.
    apply (small_everywhere _ _ i) in H1.
    right; right; exists i.
    now apply TForallType.
    destruct H1.
    right; left.
    now apply (TForallPropType _ _ _ _ i).
    destruct H1.
    destruct (PeanoNat.Nat.le_ge_cases x i).
    right; right.
    exists i.
    apply (typing_universe_inclusion _ _ _ _ H2) in H1.
    now apply TForallType.
    right; right.
    exists x.
    apply (typing_universe_inclusion _ _ _ _ H2) in H.
    now apply TForallType.

    destruct IHtyping2.
    left.
    now apply TForallSmallProp.
    destruct H1.
    right; left.
    now apply TForallPropProp.
    destruct H1.
    apply (prop_everywhere _ _ x) in H.
    right; right; exists x.
    now apply TForallType.
    apply (type_of_fetched_var _ _ _ H H0).

    right; right; exists 1; now apply TTypeKind.

    right; right; exists 1; now apply TTypeKind.

    right; right; exists (S (S n)); now apply TTypeKind.

    right; right; exists (S universe); apply TTypeKind.
    exact (typable_wf _ _ _ H).

    right; right; exists 0; apply TPropKind.
    exact (typable_wf _ _ _ H).

    right; right; exists 0; apply TPropKind.
    exact (typable_wf _ _ _ H).

    right; right; exists 0; apply TPropKind.
    exact (typable_wf _ _ _ H).

    right; right; exists 0; apply TSmallKind.
    exact (typable_wf _ _ _ H).

    right; right; exists 0; apply TSmallKind.
    exact (typable_wf _ _ _ H).

    right; right; exists 1; apply TTypeKind.
    exact (typable_wf _ _ _ H).

    right; right; exists 1; apply TTypeKind.
    exact (typable_wf _ _ _ H).

    right; right; exists (S (S universe)); apply TTypeKind.
    exact (typable_wf _ _ _ H).

    left; exact H2.

    right; left; exact H2.

    right; right; exists i; exact H2.

    left; exact H2.

    right; left; exact H2.

    right; right; exists i; exact H2.

    left; exact H2.

    right; left; exact H2.

    right; right; exists i; exact H2.
Qed.

(*
    A lemma stating that renaming variables in a term won't change
    the type.
*)
Lemma alpha_preservation : forall (ctx : context) (t1 t2 type : term),
    ctx |- t1 := type ->
    t1 =a t2 ->
    ctx |- t2 := type
.
Proof.
    intros.
    generalize t2 H0; clear H0 t2.
    induction H.

    intros.
    destruct t2; try easy.
    now apply TNat.

    intros.
    destruct t2; try easy.
    now apply TNatO.

    intros.
    destruct t2; try easy.
    now apply TNatSucc.

    intros.
    destruct t2; try easy.
    simpl in H3.
    assert (WF ctx) by (exact (typable_wf _ _ _ H)).
    assert (WF ({"n"%string == Nat} :: ctx)) by (apply WF_assum_small; [> exact H4 | (apply TNat; exact H4)]).
    assert (WF ({"_"%string == (App (lift choice 0 1) (Var 0))} :: ({"n"%string == Nat} :: ctx))).
    apply WF_assum_small.
    exact H5.
    change SmallKind with (top_subst SmallKind (Var 0)).
    apply (TApp _ "_"%string Nat).
    change (Nat ===> SmallKind) with (lift (Nat ===> SmallKind) 0 1).
    apply (ctx_append_left (Some ("n"%string, Nat) :: nil)%list).
    exact H.
    exact H5.
    apply TVar.
    exact H5.
    unfold has_type; reflexivity.
    apply (ConversionSmallRename _ _ (App t2_1 t2_4)).
    apply TNatRec.
    now apply IHtyping1.
    apply (ConversionSmallRename _ _ (App choice NatO)).
    now apply IHtyping2.
    change SmallKind with (top_subst SmallKind NatO).
    apply (TApp _ "_"%string Nat).
    exact H.
    apply TNatO.
    exact H4.
    simpl; tauto.
    change SmallKind with (top_subst SmallKind NatO).
    apply (TApp _ "_"%string Nat).
    now apply IHtyping1.
    apply TNatO.
    exact H4.
    apply (
        ConversionSmallRename _ _ 
        (
            Forall "n"%string Nat 
            (
                App (lift choice 0 1) (Var 0) ===>
                App (lift choice 0 2) (App NatSucc (Var 1))
            )
        )
    ).
    now apply IHtyping3.
    apply TForallSmallSmall.
    apply TNat.
    exact H4.
    apply TForallSmallSmall.
    change SmallKind with (top_subst SmallKind (Var 0)).
    apply (TApp _ "_"%string Nat).
    change (Nat ===> SmallKind) with (lift (Nat ===> SmallKind) 0 1).
    apply (ctx_append_left (Some ("n"%string, Nat) :: nil)%list).
    exact H.
    simpl.
    exact H5.
    apply TVar.
    exact H5.
    reflexivity.
    change SmallKind with (top_subst SmallKind (App NatSucc (Var 1))).
    apply (TApp _ "_"%string Nat).
    unfold push_var; unfold lift1_context; simpl.
    rewrite lift_context_merge.
    rewrite lift_merge.
    simpl.
    change (Nat ===> SmallKind) with (lift (Nat ===> SmallKind) 0 2).
    apply (ctx_append_left (Some ("_"%string, App (lift choice 0 2) (Var 1)) :: Some ("n"%string, Nat) :: nil)%list).
    exact H.
    simpl.
    assert (2 = 1 + 1) by reflexivity.
    rewrite H7.
    rewrite <- lift_context_merge.
    rewrite <- lift_merge.
    exact H6.
    change Nat with (top_subst Nat (Var 1)).
    apply (TApp _ "_"%string Nat).
    apply TNatSucc.
    exact H6.
    apply TVar.
    exact H6.
    reflexivity.
    simpl.
    refine (conj I _).
    refine (conj _ _).
    refine (conj _ (eq_refl _)).
    apply lifting_respects_alpha_eq; tauto.
    refine (conj _ (conj I (eq_refl _))).
    apply lifting_respects_alpha_eq; tauto.
    apply TForallSmallSmall.
    apply TNat.
    exact H4.
    apply TForallSmallSmall.
    change SmallKind with (top_subst SmallKind (Var 0)).
    apply (TApp _ "_"%string Nat).
    change (Nat ===> SmallKind) with (lift (Nat ===> SmallKind) 0 1).
    apply (ctx_append_left (Some ("n"%string, Nat) :: nil)%list).
    now apply IHtyping1.
    simpl.
    exact H5.
    apply TVar.
    exact H5.
    reflexivity.
    change SmallKind with (top_subst SmallKind (App NatSucc (Var 1))).
    apply (TApp _ "_"%string Nat).
    unfold push_var; unfold lift1_context; simpl.
    rewrite lift_context_merge.
    rewrite lift_merge.
    simpl.
    change (Nat ===> SmallKind) with (lift (Nat ===> SmallKind) 0 2).
    apply (ctx_append_left (Some ("_"%string, App (lift t2_1 0 2) (Var 1)) :: Some ("n"%string, Nat) :: nil)%list).
    now apply IHtyping1.
    simpl.
    assert (2 = 1 + 1) by reflexivity.
    rewrite H7.
    rewrite <- lift_context_merge.
    rewrite <- lift_merge.
    change (
        App (lift (lift t2_1 0 1) 0 1) (Var 1)
    ) with (
        lift (App (lift t2_1 0 1) (Var 0)) 0 1
    ).
    change Nat with (lift (lift Nat 0 1) 0 1).
    change (
        Some ("n"%string, lift (lift Nat 0 1) 0 1) ::
        lift_context (lift_context ctx 0 1) 0 1
    )%list with (
        lift_context (lift_context (Some ("n"%string, Nat) :: ctx) 0 1) 0 1
    )%list.
    apply WF_assum_small.
    exact H5.
    change SmallKind with (top_subst SmallKind (Var 0)).
    apply (TApp _ "_"%string Nat).
    change (Nat ===> SmallKind) with (lift (Nat ===> SmallKind) 0 1).
    apply (ctx_append_left (Some ("n"%string, Nat) :: nil)%list).
    now apply IHtyping1.
    simpl.
    exact H5.
    apply TVar.
    exact H5.
    reflexivity.
    change Nat with (top_subst Nat (Var 1)).
    apply (TApp _ "_"%string Nat).
    apply TNatSucc.
    apply WF_assum_small.
    exact H5.
    change (top_subst Nat (Var 1)) with Nat.
    change SmallKind with (top_subst SmallKind (Var 0)).
    apply (TApp _ "_"%string Nat).
    change (Nat ===> SmallKind) with (lift (Nat ===> SmallKind) 0 1).
    apply (ctx_append_left (Some ("n"%string, Nat) :: nil)%list).
    now apply IHtyping1.
    exact H5.
    apply TVar.
    exact H5.
    reflexivity.
    apply TVar.
    apply WF_assum_small.
    exact H5.
    change SmallKind with (top_subst SmallKind (Var 0)).
    change (top_subst Nat (Var 1)) with Nat.
    apply (TApp _ "_"%string Nat).
    change (Nat ===> SmallKind) with (lift (Nat ===> SmallKind) 0 1).
    apply (ctx_append_left (Some ("n"%string, Nat) :: nil)%list).
    now apply IHtyping1.
    exact H5.
    apply TVar.
    exact H5.
    reflexivity.
    reflexivity.
    now apply IHtyping4.
    change SmallKind with (top_subst SmallKind t2_4).
    apply (TApp _ "_"%string Nat).
    now apply IHtyping1.
    now apply IHtyping4.
    simpl.
    split.
    symmetry; tauto.
    symmetry; tauto.
    change SmallKind with (top_subst SmallKind num).
    apply (TApp _ "_"%string Nat).
    exact H.
    exact H2.

    intros.
    destruct t2; try easy.
    simpl in H1.
    apply type_of_type in H.
    assert (ctx |- Forall str domain range := ?).
    destruct H.
    now exists SmallKind.
    destruct H.
    now exists PropKind.
    destruct H.
    now exists (TypeKind x).
    apply forall_typing in H2.
    destruct H2.
    destruct H2; destruct H2.
    apply (ConversionTypeRename _ _ (top_subst range t2_2) _ x).
    apply (TApp _ str domain).
    now apply IHtyping1.
    now apply IHtyping2.
    assert (H4 := IHtyping2 t2_2 (proj2 H1)).
    apply (top_subst_lemma _ _ _ _ _ _ H4) in H3.
    exact H3.
    unfold top_subst.
    apply lowering_respects_alpha_eq.
    apply subst_respects_alpha_eq.
    reflexivity.
    apply lifting_respects_alpha_eq; symmetry; tauto.
    apply (top_subst_lemma _ _ _ _ _ _ H0) in H3.
    exact H3.
    destruct H2.
    destruct H2.
    apply (ConversionPropRename _ _ (top_subst range t2_2)).
    apply (TApp _ str domain).
    now apply IHtyping1.
    now apply IHtyping2.
    assert (H4 := IHtyping2 t2_2 (proj2 H1)).
    apply (top_subst_lemma _ _ _ _ _ _ H4) in H3.
    exact H3.
    apply lowering_respects_alpha_eq.
    apply subst_respects_alpha_eq.
    reflexivity.
    apply lifting_respects_alpha_eq; symmetry; tauto.
    apply (top_subst_lemma _ _ _ _ _ _ H0) in H3.
    exact H3.
    destruct H2.
    
(*)
(*
    Finally we prove the preservation lemma:
    Let be `t1` have type `type` under context `ctx` and `t1` one-step reduces
    to `t2`, then `t2` has the same type under context `ctx`.
*)
Theorem preservation : forall (ctx : context) (t1 t2 type : term),
    ctx |- t1 := type ->
    t1 ->b t2 ->
    ctx |- t2 := type
.
Proof.
    intros ctx t1 t2 type H.
    generalize t2; clear t2.
    induction H.

    intros.
    exfalso.
    inversion H0.

    intros.
    exfalso.
    inversion H0.

    intros.
    exfalso.
    inversion H0.

    intros.
    inversion H3.
    subst t2; subst num0; subst step0; subst type_choice.
    subst terminate.
*)