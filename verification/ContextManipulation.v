(*
    Theorems about weaking and strengthening contexts.
*)

Require List.
Require Import Term.
Require Import String.
Require Import Typing.
Require Import Relations.
Require Import WFContext.
Require Import ListLemmas.
Require Import TermReduction.

(*
    This is a module for abusing dependent
    induction which requires John Major inequality.

    NOTE: get rid of that
*)
Require Import Program.Equality.

Definition weak_normalization := forall (ctx : context) (t : term) (type : term), ctx |- t := type -> exists t' : term, irreducable t' /\ t ->>b t'.
Definition church_rosser := forall (ctx : context) (t t1 t2 : term) (type : term), ctx |- t := type -> irreducable t1 -> irreducable t2 -> t ->>b t1 -> t ->>b t2 -> t1 =a t2.

Ltac ctx_insert_abs_like_goal typing_rule wf_rule str domain l mid r IHtyping1 IHtyping2 := 
    simpl;
    apply typing_rule; (
        now apply IHtyping1
        || (
            assert (
                LIST_PUSH_VALUE_LEMMA : 
                ({str == lift domain (List.length l) (List.length mid)} :: (lift_context l (List.length l) (List.length mid) ++ mid ++ lift_context r (List.length l) (List.length mid))%list)
                =
                (lift_context ({str == domain} :: l) (S (List.length l)) (List.length mid) ++ (lift_context mid 0 1) ++ lift_context (lift_context r 0 1) (S (List.length l)) (List.length mid))%list
            ) by (
                unfold push_var;
                unfold lift1_context;
                simpl;
                rewrite <- (PeanoNat.Nat.add_1_r (List.length l));
                rewrite <- (PeanoNat.Nat.add_0_r (List.length l + 1));
                rewrite <- lift_swap_ex;
                repeat rewrite lift_context_split;
                repeat rewrite <- lift_context_swap;
                now repeat rewrite PeanoNat.Nat.add_0_r
            );
            assert (
                LIST_PUSH_LENGTH_LEMMA :
                S (List.length l)
                = 
                List.length ({str == domain} :: l)
            ) by (
                unfold push_var; simpl;
                unfold lift1_context; now rewrite lift_context_length
            );
            rewrite LIST_PUSH_LENGTH_LEMMA in LIST_PUSH_VALUE_LEMMA;
            rewrite PeanoNat.Nat.add_1_r; rewrite LIST_PUSH_LENGTH_LEMMA;
            rewrite <- (lift_context_length mid 0 1) in LIST_PUSH_VALUE_LEMMA at 4;
            rewrite <- (lift_context_length mid 0 1) in LIST_PUSH_VALUE_LEMMA at 4;
            rewrite LIST_PUSH_VALUE_LEMMA;
            rewrite <- (lift_context_length mid 0 1);
            apply IHtyping2; (
                (
                    unfold push_var; unfold lift1_context;
                    rewrite List.app_comm_cons; now repeat rewrite lift_context_split 
                )   
                ||
                (
                    rewrite <- LIST_PUSH_VALUE_LEMMA;
                    apply wf_rule; (easy || now apply IHtyping1)
                )
            )
        )
    )
.

(*
    The context can be easily weakened by adding some variables in
    the middle and lifting the left and right parts, term and types
    to preserve the correctness of dependent references.
*)
Lemma ctx_insert : forall (l mid r : context) (t type : term),
    (l ++ r)%list |- t := type ->
    WF (lift_context l (List.length l) (List.length mid) ++ mid ++ lift_context r (List.length l) (List.length mid))%list ->
    (lift_context l (List.length l) (List.length mid) ++ mid ++ lift_context r (List.length l) (List.length mid))%list |- lift t (List.length l) (List.length mid) := lift type (List.length l) (List.length mid)
.
Proof.
    intros l mid r t type H; generalize mid; clear mid; 
    dependent induction H; (intros; try (solve [simpl; now constructor])).

    simpl.
    apply TNatRec.
    now apply IHtyping1.
    now apply IHtyping2.
    generalize (IHtyping3 _ _ (JMeq_refl _) _ H3).
    simpl.
    assert (PeanoNat.Nat.ltb 0 (List.length l + 1) = true) by (rewrite PeanoNat.Nat.add_1_r; apply PeanoNat.Nat.ltb_lt; apply PeanoNat.Nat.lt_0_succ).
    rewrite H4; clear H4.
    assert (PeanoNat.Nat.ltb 1 (List.length l + 1 + 1) = true) by (repeat rewrite PeanoNat.Nat.add_1_r; apply PeanoNat.Nat.ltb_lt; apply Lt.lt_n_S; apply PeanoNat.Nat.lt_0_succ).
    rewrite H4; clear H4.
    rewrite <- PeanoNat.Nat.add_assoc; simpl.
    rewrite <- (PeanoNat.Nat.add_0_r (List.length l + 1)); rewrite <- (PeanoNat.Nat.add_0_r (List.length l + 2)).
    repeat rewrite <- lift_swap_ex.    
    repeat rewrite PeanoNat.Nat.add_0_r.
    easy.
    now apply IHtyping4.

    simpl.
    generalize (TApp _ _ _ _ _ _ (IHtyping1 _ _ (JMeq_refl _) _ H1) (IHtyping2 _ _ (JMeq_refl _) _ H1)).
    fold lift.
    assert (
        top_subst (lift range (List.length l + 1) (List.length mid)) (lift r0 (List.length l) (List.length mid)) 
        = 
        lift (top_subst range r0) (List.length l) (List.length mid)
    ).
    unfold top_subst.
    rewrite <- (PeanoNat.Nat.add_0_r (List.length l)) at 2.
    unfold lift1; rewrite lift_swap_ex.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite lift_subst_unfold_alt by (rewrite PeanoNat.Nat.add_1_r; unfold lt; apply Le.le_n_S; apply le_0_n).
    unfold clean_after_subst.
    set (T := subst range 0 (lift r0 0 1)).
    assert (forall v, var_occurs T v -> v < 0 \/ 0 + 1 <= v).
    simpl; intros; right.
    destruct v.
    exfalso; generalize H2; subst T; apply subst_destroys; apply (lifting_destroys _ _ _ _ (le_0_n _) (Le.le_n_S _ _ (le_n _))).
    apply Le.le_n_S; apply le_0_n.
    elim (lifted_repr T _ _ H2); clear H2.
    intros.
    rewrite H2.
    rewrite <- (PeanoNat.Nat.add_0_r (List.length l + 1)).
    rewrite <- lift_swap_ex.
    now (repeat rewrite lift_lower_destruct; rewrite PeanoNat.Nat.add_0_r).
    now rewrite H2.

    ctx_insert_abs_like_goal TAbsSmall WF_assum_small str arg_type l mid r IHtyping1 IHtyping2. 

    ctx_insert_abs_like_goal (fun a b c d e => TAbsType a b c d e i) (fun a b c => WF_assum_type a b c i) str arg_type l mid r IHtyping1 IHtyping2.

    ctx_insert_abs_like_goal TAbsProp WF_assum_prop str arg_type l mid r IHtyping1 IHtyping2. 

    simpl.
    destruct (PeanoNat.Nat.lt_ge_cases n (List.length l)).
    assert (PeanoNat.Nat.ltb n (List.length l) = true).
    now apply PeanoNat.Nat.ltb_lt.
    rewrite H3.
    apply TVar.
    exact H1.
    now apply insert_lemma_l.
    assert (PeanoNat.Nat.ltb n (List.length l) = false).
    now apply PeanoNat.Nat.ltb_ge.
    rewrite H3.
    apply TVar.
    exact H1.
    now apply insert_lemma_r.

    ctx_insert_abs_like_goal TForallType (fun a b c => WF_assum_type a b c universe) str domain l mid r IHtyping1 IHtyping2.

    ctx_insert_abs_like_goal TForallPropSmall WF_assum_small str domain l mid r IHtyping1 IHtyping2. 

    ctx_insert_abs_like_goal TForallPropProp WF_assum_prop str domain l mid r IHtyping1 IHtyping2. 

    ctx_insert_abs_like_goal (fun a b c d => TForallPropType a b c d i) (fun a b c => WF_assum_type a b c i) str domain l mid r IHtyping1 IHtyping2.

    ctx_insert_abs_like_goal TForallSmallSmall WF_assum_small str domain l mid r IHtyping1 IHtyping2. 

    ctx_insert_abs_like_goal TForallSmallProp WF_assum_prop str domain l mid r IHtyping1 IHtyping2.

    simpl.
    apply JumpToTypeUniverseSmall.
    now apply IHtyping.

    simpl.
    apply JumpToTypeUniverseProp.
    now apply IHtyping.

    simpl.
    apply RaiseUniverse.
    now apply IHtyping.

    apply (ConversionSmallL _ _ (lift type (List.length l) (List.length mid))).
    now apply IHtyping1.
    now apply IHtyping2.
    now apply lifting_respects_one_step.
    now apply IHtyping3.

    apply (ConversionPropL _ _ (lift type (List.length l) (List.length mid))).
    now apply IHtyping1.
    now apply IHtyping2.
    now apply lifting_respects_one_step.
    now apply IHtyping3.

    apply (ConversionTypeL _ _ (lift type (List.length l) (List.length mid)) _ i).
    now apply IHtyping1.
    now apply IHtyping2.
    now apply lifting_respects_one_step.
    now apply IHtyping3.

    apply (ConversionSmallR _ _ (lift type (List.length l) (List.length mid))).
    now apply IHtyping1.
    now apply IHtyping2.
    now apply lifting_respects_one_step.
    now apply IHtyping3.

    apply (ConversionPropR _ _ (lift type (List.length l) (List.length mid))).
    now apply IHtyping1.
    now apply IHtyping2.
    now apply lifting_respects_one_step.
    now apply IHtyping3.

    apply (ConversionTypeR _ _ (lift type (List.length l) (List.length mid)) _ i).
    now apply IHtyping1.
    now apply IHtyping2.
    now apply lifting_respects_one_step.
    now apply IHtyping3.

    apply (ConversionSmallRename _ _ (lift type (List.length l) (List.length mid))).
    now apply IHtyping1.
    now apply IHtyping2.
    now apply lifting_respects_alpha_eq.
    now apply IHtyping3.

    apply (ConversionPropRename _ _ (lift type (List.length l) (List.length mid))).
    now apply IHtyping1.
    now apply IHtyping2.
    now apply lifting_respects_alpha_eq.
    now apply IHtyping3.

    apply (ConversionTypeRename _ _ (lift type (List.length l) (List.length mid)) _ i).
    now apply IHtyping1.
    now apply IHtyping2.
    now apply lifting_respects_alpha_eq.
    now apply IHtyping3.
Qed.

(*
    The theorem above can be used to append variables on the left.
    It's just a special case when the left part of the context is
    empty.
*)
Corollary ctx_append_left : forall (l r : context) (t type : term),
    r |- t := type ->
    WF (l ++ lift_context r 0 (List.length l))%list ->
    (l ++ lift_context r 0 (List.length l))%list |- lift t 0 (List.length l) := lift type 0 (List.length l)
.
Proof.
    intros l r t type.
    rewrite <- (List.app_nil_l (l ++ lift_context r _ _)).
    rewrite <- (List.app_nil_l l) at 1.
    change 0 with (@List.length (option (string * term)) nil).
    change nil with (lift_context nil (@List.length (option (string * term)) nil) (List.length l)) at 4.
    change nil with (lift_context nil (@List.length (option (string * term)) nil) (List.length l)) at 2.
    apply (ctx_insert nil l r).
Qed.

(*
    A basic theorem stating that in every well-formed context
    type of each variable is typable.
*)
Theorem type_of_fetched_var : forall (ctx : context) (slot : nat) (t : term),
    WF ctx ->
    ctx[slot] := t ->
    (ctx |- t := SmallKind) \/
    (ctx |- t := PropKind) \/
    (exists (i : nat), ctx |- t := TypeKind i)
.
Proof.
    intros.
    assert (S slot <= List.length ctx) by (
        change (S slot <= List.length ctx) with (slot < List.length ctx);
        apply List.nth_error_Some;
        unfold has_type in H0;
        intro H1; now rewrite H1 in H0
    ).
    apply List.firstn_length_le in H1.
    assert (H2 := list_firstn_skipn_eqn _ ctx slot).
    assert (H3 := wf_var_cases ctx H slot t H0).
    destruct H3.

    left.
    apply (ctx_append_left (List.firstn (S slot) ctx)) in H3.
    rewrite H1 in H3.
    rewrite lower_lift_context_destruct in H3 by (intros; simpl; rewrite <- H1; rewrite H2 in H; apply (var_used_ineq _ (List.skipn (S slot) ctx) _ H H4)).
    rewrite lower_lift_destruct in H3 by (simpl; intros; exact (wf_ctx_slot_lt_var ctx H slot t H0 _ H4)).
    rewrite <- H2 in H3; simpl in H3.
    exact H3.
    rewrite H1.
    rewrite lower_lift_context_destruct by (intros; simpl; rewrite <- H1; rewrite H2 in H; apply (var_used_ineq _ (List.skipn (S slot) ctx) _ H H4)).
    now rewrite <- H2.

    right; destruct H3.

    left.
    apply (ctx_append_left (List.firstn (S slot) ctx)) in H3.
    rewrite H1 in H3.
    rewrite lower_lift_context_destruct in H3 by (intros; simpl; rewrite <- H1; rewrite H2 in H; apply (var_used_ineq _ (List.skipn (S slot) ctx) _ H H4)).
    rewrite lower_lift_destruct in H3 by (simpl; intros; exact (wf_ctx_slot_lt_var ctx H slot t H0 _ H4)).
    rewrite <- H2 in H3; simpl in H3.
    exact H3.
    rewrite H1.
    rewrite lower_lift_context_destruct by (intros; simpl; rewrite <- H1; rewrite H2 in H; apply (var_used_ineq _ (List.skipn (S slot) ctx) _ H H4)).
    now rewrite <- H2.

    right.
    destruct H3.
    exists x.
    apply (ctx_append_left (List.firstn (S slot) ctx)) in H3.
    rewrite H1 in H3.
    rewrite lower_lift_context_destruct in H3 by (intros; simpl; rewrite <- H1; rewrite H2 in H; apply (var_used_ineq _ (List.skipn (S slot) ctx) _ H H4)).
    rewrite lower_lift_destruct in H3 by (simpl; intros; exact (wf_ctx_slot_lt_var ctx H slot t H0 _ H4)).
    rewrite <- H2 in H3; simpl in H3.
    exact H3.
    rewrite H1.
    rewrite lower_lift_context_destruct by (intros; simpl; rewrite <- H1; rewrite H2 in H; apply (var_used_ineq _ (List.skipn (S slot) ctx) _ H H4)).
    now rewrite <- H2.
Qed.

Corollary wf_fetched_var : forall (ctx : context) (slot : nat) (t : term),
    WF ctx ->
    ctx[slot] := t ->
    ctx |- t := ?
.
Proof.
    intros.
    destruct (type_of_fetched_var _ _ _ H H0).
    now exists SmallKind.
    destruct H1.
    now exists PropKind.
    destruct H1.
    now exists (TypeKind x).
Qed.

(*
    Another basic theorem stating that a if a var occurs
    in a typable term, then it has a type associated with it.
*)
Theorem typable_occurs : forall (ctx : context) (t type : term),
    ctx |- t := type ->
    (forall v, var_occurs t v -> ctx[v] := ?! -> False)
.
Proof.
    intros ctx t type H.
    induction H; try easy.

    simpl; intros.
    destruct H3.
    exact (IHtyping1 v H3 H4).
    destruct H3.
    exact (IHtyping2 v H3 H4).
    destruct H3.
    exact (IHtyping3 v H3 H4).
    exact (IHtyping4 v H3 H4).

    simpl; intros.
    destruct H1.
    exact (IHtyping1 v H1 H2).
    exact (IHtyping2 v H1 H2).

    simpl; intros.
    destruct H1.
    exact (IHtyping1 v H1 H2).
    set (H3 := IHtyping2 (S v) H1).
    change (({ str == arg_type }::ctx)[S v] := ?!) with ((lift1_context ctx)[v] := ?!) in H3.
    unfold lift1_context in H3; rewrite <- lift_lemma_None in H3.
    easy.

    simpl; intros.
    destruct H1.
    exact (IHtyping1 v H1 H2).
    set (H3 := IHtyping2 (S v) H1).
    change (({ str == arg_type }::ctx)[S v] := ?!) with ((lift1_context ctx)[v] := ?!) in H3.
    unfold lift1_context in H3; rewrite <- lift_lemma_None in H3.
    easy.

    simpl; intros.
    destruct H1.
    exact (IHtyping1 v H1 H2).
    set (H3 := IHtyping2 (S v) H1).
    change (({ str == arg_type }::ctx)[S v] := ?!) with ((lift1_context ctx)[v] := ?!) in H3.
    unfold lift1_context in H3; rewrite <- lift_lemma_None in H3.
    easy.

    simpl; intros; subst n.
    apply (has_type_contradict _ _ _ H0 H2).

    simpl; intros.
    destruct H1.
    exact (IHtyping1 v H1 H2).
    set (H3 := IHtyping2 (S v) H1).
    change (({ str == domain }::ctx)[S v] := ?!) with ((lift1_context ctx)[v] := ?!) in H3.
    unfold lift1_context in H3; rewrite <- lift_lemma_None in H3.
    easy.

    simpl; intros.
    destruct H1.
    exact (IHtyping1 v H1 H2).
    set (H3 := IHtyping2 (S v) H1).
    change (({ str == domain }::ctx)[S v] := ?!) with ((lift1_context ctx)[v] := ?!) in H3.
    unfold lift1_context in H3; rewrite <- lift_lemma_None in H3.
    easy.

    simpl; intros.
    destruct H1.
    exact (IHtyping1 v H1 H2).
    set (H3 := IHtyping2 (S v) H1).
    change (({ str == domain }::ctx)[S v] := ?!) with ((lift1_context ctx)[v] := ?!) in H3.
    unfold lift1_context in H3; rewrite <- lift_lemma_None in H3.
    easy.

    simpl; intros.
    destruct H1.
    exact (IHtyping1 v H1 H2).
    set (H3 := IHtyping2 (S v) H1).
    change (({ str == domain }::ctx)[S v] := ?!) with ((lift1_context ctx)[v] := ?!) in H3.
    unfold lift1_context in H3; rewrite <- lift_lemma_None in H3.
    easy.

    simpl; intros.
    destruct H1.
    exact (IHtyping1 v H1 H2).
    set (H3 := IHtyping2 (S v) H1).
    change (({ str == domain }::ctx)[S v] := ?!) with ((lift1_context ctx)[v] := ?!) in H3.
    unfold lift1_context in H3; rewrite <- lift_lemma_None in H3.
    easy.

    simpl; intros.
    destruct H1.
    exact (IHtyping1 v H1 H2).
    set (H3 := IHtyping2 (S v) H1).
    change (({ str == domain }::ctx)[S v] := ?!) with ((lift1_context ctx)[v] := ?!) in H3.
    unfold lift1_context in H3; rewrite <- lift_lemma_None in H3.
    easy.
Qed.

(*
    Finally we state that a variable which is used in a 
    well formed context (occurs inside one of the types associated to a variable)
    must have a type associated with it.
*)
Theorem wf_used_var : forall (ctx : context) (v : nat),
    WF ctx ->
    var_used ctx v ->
    ctx[v] := ?! ->
    False
.
Proof.
    intros ctx v H.
    generalize v; clear v.
    induction H; intro v.
    easy.

    simpl.
    intro H1.
    destruct H1.
    destruct v.
    intros; generalize H1; apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite <- (PeanoNat.Nat.add_1_r v) in H1.
    change (({ str == t } :: ctx)[S v] := ?!) with ((lift_context ctx 0 1)[v] := ?!).
    apply (lifting_respects_occurance_r _ _ _ _ (le_0_n _)) in H1.
    intro H2.
    apply lift_lemma_None in H2.
    exact (typable_occurs _ _ _ H0 _ H1 H2).
    unfold lift1_context in H1.
    destruct v.
    exfalso; generalize H1.
    apply (lifting_context_destroys ctx _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite <- (PeanoNat.Nat.add_1_r v) in H1.
    apply (var_used_lift_r ctx _ _ _ (le_0_n _)) in H1.
    change (({ str == t } :: ctx)[S v] := ?!) with ((lift_context ctx 0 1)[v] := ?!).
    rewrite <- lift_lemma_None.
    now apply IHWF.

    simpl.
    intro H1.
    destruct H1.
    destruct v.
    intros; generalize H1; apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite <- (PeanoNat.Nat.add_1_r v) in H1.
    change (({ str == t } :: ctx)[S v] := ?!) with ((lift_context ctx 0 1)[v] := ?!).
    apply (lifting_respects_occurance_r _ _ _ _ (le_0_n _)) in H1.
    intro H2.
    apply lift_lemma_None in H2.
    exact (typable_occurs _ _ _ H0 _ H1 H2).
    unfold lift1_context in H1.
    destruct v.
    exfalso; generalize H1.
    apply (lifting_context_destroys ctx _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite <- (PeanoNat.Nat.add_1_r v) in H1.
    apply (var_used_lift_r ctx _ _ _ (le_0_n _)) in H1.
    change (({ str == t } :: ctx)[S v] := ?!) with ((lift_context ctx 0 1)[v] := ?!).
    rewrite <- lift_lemma_None.
    now apply IHWF.

    simpl.
    intro H1.
    destruct H1.
    destruct v.
    intros; generalize H1; apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite <- (PeanoNat.Nat.add_1_r v) in H1.
    change (({ str == t } :: ctx)[S v] := ?!) with ((lift_context ctx 0 1)[v] := ?!).
    apply (lifting_respects_occurance_r _ _ _ _ (le_0_n _)) in H1.
    intro H2.
    apply lift_lemma_None in H2.
    exact (typable_occurs _ _ _ H0 _ H1 H2).
    unfold lift1_context in H1.
    destruct v.
    exfalso; generalize H1.
    apply (lifting_context_destroys ctx _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite <- (PeanoNat.Nat.add_1_r v) in H1.
    apply (var_used_lift_r ctx _ _ _ (le_0_n _)) in H1.
    change (({ str == t } :: ctx)[S v] := ?!) with ((lift_context ctx 0 1)[v] := ?!).
    rewrite <- lift_lemma_None.
    now apply IHWF.

    simpl.
    intro H1.
    destruct v.
    exfalso; generalize H1.
    apply (lifting_context_destroys ctx _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite <- (PeanoNat.Nat.add_1_r v) in H1.
    apply (var_used_lift_r ctx _ _ _ (le_0_n _)) in H1.
    change ((push_dummy ctx)[S v] := ?!) with ((lift_context ctx 0 1)[v] := ?!).
    rewrite <- lift_lemma_None.
    now apply IHWF.
Qed.

Ltac ctx_none_seq_term_abs_like_goal var_ineq occurs_hyp str domain l mid r IHtyping1 IHtyping2 :=
    simpl in occurs_hyp;
    destruct occurs_hyp as [occurs_hyp | occurs_hyp];
    (
        exact (IHtyping1 l r mid (JMeq_refl _) _ occurs_hyp var_ineq) 
    ||
        (
            apply Le.le_S_n; apply Le.le_n_S in var_ineq;
            assert (
                PUSH_VAR_EQ_LEMMA :
                    push_var (l ++ List.repeat None mid ++ r)%list str domain 
                    ~= 
                    (push_var l str domain ++ List.repeat None mid ++ lift1_context r)%list
            ) by (
                unfold push_var; unfold lift1_context;
                simpl; repeat rewrite lift_context_split; 
                rewrite lift_none; reflexivity
            );
            assert (
                PUSH_VAR_LENG_LEMMA :
                    List.length (push_var l str domain)
                    =
                    S (List.length l)
            ) by (
                unfold push_var; unfold lift1_context; 
                rewrite lift_context_length; simpl;
                reflexivity
            );
            generalize (IHtyping2 (push_var l str domain) (lift1_context r) mid PUSH_VAR_EQ_LEMMA _ occurs_hyp);
            rewrite PUSH_VAR_LENG_LEMMA;
            tauto
        )
    )
.

(*
    A lemma stating that a typable term can't reference dummy
    variables.
*)
Lemma ctx_none_seq_term : forall (l r : context) (t type : term) (mid : nat),
    (l ++ (List.repeat None mid) ++ r)%list |- t := type ->
    (forall v, var_occurs t v -> List.length l <= v -> List.length l + mid <= v)
.
Proof.
    intros.
    dependent induction H; try easy.

    simpl in H3.
    destruct H3.
    now apply (IHtyping1 l r).
    destruct H3.
    now apply (IHtyping2 l r).
    destruct H3.
    now apply (IHtyping3 l r).
    now apply (IHtyping4 l r).

    simpl in H1.
    destruct H1.
    now apply (IHtyping1 l r).
    now apply (IHtyping2 l r).

    ctx_none_seq_term_abs_like_goal H2 H1 str arg_type l mid r IHtyping1 IHtyping2.

    ctx_none_seq_term_abs_like_goal H2 H1 str arg_type l mid r IHtyping1 IHtyping2.

    ctx_none_seq_term_abs_like_goal H2 H1 str arg_type l mid r IHtyping1 IHtyping2.

    simpl in H1; subst n.
    destruct (PeanoNat.Nat.lt_ge_cases v ((List.length l) + mid)).
    unfold has_type in H0.
    rewrite (List.nth_error_app2 _ _ H2) in H0.
    rewrite List.nth_error_app1 in H0.
    case_eq (List.nth_error (List.repeat (@None (string * term)) mid) (v - List.length l)).
    intros.
    destruct o.
    destruct p.
    apply List.nth_error_In in H3.
    apply List.repeat_spec in H3.
    discriminate H3.
    now rewrite H3 in H0.
    intro H3.
    now rewrite H3 in H0.
    rewrite List.repeat_length.
    apply (PeanoNat.Nat.add_lt_mono_r _ _ (List.length l)).
    rewrite PeanoNat.Nat.sub_add; try easy.
    now rewrite PeanoNat.Nat.add_comm.
    exact H1.

    ctx_none_seq_term_abs_like_goal H2 H1 str domain l mid r IHtyping1 IHtyping2.

    ctx_none_seq_term_abs_like_goal H2 H1 str domain l mid r IHtyping1 IHtyping2.

    ctx_none_seq_term_abs_like_goal H2 H1 str domain l mid r IHtyping1 IHtyping2.

    ctx_none_seq_term_abs_like_goal H2 H1 str domain l mid r IHtyping1 IHtyping2.

    ctx_none_seq_term_abs_like_goal H2 H1 str domain l mid r IHtyping1 IHtyping2.

    ctx_none_seq_term_abs_like_goal H2 H1 str domain l mid r IHtyping1 IHtyping2.

    now apply (IHtyping l r).

    now apply (IHtyping l r).

    now apply (IHtyping l r).
    now apply (IHtyping1 l r).

    now apply (IHtyping1 l r).
    
    now apply (IHtyping1 l r).

    now apply (IHtyping1 l r).

    now apply (IHtyping1 l r).
    
    now apply (IHtyping1 l r).

    now apply (IHtyping1 l r).

    now apply (IHtyping1 l r).
    
    now apply (IHtyping1 l r).
Qed.

Ltac ctx_none_seq_type_abs_line_goal domain_typing var_ineq occurs_hyp str domain l mid r IHtyping1 IHtyping2 :=
    simpl in occurs_hyp;
    destruct occurs_hyp as [occurs_hyp | occurs_hyp];
    (
        exact (ctx_none_seq_term _ _ _ _ _ domain_typing _ occurs_hyp var_ineq)
        ||
        (
            assert (
                PUSH_VAR_EQ_LEMMA :
                    push_var (l ++ List.repeat None mid ++ r)%list str domain 
                    ~= 
                    (push_var l str domain ++ List.repeat None mid ++ lift1_context r)%list
            ) by (
                unfold push_var; unfold lift1_context;
                simpl; repeat rewrite lift_context_split; 
                rewrite lift_none; reflexivity
            );
            assert (
                PUSH_VAR_LENG_LEMMA :
                    List.length (push_var l str domain)
                    =
                    S (List.length l)
            ) by (
                unfold push_var; unfold lift1_context; 
                rewrite lift_context_length; simpl;
                reflexivity
            );
            apply Le.le_S_n;
            generalize (IHtyping2 ({str == domain}::l) (lift1_context r) mid PUSH_VAR_EQ_LEMMA _ occurs_hyp);
            repeat rewrite PUSH_VAR_LENG_LEMMA;
            apply Le.le_n_S in var_ineq;
            tauto
        )
    )
.

(*
    A lemma stating that the type of a typable term can't
    reference dummy variables either.
*)
Lemma ctx_none_seq_type : forall (l r : context) (t type : term) (mid : nat),
    (l ++ (List.repeat None mid) ++ r)%list |- t := type ->
    (forall v, var_occurs type v -> List.length l <= v -> List.length l + mid <= v)
.
Proof.
    intros.
    dependent induction H; try easy.

    simpl in H0.
    tauto.

    simpl in H3.
    destruct H3.
    exact (ctx_none_seq_term _ _ _ _ _ H _ H3 H4).
    exact (ctx_none_seq_term _ _ _ _ _ H2 _ H3 H4).

    unfold top_subst in H1.
    unfold clean_after_subst in H1.
    apply lowering_and_occurance_alt in H1.
    destruct H1.
    apply subst_respects_occurance in H1.
    destruct H1.
    destruct H1.
    unfold lift1 in H1.
    apply (lifting_respects_occurance_r _ _ _ _ (le_0_n _)) in H1.
    exact (ctx_none_seq_term _ _ _ _ _ H0 _ H1 H2).
    destruct H1.
    assert (var_occurs (Forall str domain range) v).
    simpl.
    right; now rewrite PeanoNat.Nat.add_1_r in H1.
    exact (IHtyping1 l r mid (JMeq_refl _) _ H4 H2).
    exfalso; exact (PeanoNat.Nat.nlt_0_r _ H1).
    intros.
    destruct v'.
    exfalso; generalize H3.
    unfold lift1; apply subst_destroys; apply lifting_destroys.
    apply le_0_n.
    constructor.
    simpl; apply Le.le_n_S; apply le_0_n.

    ctx_none_seq_type_abs_line_goal H H2 H1 str arg_type l mid r IHtyping1 IHtyping2.

    ctx_none_seq_type_abs_line_goal H H2 H1 str arg_type l mid r IHtyping1 IHtyping2.

    ctx_none_seq_type_abs_line_goal H H2 H1 str arg_type l mid r IHtyping1 IHtyping2.

    apply wf_fetched_var in H0.
    destruct H0.
    exact (ctx_none_seq_term _ _ _ _ _ H0 _ H1 H2).
    exact H.

    exact (ctx_none_seq_term _ _ _ _ _ H2 _ H3 H4).

    exact (ctx_none_seq_term _ _ _ _ _ H2 _ H3 H4).

    exact (ctx_none_seq_term _ _ _ _ _ H2 _ H3 H4).

    exact (ctx_none_seq_term _ _ _ _ _ H2 _ H3 H4).

    exact (ctx_none_seq_term _ _ _ _ _ H2 _ H3 H4).

    exact (ctx_none_seq_term _ _ _ _ _ H2 _ H3 H4).

    exact (ctx_none_seq_term _ _ _ _ _ H2 _ H3 H4).

    exact (ctx_none_seq_term _ _ _ _ _ H2 _ H3 H4).

    exact (ctx_none_seq_term _ _ _ _ _ H2 _ H3 H4).
Qed.

(*
    Finally we state that types which are associated to vars
    in a well-formed context can't reference dummy variables.
*)
Lemma ctx_none_seq_ctx : forall (l r : context) (mid : nat),
    WF (l ++ (List.repeat None mid) ++ r)%list ->
    (forall v, var_used (l ++ (List.repeat None mid) ++ r)%list v -> List.length l <= v -> List.length l + mid <= v)
.
Proof.
    intros.
    destruct (PeanoNat.Nat.lt_ge_cases v (List.length l + mid)).
    assert ((l ++ (List.repeat None mid) ++ r)%list[v] := ?!).
    unfold has_no_type.
    rewrite (List.nth_error_app2 _ _ H1).
    rewrite List.nth_error_app1.
    case_eq (List.nth_error (List.repeat (@None (string * term)) mid) (v - List.length l)); intros.
    apply List.nth_error_In in H3.
    apply List.repeat_spec in H3.
    subst o.
    exact I.
    exact I.
    apply (PeanoNat.Nat.add_lt_mono_r _ _ (List.length l)).
    rewrite List.repeat_length.
    rewrite PeanoNat.Nat.sub_add.
    now rewrite PeanoNat.Nat.add_comm.
    exact H1.
    exfalso.
    exact (wf_used_var _ _ H H0 H3).
    exact H2.
Qed.

Ltac cut_none_mid_abs_like_goal ctx l r mid str arg_type range body TYPING1 TYPING_RULE IHTYPING1 IHTYPING2 CTX_EQ :=
    apply TYPING_RULE; [>
        now apply IHTYPING1 |
        (
            assert (
                PUSH_VAR_EQ_LEMMA1 :
                    push_var (lower_context l (List.length l) mid ++ lower_context r (List.length l) mid)%list str (lower arg_type (List.length l) mid) 
                    = 
                    (push_var (lower_context l (List.length l) mid) str (lower arg_type (List.length l) mid) ++ lift1_context (lower_context r (List.length l) mid))%list
            ) by (
                unfold push_var; unfold lift1_context;
                simpl; repeat rewrite lift_context_split; 
                reflexivity
            );
            assert (
                PUSH_VAR_LENG_LEMMA :
                    List.length (push_var l str arg_type)
                    =
                    S (List.length l)
            ) by (
                unfold push_var; unfold lift1_context; 
                rewrite lift_context_length; simpl;
                reflexivity
            );
            rewrite PUSH_VAR_EQ_LEMMA1;
            rewrite PeanoNat.Nat.add_1_r;
            assert (
                PUSH_VAR_EQ_LEMMA2 :
                    (push_var (lower_context l (List.length l) mid) str (lower arg_type (List.length l) mid) ++ lift1_context (lower_context r (List.length l) mid))%list
                    = 
                    (lower_context (lift1_context (Some (str, arg_type) :: l)) (List.length l + 1) mid ++ lower_context (lift1_context r) (List.length l + 1) mid)%list
            ) by (
                unfold push_var; unfold lift1_context; simpl;
                rewrite <- (PeanoNat.Nat.add_0_r (List.length l)) at 1;
                rewrite <- (PeanoNat.Nat.add_0_r (List.length l)) at 2; 
                rewrite <- (PeanoNat.Nat.add_0_r (List.length l)) at 3;
                rewrite lift_lower_swap_ex by (
                    rewrite PeanoNat.Nat.add_0_r;
                    rewrite CTX_EQ in TYPING1; exact (ctx_none_seq_term _ _ _ _ _ TYPING1)
                );
                rewrite lift_lower_context_swap by (
                    rewrite PeanoNat.Nat.add_0_r;
                    (
                        match goal with
                        | [|- forall v : nat, _ -> _] =>
                            let hyp_name := fresh "H" in
                            intros v hyp_name;
                            assert (USED_STMT : var_used (l ++ List.repeat None mid ++ r)%list v) by 
                            (apply (var_used_cases l (List.repeat None mid ++ r)%list); tauto);
                            generalize v USED_STMT; apply ctx_none_seq_ctx; rewrite <- CTX_EQ; exact (typable_wf _ _ _ TYPING1)
                        end
                    )
                );
                rewrite lift_lower_context_swap by (
                    rewrite PeanoNat.Nat.add_0_r;
                    (
                        match goal with
                        | [|- forall v : nat, _ -> _] => 
                            let hyp_name := fresh "H" in 
                            intros v hyp_name;
                            assert (USED_STMT : var_used (l ++ List.repeat None mid ++ r)%list v) by 
                            (intros; rewrite List.app_assoc; apply (var_used_cases (l ++ List.repeat None mid)%list r); tauto);
                            generalize v USED_STMT; apply ctx_none_seq_ctx; rewrite <- CTX_EQ; exact (typable_wf _ _ _ TYPING1)
                        end
                    )
                );
                rewrite PeanoNat.Nat.add_0_r; reflexivity
            );
            rewrite PUSH_VAR_EQ_LEMMA2;
            change (lift1_context (Some (str, arg_type) :: l)%list) with (push_var l str arg_type);
            rewrite PeanoNat.Nat.add_1_r;
            rewrite <- PUSH_VAR_LENG_LEMMA;
            apply IHTYPING2;
            rewrite CTX_EQ;
            unfold push_var; simpl;
            unfold lift1_context;
            repeat rewrite lift_context_split;
            now rewrite lift_none
        )
    ]
.

(*
    We state that a chunk of dummy-variables can be easily cut out
    of the context but the left and right parts of the context, the
    term and its type must be lowered accordingly.
*)
Theorem cut_none_mid : forall (l r : context) (t type : term) (mid : nat),
    (l ++ (List.repeat None mid) ++ r)%list |- t := type ->
    (lower_context l (List.length l) mid ++ lower_context r (List.length l) mid)%list |- lower t (List.length l) mid := lower type (List.length l) mid
.
Proof.
    (* 
        Some tricky goal reshaping to make it look like a predicate
        for an induction principle. We pretty much do something similar
        to `dependent induction`, but get the possibility to use mutual
        induction while preserving doing something like `dependent induction`
        note that all of that can be done without assuming the John Major
        equality.
        The `Print Assumptions cut_none_mid` shows John Major's equality
        axiom because this theorem uses `ctx_none_seq_type`, which
        calls `wf_fetched_var`, which uses `ctx_append_left`, which
        is a corollary of `ctx_insert` which uses the John Major
        equality, but can be proved without it.
    *)
    intros.
    set (ctx := (l ++ List.repeat None mid ++ r)%list).
    assert (ctx = (l ++ List.repeat None mid ++ r)%list) by (now subst ctx).
    rewrite <- H0 in H.
    generalize l r mid H0.
    generalize ctx t type H.
    clear H0 H ctx mid t type l r.
    (*
        We now call the induction principle
    *)
    apply (
        typing_ind_mut
        (
            fun ctx t type proof => 
            forall l r mid,
            ctx = (l ++ List.repeat None mid ++ r)%list ->
            (lower_context l (Datatypes.length l) mid ++
            lower_context r (Datatypes.length l) mid)%list
            |- lower t (Datatypes.length l) mid := lower type (Datatypes.length l) mid
        ) 
        (
            fun ctx _ => 
            forall l r mid,
            ctx = (l ++ List.repeat None mid ++ r)%list ->
            WF (lower_context l (Datatypes.length l) mid ++
            lower_context r (Datatypes.length l) mid)%list
        )
    ).

    simpl; intros.
    apply TNat.
    now apply H.

    simpl; intros.
    apply TNatO.
    now apply H.

    simpl; intros.
    apply TNatSucc.
    now apply H.

    simpl; intros.
    apply TNatRec.
    now apply H.
    now apply H0.
    generalize (H1 _ _ _ H3).
    assert (PeanoNat.Nat.ltb 0 (List.length l + 1) = true).
    rewrite PeanoNat.Nat.add_1_r; apply PeanoNat.Nat.ltb_lt; apply PeanoNat.Nat.lt_0_succ.
    assert (PeanoNat.Nat.ltb 1 (List.length l + 1 + 1) = true).
    repeat rewrite PeanoNat.Nat.add_1_r; apply PeanoNat.Nat.ltb_lt; apply Lt.lt_n_S; apply PeanoNat.Nat.lt_0_succ.
    rewrite H4; rewrite H5; clear H4 H5.
    intro H4.
    rewrite <- (PeanoNat.Nat.add_0_r (List.length l)) at 4.
    rewrite <- (PeanoNat.Nat.add_0_r (List.length l)) at 5.
    rewrite lift_lower_swap_ex by (rewrite PeanoNat.Nat.add_0_r; rewrite H3 in t; exact (ctx_none_seq_term _ _ _ _ _ t)).
    rewrite lift_lower_swap_ex by (rewrite PeanoNat.Nat.add_0_r; rewrite H3 in t; exact (ctx_none_seq_term _ _ _ _ _ t)).
    repeat rewrite PeanoNat.Nat.add_0_r.
    rewrite <- PeanoNat.Nat.add_assoc in H4.
    exact H4.
    now apply H2.

    simpl; intros.
    unfold top_subst.
    unfold clean_after_subst.
    rewrite <- (PeanoNat.Nat.add_0_r (List.length l0)) at 5.
    rewrite <- lower_swap_ex.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite <- lower_subst_unfold_alt.
    unfold lift1.
    rewrite <- (PeanoNat.Nat.add_0_r (List.length l0 + 1)) at 2.
    rewrite <- lift_lower_swap_ex.
    rewrite PeanoNat.Nat.add_0_r.
    change (
        lower (
            subst
            (lower range (List.length l0 + 1) mid)
            0
            (lift (lower r (List.length l0) mid) 0 1)
        ) 0 1
    ) with (
        top_subst (lower range (List.length l0 + 1) mid) (lower r (List.length l0) mid)
    ).
    apply (TApp _ str (lower domain (List.length l0) mid)).
    now apply H.
    now apply H0.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite H1 in t0; exact (ctx_none_seq_term _ _ _ _ _ t0).
    intro v; destruct v.
    intro H2; exfalso; generalize H2; unfold lift1; apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    intro H2.
    rewrite <- PeanoNat.Nat.add_1_r in H2; unfold lift1 in H2.
    apply (lifting_respects_occurance_r _ _ _ _ (le_0_n _)) in H2.
    intro H3.
    rewrite PeanoNat.Nat.add_1_r in H3.
    rewrite PeanoNat.Nat.add_shuffle0.
    rewrite PeanoNat.Nat.add_1_r.
    apply Le.le_n_S; apply Le.le_S_n in H3.
    generalize v H2 H3.
    rewrite H1 in t0; exact (ctx_none_seq_term _ _ _ _ _ t0).
    rewrite H1 in t.
    generalize (ctx_none_seq_type _ _ _ _ _ t).
    intro H2; simpl in H2.
    intro v; destruct v.
    intros H3 H4; exfalso; generalize H4; rewrite PeanoNat.Nat.add_1_r; apply PeanoNat.Nat.nle_succ_0.
    intros.
    rewrite PeanoNat.Nat.add_shuffle0.
    rewrite PeanoNat.Nat.add_1_r; rewrite PeanoNat.Nat.add_1_r in H4.
    apply Le.le_n_S; apply Le.le_S_n in H4.
    intuition.
    rewrite PeanoNat.Nat.add_1_r; apply PeanoNat.Nat.lt_0_succ.
    intros V H2.
    apply subst_respects_occurance in H2.
    destruct H2.
    destruct H2.
    destruct V.
    exfalso; unfold lift1 in H2; generalize H2; apply (lifting_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    rewrite <- PeanoNat.Nat.add_1_r in H2; unfold lift1 in H2.
    apply (lifting_respects_occurance_r _ _ _ _ (le_0_n _)) in H2.
    rewrite PeanoNat.Nat.add_0_r.
    intro H4.
    rewrite PeanoNat.Nat.add_shuffle0; rewrite PeanoNat.Nat.add_1_r; rewrite PeanoNat.Nat.add_1_r in H4.
    apply Le.le_n_S; apply Le.le_S_n in H4.
    generalize V H2 H4.
    rewrite H1 in t0; exact (ctx_none_seq_term _ _ _ _ _ t0).
    destruct H2.
    rewrite PeanoNat.Nat.add_0_r.
    destruct V; try easy.
    intro H4.
    rewrite PeanoNat.Nat.add_shuffle0; rewrite PeanoNat.Nat.add_1_r; rewrite PeanoNat.Nat.add_1_r in H4.
    apply Le.le_n_S; apply Le.le_S_n in H4.
    generalize V H2 H4.
    rewrite H1 in t; generalize (ctx_none_seq_type _ _ _ _ _ t).
    simpl; intuition.

    simpl; intros.
    cut_none_mid_abs_like_goal ctx l r mid str arg_type range body t TAbsSmall H H0 H1.

    simpl; intros.
    cut_none_mid_abs_like_goal ctx l r mid str arg_type range body t (fun a b c d e => TAbsType a b c d e i) H H0 H1.

    simpl; intros.
    cut_none_mid_abs_like_goal ctx l r mid str arg_type range body t TAbsProp H H0 H1.

    simpl; intros.
    rewrite H0 in h.
    case_eq (PeanoNat.Nat.ltb n (List.length l)); intros; unfold has_type; unfold has_type in h.
    apply TVar.
    now apply H.
    apply PeanoNat.Nat.ltb_lt in H1.
    rewrite (List.nth_error_app1 _ _ H1) in h.
    unfold has_type; rewrite List.nth_error_app1 by (now rewrite lower_context_length).
    now apply has_type_lower.
    apply PeanoNat.Nat.ltb_ge in H1.
    
    destruct (PeanoNat.Nat.lt_ge_cases n (List.length l + mid)).
    rewrite (List.nth_error_app2 _ _ H1) in h.
    assert (n - List.length l < List.length (List.repeat (@None (string * term)) mid)).
    apply (PeanoNat.Nat.add_lt_mono_r _ _ (List.length l)).
    rewrite PeanoNat.Nat.sub_add by exact H1.
    now (rewrite List.repeat_length; rewrite PeanoNat.Nat.add_comm).
    rewrite List.nth_error_app1 in h by exact H3. 
    case_eq (List.nth_error (List.repeat (@None (string * term)) mid) (n - List.length l)); intros.
    rewrite H4 in h.
    apply List.nth_error_In in H4.
    apply List.repeat_spec in H4.
    now subst o.
    apply List.nth_error_None in H4.
    exfalso; exact (Lt.lt_not_le _ _ H3 H4).
    assert (mid <= n - List.length l).
    apply (PeanoNat.Nat.sub_le_mono_r _ _ (List.length l)) in H2.
    rewrite PeanoNat.Nat.add_comm in H2.
    now rewrite PeanoNat.Nat.add_sub in H2.
    rewrite List.nth_error_app2 in h by exact H1.
    rewrite List.nth_error_app2 in h by (now rewrite List.repeat_length).
    apply TVar.
    now apply H.
    unfold has_type.
    rewrite List.nth_error_app2 by (
        apply (PeanoNat.Nat.sub_le_mono_r _ _ mid) in H2;
        rewrite PeanoNat.Nat.add_sub in H2;
        now rewrite lower_context_length
    ).
    rewrite List.repeat_length in h.
    rewrite <- PeanoNat.Nat.sub_add_distr; rewrite <- PeanoNat.Nat.sub_add_distr in h.
    rewrite lower_context_length; rewrite PeanoNat.Nat.add_comm.
    now apply has_type_lower.

    simpl; intros.
    apply TSmallKind.
    now apply H.

    simpl; intros.
    apply TPropKind.
    now apply H.

    simpl; intros.
    apply TTypeKind.
    now apply H.

    simpl; intros.
    cut_none_mid_abs_like_goal ctx l r mid str domain range body t TForallType H H0 H1.

    simpl; intros.
    cut_none_mid_abs_like_goal ctx l r mid str domain range body t TForallPropSmall H H0 H1.

    simpl; intros.
    cut_none_mid_abs_like_goal ctx l r mid str domain range body t TForallPropProp H H0 H1.

    simpl; intros.
    cut_none_mid_abs_like_goal ctx l r mid str domain range body t (fun a b c d => TForallPropType a b c d i) H H0 H1.

    simpl; intros.
    cut_none_mid_abs_like_goal ctx l r mid str domain range body t TForallSmallSmall H H0 H1.

    simpl; intros.
    cut_none_mid_abs_like_goal ctx l r mid str domain range body t TForallSmallProp H H0 H1.

    simpl; intros.
    apply JumpToTypeUniverseSmall.
    now apply H.

    simpl; intros.
    apply JumpToTypeUniverseProp.
    now apply H.

    simpl; intros.
    apply RaiseUniverse.
    now apply H.

    simpl; intros.
    apply (ConversionSmallL _ _ (lower type (List.length l) mid)).
    now apply H.
    now apply H0.
    apply lowering_respects_one_step.
    exact s.
    rewrite H2 in t1; exact (ctx_none_seq_term _ _ _ _ _ t1).
    now apply H1.

    simpl; intros.
    apply (ConversionPropL _ _ (lower type (List.length l) mid)).
    now apply H.
    now apply H0.
    apply lowering_respects_one_step.
    exact s.
    rewrite H2 in t1; exact (ctx_none_seq_term _ _ _ _ _ t1).
    now apply H1.

    simpl; intros.
    apply (ConversionTypeL _ _ (lower type (List.length l) mid) _ i).
    now apply H.
    now apply H0.
    apply lowering_respects_one_step.
    exact s.
    rewrite H2 in t1; exact (ctx_none_seq_term _ _ _ _ _ t1).
    now apply H1.

    simpl; intros.
    apply (ConversionSmallR _ _ (lower type (List.length l) mid)).
    now apply H.
    now apply H0.
    apply lowering_respects_one_step.
    exact s.
    rewrite H2 in t2; exact (ctx_none_seq_term _ _ _ _ _ t2).
    now apply H1.

    simpl; intros.
    apply (ConversionPropR _ _ (lower type (List.length l) mid)).
    now apply H.
    now apply H0.
    apply lowering_respects_one_step.
    exact s.
    rewrite H2 in t2; exact (ctx_none_seq_term _ _ _ _ _ t2).
    now apply H1.

    simpl; intros.
    apply (ConversionTypeR _ _ (lower type (List.length l) mid) _ i).
    now apply H.
    now apply H0.
    apply lowering_respects_one_step.
    exact s.
    rewrite H2 in t2; exact (ctx_none_seq_term _ _ _ _ _ t2).
    now apply H1.

    simpl; intros.
    apply (ConversionSmallRename _ _ (lower type (List.length l) mid)).
    now apply H.
    now apply H0.
    apply lowering_respects_alpha_eq.
    exact t2.
    now apply H1.

    simpl; intros.
    apply (ConversionPropRename _ _ (lower type (List.length l) mid)).
    now apply H.
    now apply H0.
    apply lowering_respects_alpha_eq.
    exact t2.
    now apply H1.

    simpl; intros.
    apply (ConversionTypeRename _ _ (lower type (List.length l) mid) _ i).
    now apply H.
    now apply H0.
    apply lowering_respects_alpha_eq.
    exact t2.
    now apply H1.

    intros.
    symmetry in H.
    apply List.app_eq_nil in H.
    destruct H.
    apply List.app_eq_nil in H0.
    destruct H0.
    subst l; subst r; simpl.
    apply WF_empty.

    simpl; intros.
    destruct l.
    simpl in H1.
    destruct mid.
    simpl in H1.
    destruct r.
    easy.
    unfold push_var in H1; unfold lift1_context in H1; simpl in H1; injection H1.
    intros; subst r; subst o; simpl.
    rewrite lower_c_0.
    rewrite lower_context_c_0.
    apply WF_assum_small.
    exact w.
    exact t0.
    simpl in H1; easy.
    simpl in H1.
    unfold has_type in H1; unfold lift1_context in H1; simpl in H1; injection H1.
    intros; subst o.
    simpl.
    elim (lifted_context_repr l 0 1).
    intros.
    elim (lifted_context_repr r 0 1).
    intros.
    subst l; subst r.
    rewrite lift_context_length.
    rewrite <- (PeanoNat.Nat.add_1_r (List.length x)).
    rewrite <- (PeanoNat.Nat.add_0_r (List.length x + 1)).
    rewrite <- lift_lower_swap_ex.
    rewrite <- lift_lower_context_swap.
    rewrite <- lift_lower_context_swap.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite <- lift_context_split.
    change (
        Some (str, lift (lower t (List.length x) mid) 0 1) :: (lift_context (lower_context x (List.length x) mid ++ lower_context x0 (List.length x) mid) 0 1)
    )%list with (
        {str == lower t (List.length x) mid}::(lower_context x (List.length x) mid ++ lower_context x0 (List.length x) mid)%list
    ).
    apply WF_assum_small.
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    exact (H _ _ _ H2).
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    exact (H0 _ _ _ H2).
    rewrite PeanoNat.Nat.add_0_r.
    intros v H3.
    assert (var_used (x ++ List.repeat None mid ++ x0)%list v).
    rewrite List.app_assoc; apply var_used_cases; intuition.
    generalize v H4.
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    rewrite H2 in w.
    now apply ctx_none_seq_ctx.
    intros v H3.
    assert (var_used (x ++ List.repeat None mid ++ x0)%list v).
    apply var_used_cases; intuition.
    rewrite PeanoNat.Nat.add_0_r.
    generalize v H4.
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    rewrite H2 in w.
    now apply ctx_none_seq_ctx.
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    rewrite H2 in w.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite H2 in t0.
    now apply (ctx_none_seq_term _ _ _ _ _ t0).
    intros.
    assert (var_used (l ++ List.repeat None mid ++ r)%list v).
    rewrite List.app_assoc; apply var_used_cases; intuition.
    rewrite <- H2 in H5; unfold lift1_context in H5.
    destruct v.
    exfalso.
    generalize H5.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.
    intros.
    assert (var_used (l ++ List.repeat None mid ++ r)%list v).
    apply var_used_cases; intuition.
    rewrite <- H2 in H4; unfold lift1_context in H4.
    destruct v.
    exfalso.
    generalize H4.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.
    
    simpl; intros.
    destruct l.
    simpl in H1.
    destruct mid.
    simpl in H1.
    destruct r.
    easy.
    unfold push_var in H1; unfold lift1_context in H1; simpl in H1; injection H1.
    intros; subst r; subst o; simpl.
    rewrite lower_c_0.
    rewrite lower_context_c_0.
    apply WF_assum_prop.
    exact w.
    exact t0.
    simpl in H1; easy.
    simpl in H1.
    unfold has_type in H1; unfold lift1_context in H1; simpl in H1; injection H1.
    intros; subst o.
    simpl.
    elim (lifted_context_repr l 0 1).
    intros.
    elim (lifted_context_repr r 0 1).
    intros.
    subst l; subst r.
    rewrite lift_context_length.
    rewrite <- (PeanoNat.Nat.add_1_r (List.length x)).
    rewrite <- (PeanoNat.Nat.add_0_r (List.length x + 1)).
    rewrite <- lift_lower_swap_ex.
    rewrite <- lift_lower_context_swap.
    rewrite <- lift_lower_context_swap.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite <- lift_context_split.
    change (
        Some (str, lift (lower t (List.length x) mid) 0 1) :: (lift_context (lower_context x (List.length x) mid ++ lower_context x0 (List.length x) mid) 0 1)
    )%list with (
        {str == lower t (List.length x) mid}::(lower_context x (List.length x) mid ++ lower_context x0 (List.length x) mid)%list
    ).
    apply WF_assum_prop.
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    exact (H _ _ _ H2).
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    exact (H0 _ _ _ H2).
    rewrite PeanoNat.Nat.add_0_r.
    intros v H3.
    assert (var_used (x ++ List.repeat None mid ++ x0)%list v).
    rewrite List.app_assoc; apply var_used_cases; intuition.
    generalize v H4.
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    rewrite H2 in w.
    now apply ctx_none_seq_ctx.
    intros v H3.
    assert (var_used (x ++ List.repeat None mid ++ x0)%list v).
    apply var_used_cases; intuition.
    rewrite PeanoNat.Nat.add_0_r.
    generalize v H4.
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    rewrite H2 in w.
    now apply ctx_none_seq_ctx.
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    rewrite H2 in w.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite H2 in t0.
    now apply (ctx_none_seq_term _ _ _ _ _ t0).
    intros.
    assert (var_used (l ++ List.repeat None mid ++ r)%list v).
    rewrite List.app_assoc; apply var_used_cases; intuition.
    rewrite <- H2 in H5; unfold lift1_context in H5.
    destruct v.
    exfalso.
    generalize H5.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.
    intros.
    assert (var_used (l ++ List.repeat None mid ++ r)%list v).
    apply var_used_cases; intuition.
    rewrite <- H2 in H4; unfold lift1_context in H4.
    destruct v.
    exfalso.
    generalize H4.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.

    simpl; intros.
    destruct l.
    simpl in H1.
    destruct mid.
    simpl in H1.
    destruct r.
    easy.
    unfold push_var in H1; unfold lift1_context in H1; simpl in H1; injection H1.
    intros; subst r; subst o; simpl.
    rewrite lower_c_0.
    rewrite lower_context_c_0.
    apply (WF_assum_type _ _ _ i).
    exact w.
    exact t0.
    simpl in H1; easy.
    simpl in H1.
    unfold has_type in H1; unfold lift1_context in H1; simpl in H1; injection H1.
    intros; subst o.
    simpl.
    elim (lifted_context_repr l 0 1).
    intros.
    elim (lifted_context_repr r 0 1).
    intros.
    subst l; subst r.
    rewrite lift_context_length.
    rewrite <- (PeanoNat.Nat.add_1_r (List.length x)).
    rewrite <- (PeanoNat.Nat.add_0_r (List.length x + 1)).
    rewrite <- lift_lower_swap_ex.
    rewrite <- lift_lower_context_swap.
    rewrite <- lift_lower_context_swap.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite <- lift_context_split.
    change (
        Some (str, lift (lower t (List.length x) mid) 0 1) :: (lift_context (lower_context x (List.length x) mid ++ lower_context x0 (List.length x) mid) 0 1)
    )%list with (
        {str == lower t (List.length x) mid}::(lower_context x (List.length x) mid ++ lower_context x0 (List.length x) mid)%list
    ).
    apply (WF_assum_type _ _ _ i).
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    exact (H _ _ _ H2).
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    exact (H0 _ _ _ H2).
    rewrite PeanoNat.Nat.add_0_r.
    intros v H3.
    assert (var_used (x ++ List.repeat None mid ++ x0)%list v).
    rewrite List.app_assoc; apply var_used_cases; intuition.
    generalize v H4.
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    rewrite H2 in w.
    now apply ctx_none_seq_ctx.
    intros v H3.
    assert (var_used (x ++ List.repeat None mid ++ x0)%list v).
    apply var_used_cases; intuition.
    rewrite PeanoNat.Nat.add_0_r.
    generalize v H4.
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    rewrite H2 in w.
    now apply ctx_none_seq_ctx.
    rewrite <- (lift_none 0 1 mid) in H2.
    rewrite <- lift_context_split in H2.
    rewrite <- lift_context_split in H2.
    unfold lift1_context in H2.
    apply lift_context_inj in H2.
    rewrite H2 in w.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite H2 in t0.
    now apply (ctx_none_seq_term _ _ _ _ _ t0).
    intros.
    assert (var_used (l ++ List.repeat None mid ++ r)%list v).
    rewrite List.app_assoc; apply var_used_cases; intuition.
    rewrite <- H2 in H5; unfold lift1_context in H5.
    destruct v.
    exfalso.
    generalize H5.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.
    intros.
    assert (var_used (l ++ List.repeat None mid ++ r)%list v).
    apply var_used_cases; intuition.
    rewrite <- H2 in H4; unfold lift1_context in H4.
    destruct v.
    exfalso.
    generalize H4.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.

    intros.
    destruct l.
    simpl in H0.
    destruct mid.
    simpl in H0.
    destruct r.
    easy.
    destruct o.
    easy.
    simpl.
    rewrite lower_context_c_0.
    rewrite <- H0.
    apply WF_dummy_assum.
    exact w.
    simpl in H0.
    unfold push_dummy in H0; simpl in H0.
    injection H0.
    intros.
    elim (lifted_context_repr r 0 1).
    intros.
    simpl; rewrite H2.
    assert (ctx = nil ++ List.repeat None mid ++ x)%list.
    simpl.
    apply (lift_context_inj _ _ 0 1).
    unfold lift1_context in H1; rewrite H1.
    rewrite lift_context_split.
    rewrite lift_none.
    now rewrite H2.
    rewrite <- (PeanoNat.Nat.add_1_r mid).
    rewrite PeanoNat.Nat.add_comm.
    rewrite <- lower_context_merge.
    rewrite lift_lower_context_destruct.
    apply (H _ _ _ H3).
    rewrite PeanoNat.Nat.add_0_l.
    intros.
    destruct v.
    exfalso; generalize H4; apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    apply Le.le_n_S; apply le_0_n.
    intros.
    assert (var_used (List.repeat None mid ++ r)%list v).
    apply var_used_cases; tauto.
    rewrite <- H1 in H3.
    unfold lift1_context in H3.
    destruct v.
    exfalso; generalize H3.
    apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; simpl; apply Le.le_n_S; apply le_0_n.
    simpl in H0.
    unfold push_dummy in H0.
    injection H0.
    intros; subst o.
    simpl.
    rewrite <- lower_context_split.
    elim (lifted_context_repr l 0 1).
    intros.
    elim (lifted_context_repr r 0 1).
    intros.
    rewrite H2 at 1; subst r; subst l; rewrite lift_context_length.
    rewrite <- lift_context_split.
    rewrite <- (PeanoNat.Nat.add_1_r (List.length x)).
    rewrite <- (PeanoNat.Nat.add_0_r (List.length x + 1)).
    rewrite <- lift_lower_context_swap.
    rewrite PeanoNat.Nat.add_0_r.
    apply WF_dummy_assum.
    rewrite lower_context_split.
    apply H.
    apply (lift_context_inj _ _ 0 1).
    repeat rewrite lift_context_split; rewrite lift_none; exact H1.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite <- (lift_none 0 1) in H1.
    repeat rewrite <- lift_context_split in H1.
    unfold lift1_context in H1.
    apply lift_context_inj in H1.
    intros v H2.
    apply var_used_cases in H2.
    destruct H2.
    assert (var_used (x ++ List.repeat None mid ++ x0)%list v).
    apply var_used_cases; tauto.
    generalize v H3.
    apply ctx_none_seq_ctx.
    now rewrite <- H1.
    assert (var_used (x ++ List.repeat None mid ++ x0)%list v).
    rewrite List.app_assoc.
    apply var_used_cases; tauto.
    generalize v H3.
    apply ctx_none_seq_ctx.
    now rewrite <- H1.
    intros v H3.
    destruct v.
    assert (var_used (l ++ List.repeat None mid ++ r)%list 0).
    rewrite List.app_assoc.
    apply var_used_cases; tauto.
    rewrite <- H1 in H4.
    unfold lift1_context in H4.
    exfalso; generalize H4; apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.
    intros v H2.
    destruct v.
    assert (var_used (l ++ List.repeat None mid ++ r)%list 0).
    apply var_used_cases; tauto.
    rewrite <- H1 in H3; unfold lift1_context in H3.
    exfalso; generalize H3; apply (lifting_context_destroys _ _ _ _ (le_0_n _) (PeanoNat.Nat.lt_0_succ _)).
    right; apply Le.le_n_S; apply le_0_n.
Qed.

(*
    Special case when we cut dummy variables on the left.
*)
Corollary cut_none_l : forall (ctx : context) (t type : term) (mid : nat),
    ((List.repeat None mid) ++ ctx)%list |- t := type ->
    (lower_context ctx 0 mid)%list |- lower t 0 mid := lower type 0 mid
.
Proof.
    intros.
    rewrite <- (List.app_nil_l (List.repeat None mid ++ ctx)%list) in H.
    rewrite <- (List.app_nil_l (lower_context ctx 0 mid)%list).
    change nil with (lower_context nil 0 mid).
    change 0 with (List.length (@nil (option (string * term)))).
    now apply cut_none_mid.
Qed.

Ltac replace_none_mid_abs_like_goal TYPING_RULE WF_RULE TYPING_HYP1 TYPING_HYP2 ARG_NAME ARG_TYPE CTX_EQ WF_HYP LEFT_PART RIGHT_PART NEW_MID :=
    apply TYPING_RULE; (
        now apply (TYPING_HYP1 _ _ _ CTX_EQ) 
        ||
        (
            unfold push_var; unfold lift1_context; simpl; repeat rewrite lift_context_split;
            apply (TYPING_HYP2 ({ARG_NAME == ARG_TYPE} :: LEFT_PART) (lift1_context RIGHT_PART) (lift1_context NEW_MID));
            (
                (
                    rewrite CTX_EQ; unfold push_var; unfold lift1_context; 
                    simpl; repeat rewrite lift_context_split; rewrite lift_context_length;
                    now rewrite lift_none
                ) ||
                (
                    unfold push_var; unfold lift1_context; simpl;
                    repeat rewrite <- lift_context_split;
                    apply WF_RULE; (exact WF_HYP || now apply (TYPING_HYP1 _ _ _ CTX_EQ))
                )
            )
        )
    )
.

(*
    A theorem about changing the sequence of `None`s with some useful
    stuff
*)
Theorem replace_none_mid : forall (l r new_mid : context) (t type : term),
    (l ++ (List.repeat None (List.length new_mid)) ++ r)%list |- t := type ->
    WF (l ++ new_mid ++ r)%list ->
    (l ++ new_mid ++ r)%list |- t := type
.
Proof. 
    (*
        I decided to prove that theorem without dependent induction too
        as a proof of concept, that John Major's equality is not
        needed.
    *)
    intros l r new_mid t type H.
    set (ctx := (l ++ List.repeat None (List.length new_mid) ++ r)%list).
    assert (ctx = (l ++ List.repeat None (List.length new_mid) ++ r)%list).
    now subst ctx.
    rewrite <- H0 in H.
    generalize l r new_mid H0.
    clear H0.
    generalize ctx t type H.
    clear H ctx t type l r new_mid.
    (* Invoking the induction *)
    intros ctx t type H.
    induction H.
    (* Solving subgoals *)

    intros; now apply TNat.

    intros; now apply TNatO.

    intros; now apply TNatSucc.

    intros.
    apply TNatRec.
    now apply (IHtyping1 _ _ _ H3).
    now apply (IHtyping2 _ _ _ H3).
    now apply (IHtyping3 _ _ _ H3).
    now apply (IHtyping4 _ _ _ H3).

    intros.
    apply (TApp _ str domain).
    now apply (IHtyping1 _ _ _ H1).
    now apply (IHtyping2 _ _ _ H1).

    intros.
    replace_none_mid_abs_like_goal TAbsSmall WF_assum_small IHtyping1 IHtyping2 str arg_type H1 H2 l r new_mid.

    intros.
    replace_none_mid_abs_like_goal (fun a b c d e => TAbsType a b c d e i) (fun a b c => WF_assum_type a b c i) IHtyping1 IHtyping2 str arg_type H1 H2 l r new_mid.

    intros.
    replace_none_mid_abs_like_goal TAbsProp WF_assum_prop IHtyping1 IHtyping2 str arg_type H1 H2 l r new_mid.

    intros.
    apply TVar.
    exact H2.
    subst ctx.
    generalize H0.
    unfold has_type.
    destruct (PeanoNat.Nat.lt_ge_cases n (List.length l)).
    rewrite (List.nth_error_app1 _ _ H1).
    rewrite (List.nth_error_app1 _ _ H1).
    exact id.
    rewrite (List.nth_error_app2 _ _ H1).
    destruct (PeanoNat.Nat.lt_ge_cases n (List.length l + List.length new_mid)).
    assert (n - List.length l < List.length new_mid).
    apply (PeanoNat.Nat.add_lt_mono_r _ _ (List.length l)).
    rewrite (PeanoNat.Nat.sub_add _ _ H1).
    now rewrite PeanoNat.Nat.add_comm.
    rewrite (List.nth_error_app2 _ _ H1).
    rewrite <- (List.repeat_length (@None (string * term)) (List.length new_mid)) in H4.
    rewrite (List.nth_error_app1 _ _ H4).
    assert (List.nth_error (List.repeat None (List.length new_mid)) (n - List.length l) = Some (@None (string * term))).
    case_eq (List.nth_error (List.repeat (@None (string * term)) (List.length new_mid)) (n - List.length l)); intros.
    apply List.nth_error_In in H5.
    apply List.repeat_spec in H5.
    now subst o.
    apply List.nth_error_None in H5.
    exfalso.
    exact (Lt.lt_not_le _ _ H4 H5).
    rewrite H5.
    tauto.
    rewrite (List.nth_error_app2 _ _ H1).
    assert (List.length new_mid <= n - List.length l).
    apply (PeanoNat.Nat.add_le_mono_r _ _ (List.length l)).
    rewrite (PeanoNat.Nat.sub_add _ _ H1).
    now rewrite PeanoNat.Nat.add_comm.
    rewrite (List.nth_error_app2 _ _ H4).
    rewrite <- (List.repeat_length (@None (string * term)) (List.length new_mid)) in H4.
    rewrite (List.nth_error_app2 _ _ H4).
    rewrite List.repeat_length.
    exact id.

    intros; now apply TSmallKind.

    intros; now apply TPropKind.

    intros; now apply TTypeKind.

    intros.
    replace_none_mid_abs_like_goal (fun a b c d => TForallType a b c d universe) (fun a b c => WF_assum_type a b c universe) IHtyping1 IHtyping2 str domain H1 H2 l r new_mid.

    intros.
    replace_none_mid_abs_like_goal TForallPropSmall WF_assum_small IHtyping1 IHtyping2 str domain H1 H2 l r new_mid.

    intros.
    replace_none_mid_abs_like_goal TForallPropProp WF_assum_prop IHtyping1 IHtyping2 str domain H1 H2 l r new_mid.

    intros.
    replace_none_mid_abs_like_goal (fun a b c d => TForallPropType a b c d i) (fun a b c => WF_assum_type a b c i) IHtyping1 IHtyping2 str domain H1 H2 l r new_mid.

    intros.
    replace_none_mid_abs_like_goal TForallSmallSmall WF_assum_small IHtyping1 IHtyping2 str domain H1 H2 l r new_mid.

    intros.
    replace_none_mid_abs_like_goal TForallSmallProp WF_assum_prop IHtyping1 IHtyping2 str domain H1 H2 l r new_mid.

    intros.
    apply JumpToTypeUniverseSmall.
    apply IHtyping.
    exact H0.
    exact H1.

    intros.
    apply JumpToTypeUniverseProp.
    apply IHtyping.
    exact H0.
    exact H1.

    intros.
    apply RaiseUniverse.
    apply IHtyping.
    exact H0.
    exact H1.

    intros.
    apply (ConversionSmallL _ _ type).
    now apply IHtyping1.
    now apply IHtyping2.
    exact H1.
    now apply IHtyping3.

    intros.
    apply (ConversionPropL _ _ type).
    now apply IHtyping1.
    now apply IHtyping2.
    exact H1.
    now apply IHtyping3.

    intros.
    apply (ConversionTypeL _ _ type _ i).
    now apply IHtyping1.
    now apply IHtyping2.
    exact H1.
    now apply IHtyping3.

    intros.
    apply (ConversionSmallR _ _ type).
    now apply IHtyping1.
    now apply IHtyping2.
    exact H1.
    now apply IHtyping3.

    intros.
    apply (ConversionPropR _ _ type).
    now apply IHtyping1.
    now apply IHtyping2.
    exact H1.
    now apply IHtyping3.

    intros.
    apply (ConversionTypeR _ _ type _ i).
    now apply IHtyping1.
    now apply IHtyping2.
    exact H1.
    now apply IHtyping3.

    intros.
    apply (ConversionSmallRename _ _ type).
    now apply IHtyping1.
    now apply IHtyping2.
    exact H1.
    now apply IHtyping3.

    intros.
    apply (ConversionPropRename _ _ type).
    now apply IHtyping1.
    now apply IHtyping2.
    exact H1.
    now apply IHtyping3.

    intros.
    apply (ConversionTypeRename _ _ type _ i).
    now apply IHtyping1.
    now apply IHtyping2.
    exact H1.
    now apply IHtyping3.
Qed.
(* Note that `Print Assumptions replace_none_mid` should say "closed under global context" *)

(*
    A useful special case of that theorem
*)
Corollary replace_none_left : forall (r new_l : context) (t type : term),
    ((List.repeat None (List.length new_l)) ++ r)%list |- t := type ->
    WF (new_l ++ r)%list ->
    (new_l ++ r)%list |- t := type
.
Proof.
    intros.
    rewrite <- (List.app_nil_l (new_l ++ r)%list).
    rewrite <- (List.app_nil_l (new_l ++ r)%list) in H0.
    rewrite <- (List.app_nil_l (List.repeat None (List.length new_l) ++ r)%list) in H.
    now apply replace_none_mid.
Qed.
