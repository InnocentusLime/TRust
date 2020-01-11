(*
    The library with facts about lifting, lowering and 
    substitution in contexts. True for all versions
    of our system
*)
Require Import Term.
Require Import Omega.
Require Import String.
Require Import ListLemmas.

(* TODO: shorten the file by using some general facts *)

(*
    Following the Pierce's impl, we save the var's name too.
*)
Definition context : Set := list (option (string * term)).

Definition lift_ctx_elem (c d : nat) (x : option (string * term)) : option (string * term) :=
    match x with
    | Some x => Some (fst x, lift (snd x) c d)
    | _ => None
    end
.

Definition lower_ctx_elem (c d : nat) (x : option (string * term)) : option (string * term) :=
    match x with
    | Some x => Some (fst x, lower (snd x) c d)
    | _ => None
    end
.

Definition lift_context (ctx : context) (c d : nat) := List.map (lift_ctx_elem c d) ctx.
Definition lift1_context (ctx : context) : context := lift_context ctx 0 1.
Definition lower_context (ctx : context) (c d : nat) := List.map (lower_ctx_elem c d) ctx.
Definition lower1_context (ctx : context) : context := lower_context ctx 0 1.
Definition push_var (ctx : context) (str : string) (t : term) : context := lift1_context (cons (Some (str, t)) ctx).
Definition push_dummy (ctx : context) : context := cons None (lift1_context ctx).

(* TODO: replace with `List.map` *)
Fixpoint subst_context (ctx : context) (v : nat) (N : term) :=
    match ctx with
    | nil => nil
    | cons (Some (s, t)) tl => cons (Some (s, subst t v N)) (subst_context tl v N)
    | cons None tl => cons None (subst_context tl v N)
    end
.
Fixpoint var_used (ctx : context) (v : nat) :=
    match ctx with
    | nil => False
    | cons (Some (_, trm)) t => var_occurs trm v \/ var_used t v
    | cons None t => var_used t v
    end
.
Fixpoint set_val (ctx : context) (i : nat) (v : option (string * term)) : context :=
    match ctx, i with
    | nil, 0 => cons v nil
    | nil, S n => cons None (set_val nil n v)
    | cons h t, 0 => cons v t
    | cons h t, S n => cons h (set_val t n v)
    end
.

Definition has_type (ctx : context) (v : nat) (t : term) : Prop :=
    match (List.nth_error ctx v) with
    | Some (Some (_, x)) => x = t
    | _ => False
    end
.
(* Notation which is read as `x has type y in G` *)
Notation "G [ x ] := y" := (has_type G x y) (at level 70, no associativity).

Definition has_no_type (ctx : context) (v : nat) : Prop :=
    match (List.nth_error ctx v) with
    | Some (Some _) => False
    | _ => True
    end
.
(* Notation which is read as `x has no type in G` *)
Notation "G [ x ] := ?!" := (has_no_type G x) (at level 70, no associativity).

(* A notation for pushing variables. Note that it conflicts with list *)
Notation "{ s == x } :: G" := (push_var G s x) (at level 84, no associativity).

Lemma lift_context_split : forall (l r : context) (c d : nat),
    lift_context (l ++ r)%list c d = (lift_context l c d ++ lift_context r c d)%list
.
Proof.
    intro l; induction l.
    easy.
    intros; simpl.
    now rewrite IHl.
Qed.

Lemma lift_context_swap : forall ctx : context, forall c d p v : nat, 
    lift_context (lift_context ctx (d + c) p) c v = lift_context (lift_context ctx c v) (d + v + c) p
.
Proof.
    intros; induction ctx.
    reflexivity.
    simpl.
    rewrite IHctx.
    destruct a.
    destruct p0.
    simpl.
    now rewrite lift_swap_ex.
    reflexivity.
Qed.

Lemma lift_context_length : forall ctx, forall c d : nat,
    List.length (lift_context ctx c d) = List.length ctx
.
Proof.
    intros.
    induction ctx.
    easy.
    simpl.
    now rewrite IHctx.
Qed.

Lemma lift_context_swap_same_c : forall ctx, forall c d1 d2 : nat,
    lift_context (lift_context ctx c d1) c d2 = lift_context (lift_context ctx c d2) c d1
.
Proof.
    intros; induction ctx.
    easy.
    simpl; rewrite IHctx.
    destruct a.
    destruct p.
    simpl.
    now rewrite lift_swap_same_c.
    simpl.
    reflexivity.
Qed.

Lemma lift_lemma_Some : forall (ctx : context) (c d v : nat) (t : term),
    ctx[v] := t <-> (lift_context ctx c d)[v] := (lift t c d)
.
Proof.
    intro ctx.
    unfold has_type.
    induction ctx; intros.
    destruct v; easy.
    destruct v.
    simpl.
    destruct a; simpl.
    destruct p; simpl.
    split.
    congruence.
    apply lift_injection.
    easy.
    simpl.
    apply IHctx.
Qed.

Lemma lift_lemma_None : forall (ctx : context) (c d v : nat),
    ctx[v] := ?! <-> (lift_context ctx c d)[v] := ?!
.
Proof.
    intro ctx.
    induction ctx.
    easy.
    intros.
    destruct v.
    simpl.
    unfold has_no_type.
    simpl.
    destruct a; easy.
    unfold has_no_type; simpl.
    apply IHctx.
Qed.

Lemma insert_lemma_l : forall (l r mid : context) (v : nat) (t : term),
    v < List.length l ->
    ((l ++ r)[v] := t)%list ->
    ((lift_context l (List.length l) (List.length mid) ++ mid ++ lift_context r (List.length l) (List.length mid))[v] := lift t (List.length l) (List.length mid))%list
.
Proof.
    intros.
    unfold has_type.
    rewrite List.nth_error_app1.
    apply lift_lemma_Some.
    unfold has_type in H0; rewrite List.nth_error_app1 in H0.
    easy.
    easy.
    now rewrite lift_context_length.
Qed.

Lemma insert_lemma_r : forall (l r mid : context) (v : nat) (t : term),
    List.length l <= v ->
    ((l ++ r)[v] := t)%list ->
    ((lift_context l (List.length l) (List.length mid) ++ mid ++ lift_context r (List.length l) (List.length mid))[v + List.length mid] := lift t (List.length l) (List.length mid))%list
.
Proof.
    intros.
    unfold has_type; unfold has_type in H0.
    rewrite List.nth_error_app2.
    rewrite List.nth_error_app2.
    rewrite List.nth_error_app2 in H0 by assumption.
    apply lift_lemma_Some.
    rewrite <- PeanoNat.Nat.sub_add_distr.
    rewrite lift_context_length.
    rewrite (PeanoNat.Nat.add_comm (List.length l)).
    rewrite PeanoNat.Nat.sub_add_distr.
    now rewrite PeanoNat.Nat.add_sub by assumption.
    rewrite PeanoNat.Nat.add_comm.
    rewrite lift_context_length.
    apply (PeanoNat.Nat.add_le_mono_r _ _ (List.length l)).
    rewrite PeanoNat.Nat.sub_add by (refine (Le.le_trans _ _ _ H (Plus.le_plus_r _ _))).
    exact (proj1 (PeanoNat.Nat.add_le_mono_l _ _ (List.length mid)) H).
    rewrite lift_context_length.
    refine (Le.le_trans _ _ _ H (Plus.le_plus_l _ _)).
Qed.

Lemma lift_none : forall (c d n : nat),
    lift_context (List.repeat None n) c d = List.repeat None n
.
Proof.
    intros; induction n.
    reflexivity.
    simpl; now rewrite IHn.
Qed.

Lemma has_type_uniq : forall (ctx : context) (v : nat) (t1 t2 : term),
    ctx[v] := t1 ->
    ctx[v] := t2 ->
    t1 = t2
.
Proof.
    unfold has_type.
    intros ctx v t1 t2.
    destruct (List.nth_error ctx v).
    destruct o.
    destruct p.
    congruence.
    tauto.
    tauto.
Qed.

Lemma has_type_cases : forall (ctx : context) (v : nat),
    (exists t, ctx[v] := t) \/ (ctx[v] := ?!)
.
Proof.
    intros.
    unfold has_type; unfold has_no_type.
    destruct (List.nth_error ctx v).
    destruct o.
    destruct p.
    left; now exists t.
    right; easy.
    right; easy.
Qed.

Lemma has_type_contradict : forall (ctx : context) (v : nat) (t : term),
    ctx[v] := t -> ctx[v] := ?! -> False
.
Proof.
    intros ctx v t.
    unfold has_type; unfold has_no_type.
    destruct (List.nth_error ctx v).
    destruct o.
    destruct p.
    tauto.
    tauto.
    tauto.
Qed.

Lemma ctx_var_lifted_repr : forall (ctx : context) (c d v : nat) (t : term),
    (lift_context ctx c d)[v] := t ->
    exists t', t = lift t' c d
.
Proof.
    intros ctx c d v t.
    case_eq (List.nth_error ctx v).
    intro o; destruct o.
    destruct p.

    intro H.
    assert (ctx[v] := t0) by (unfold has_type; now rewrite H).
    apply (lift_lemma_Some _ c d) in H0.
    intro H1.
    exists t0.
    now apply (has_type_uniq (lift_context ctx c d) v).

    intro H.
    assert (ctx[v] := ?!) by (unfold has_no_type; now rewrite H).
    apply (lift_lemma_None _ c d) in H0.
    intro H1.
    exfalso; exact (has_type_contradict _ _ _ H1 H0).

    intro H.
    assert (ctx[v] := ?!) by (unfold has_no_type; now rewrite H).
    apply (lift_lemma_None _ c d) in H0.
    intro H1.
    exfalso; exact (has_type_contradict _ _ _ H1 H0).
Qed.

Lemma lift_lower_context_destruct : forall (ctx : context) (c d : nat),
    lower_context (lift_context ctx c d) c d = ctx
.
Proof.
    intro ctx; induction ctx.

    intros; reflexivity.

    intros; simpl.
    destruct a.
    destruct p.
    simpl.
    rewrite lift_lower_destruct.
    now rewrite IHctx.
    now rewrite IHctx.
Qed.

Lemma context_used_var : forall (ctx : context) (slot v : nat) (t : term),
    ctx[slot] := t ->
    var_occurs t v ->
    var_used ctx v
.
Proof.
    intro ctx; induction ctx.

    intro slot; destruct slot; easy.

    intro slot; destruct slot.
    destruct a.
    destruct p.
    unfold has_type; simpl.
    intros v t0 H; subst t0.
    tauto.
    unfold has_type; simpl.
    tauto.
    intros v t.
    change ((a :: ctx)%list [S slot] := t) with (ctx[slot] := t).
    intros; cut (var_used ctx v).
    destruct a; (try (destruct p); simpl; tauto).
    now apply (IHctx slot _ t).
Qed.

Lemma lower_context_merge : forall (ctx : context) (c d1 d2 : nat),
    (forall v, var_used ctx v -> c <= v -> c + d1 <= v) ->
    lower_context (lower_context ctx c d1) c d2 = lower_context ctx c (d1 + d2)
.
Proof.
    intro ctx; induction ctx.

    easy.

    simpl.
    destruct a.
    destruct p.
    simpl.
    intros.
    rewrite lower_merge by intuition.
    rewrite IHctx by intuition.
    reflexivity.
    simpl.
    intros.
    rewrite (IHctx _ _ _ H).
    reflexivity.
Qed.

Lemma lower_skip_swap : forall (ctx : context) (c d n : nat),
    List.skipn n (lower_context ctx c d) = lower_context (List.skipn n ctx) c d
.
Proof.
    intros; unfold lower_context.
    apply map_skip_swap.
Qed.

Lemma lift_skip_swap : forall (ctx : context) (c d n : nat),
    List.skipn n (lift_context ctx c d) = lift_context (List.skipn n ctx) c d
.
Proof.
    intros; unfold lift_context.
    apply map_skip_swap.
Qed.

Lemma lifting_context_destroys : forall (ctx : context) (c d n : nat),
    c <= n ->
    n < c + d ->
    var_used (lift_context ctx c d) n -> False
.
Proof.
    intro ctx; induction ctx.

    easy.

    destruct a.
    destruct p.
    simpl.
    intros.
    destruct H1.
    generalize H1; now apply lifting_destroys.
    generalize H1; now apply IHctx.
    simpl; apply IHctx.
Qed.

Lemma lift_c_0_context : forall (ctx : context) (c : nat),
    lift_context ctx c 0 = ctx
.
Proof.
    intro ctx; induction ctx.
    easy.
    destruct a.
    destruct p.
    intros; simpl.
    rewrite lift_c_0.
    now rewrite IHctx.
    intros.
    simpl.
    now rewrite IHctx.
Qed.

Lemma lower_lift_context_destruct : forall (ctx : context) (c d : nat),
    (forall v, var_used ctx v -> c <= v -> c + d <= v) ->
    lift_context (lower_context ctx c d) c d = ctx
.
Proof.
    intro ctx; induction ctx.

    easy.

    destruct a.
    destruct p.
    simpl.
    intros.
    rewrite lower_lift_destruct by intuition.
    rewrite IHctx by intuition.
    reflexivity.
    simpl; intros.
    now rewrite IHctx.
Qed.

Lemma var_used_cases : forall (l r : context) (v : nat),
    var_used (l ++ r)%list v <-> var_used l v \/ var_used r v
.
Proof.
    intro l; induction l.
    simpl.
    intuition.
    simpl; intros.
    destruct a.
    destruct p.
    rewrite or_assoc.
    apply or_iff_compat_l.
    apply IHl.
    apply IHl.
Qed.

Lemma var_used_occurs : forall (ctx : context) (v : nat),
    var_used ctx v ->
    exists slot t, ctx[slot] := t /\ var_occurs t v
.
Proof.
    intro ctx; induction ctx.
    easy.
    destruct a.
    destruct p.
    simpl.
    intros.
    destruct H.
    exists 0; exists t; easy.
    destruct (IHctx _ H).
    exists (S x).
    destruct H0.
    exists x0.
    change ((Some (s, t) :: ctx)%list [S x] := x0) with (ctx[x] := x0).
    easy.
    intros.
    simpl in H.
    destruct (IHctx _ H).
    exists (S x).
    destruct H0.
    exists x0.
    easy.
Qed.

Lemma lower_context_length : forall (ctx : context) (c d : nat),
    List.length (lower_context ctx c d) = List.length ctx
.
Proof.
    unfold lower_context.
    intros.
    rewrite List.map_length.
    reflexivity.
Qed.

Lemma lower_context_split : forall (l r : context) (c d : nat),
    lower_context (l ++ r)%list c d = (lower_context l c d ++ lower_context r c d)%list
.
Proof.
    intros.
    unfold lower_context.
    rewrite List.map_app.
    reflexivity.
Qed.

Lemma lifted_context_repr : forall (ctx : context) (c d : nat),
    (forall v, var_used ctx v -> v < c \/ c + d <= v) ->
    exists ctx', ctx = lift_context ctx' c d
.
Proof.
    intro ctx; induction ctx.
    intros; exists nil.
    reflexivity.
    destruct a.
    destruct p.
    simpl; intros.
    elim (lifted_repr t c d).
    intros.
    elim (IHctx c d).
    intros.
    subst t; subst ctx.
    exists (Some (s, x) :: x0)%list.
    reflexivity.
    intuition.
    intuition.
    simpl.
    intros; elim (IHctx c d H).
    intros.
    exists (None :: x)%list.
    rewrite H0; reflexivity.
Qed.

Lemma lifting_context_respects_occurance_r : forall (ctx : context) (c d v : nat),
    c <= v ->
    var_used ctx v <-> var_used (lift_context ctx c d) (v + d)
.
Proof.
    intro ctx; induction ctx.
    easy.
    destruct a.
    destruct p.
    simpl; intros.
    rewrite <- lifting_respects_occurance_r by exact H.
    apply or_iff_compat_l.
    now apply IHctx.
    simpl; intros.
    now apply IHctx.
Qed.

Lemma lower_context_c_0 : forall (ctx : context) (c : nat),
    lower_context ctx c 0 = ctx
.
Proof.
    intro ctx; induction ctx.
    easy.
    destruct a.
    destruct p.
    intros; simpl.
    rewrite lower_c_0; rewrite IHctx; reflexivity.
    intros; simpl.
    now rewrite IHctx.
Qed.

Lemma lift_lower_context_swap : forall ctx : context, forall c d p v : nat, 
    (forall v, var_used ctx v -> d + c <= v -> d + c + p <= v) ->
    lift_context (lower_context ctx (d + c) p) c v = lower_context (lift_context ctx c v) (d + v + c) p
.
Proof.
    intro ctx; induction ctx.
    easy.
    simpl; intros.
    destruct a.
    destruct p0.
    simpl.
    rewrite lift_lower_swap_ex by intuition.
    rewrite IHctx by intuition.
    reflexivity.
    rewrite IHctx by intuition.
    reflexivity.
Qed.

Lemma var_used_lift : forall (ctx : context) (c d v : nat),
    var_used ctx v 
    <-> 
    (
        if Compare_dec.lt_dec v c then var_used (lift_context ctx c d) v
        else var_used (lift_context ctx c d) (v + d)
    )
.
Proof.
    intro ctx; induction ctx.

    intros.
    set (H := Compare_dec.lt_dec v c).
    simpl; tauto.

    intros.
    destruct a.
    destruct p.
    simpl.
    set (H := lifting_respects_occurance t c d v).
    set (H0 := IHctx c d v).
    generalize H H0.
    set (H1 := Compare_dec.lt_dec v c).
    assert (
        (if H1 then (var_occurs (lift t c d) v \/ var_used (lift_context ctx c d) v)
        else (var_occurs (lift t c d) (v + d) \/ var_used (lift_context ctx c d) (v + d)))
        =
        ((if H1 then var_occurs (lift t c d) v
        else var_occurs (lift t c d) (v + d))
        \/
        (if H1 then var_used (lift_context ctx c d) v
        else var_used (lift_context ctx c d) (v + d)))
    ) by (now destruct H1).
    rewrite H2.
    tauto.
    simpl.
    apply IHctx.
Qed.

Lemma var_used_lift_l : forall (ctx : context) (c d v : nat),
    v < c ->
    var_used ctx v <-> var_used (lift_context ctx c d) v
.
Proof.
    intros.
    generalize (var_used_lift ctx c d v).
    destruct (Compare_dec.lt_dec v c); tauto || omega. 
Qed.

Lemma var_used_lift_r : forall (ctx : context) (c d v : nat),
    c <= v ->
    var_used ctx v <-> var_used (lift_context ctx c d) (v + d)
.
Proof.
    intros.
    generalize (var_used_lift ctx c d v).
    destruct (Compare_dec.lt_dec v c); tauto || omega. 
Qed.

Lemma has_type_lower : forall (ctx : context) (slot c d : nat) (t : term),
    ctx[slot] := t ->
    (lower_context ctx c d)[slot] := (lower t c d)
.
Proof.
    intro ctx; induction ctx.
    unfold has_type.
    intro slot; destruct slot; simpl; tauto.
    intro slot; destruct slot.
    destruct a.
    destruct p.
    unfold has_type; simpl.
    intros; congruence.
    unfold has_type; simpl.
    tauto.
    intros c d t.
    change (
        (a :: ctx)%list [S slot] := t
    ) with (
        ctx[slot] := t
    ).
    change (
        (lower_context (a :: ctx) c d)%list [S slot] := lower t c d
    ) with (
        (lower_context ctx c d)[slot] := lower t c d
    ).
    apply IHctx.
Qed.

Lemma lift_context_inj : forall (l r : context) (c d : nat),
    lift_context l c d = lift_context r c d
    <->
    l = r
.
Proof.
    intro l; induction l.
    intro r; destruct r; easy.

    destruct a.
    destruct p.
    simpl.
    intro r; destruct r.
    easy.
    destruct o.
    destruct p.
    intros.
    simpl.
    split.
    intro H; injection H.
    intros.
    apply IHl in H0.
    apply lift_injection in H1.
    congruence.
    intros.
    injection H; intros.
    congruence.
    easy.
    intro; destruct r.
    easy.
    destruct o.
    easy.
    intros; split.
    intro H; injection H; intros.
    apply IHl in H0; congruence.
    intro H; injection H; intros; congruence.
Qed.

Lemma lift_subst_context_unfold : forall (ctx : context) (N : term) (c d v : nat),
    c <= v ->
    subst_context (lift_context ctx c d) (v + d) (lift N c d) = lift_context (subst_context ctx v N) c d
.
Proof.
    intro ctx; induction ctx.
    easy.
    destruct a.
    destruct p.
    simpl.
    intros.
    rewrite (lift_subst_unfold _ _ _ _ _ H).
    rewrite (IHctx _ _ _ _ H).
    reflexivity.
    simpl.
    intros.
    rewrite (IHctx _ _ _ _ H).
    reflexivity.
Qed.

Lemma ctx_subst_erase : forall (ctx : context) (v : nat) (N : term),
    (var_used ctx v -> False) ->
    subst_context ctx v N = ctx
.
Proof.
    intro ctx; induction ctx.
    easy.
    destruct a.
    destruct p.
    simpl; intros.
    rewrite subst_erase by tauto.
    rewrite IHctx by tauto.
    reflexivity.
    intros.
    simpl.
    simpl in H.
    rewrite IHctx by tauto.
    reflexivity.
Qed.

Lemma ctx_subst_split : forall (l r : context) (v : nat) (N : term),
    subst_context (l ++ r)%list v N = (subst_context l v N ++ subst_context r v N)%list
.
Proof.
    intro l; induction l.
    easy.
    intros.
    destruct a.
    destruct p.
    simpl.
    now rewrite IHl.
    simpl.
    now rewrite IHl.
Qed.

Lemma ctx_subst_none : forall (mid v : nat) (N : term),
    subst_context (List.repeat None mid) v N = List.repeat None mid
.
Proof.
    intro mid; induction mid.
    easy.
    simpl; intros.
    now rewrite IHmid.
Qed.

Lemma ctx_subst_length : forall (ctx : context) (v : nat) (N : term),
    List.length (subst_context ctx v N) = List.length ctx
.
Proof.
    intro ctx; induction ctx.
    easy.
    intros; destruct a.
    destruct p.
    simpl.
    now rewrite IHctx.
    simpl.
    now rewrite IHctx.
Qed.

Lemma subst_context_Some : forall (ctx : context) (v1 v2 : nat) (t N : term),
    ctx[v1] := t ->
    (subst_context ctx v2 N)[v1] := subst t v2 N
.
Proof.
    intro ctx; induction ctx.
    intro v1; destruct v1; unfold has_type; easy.
    intro v1; destruct v1.
    destruct a.
    destruct p.
    unfold has_type; simpl.
    intros; congruence.
    unfold has_type; simpl.
    tauto.
    destruct a.
    destruct p.
    simpl.
    unfold has_type; simpl.
    apply IHctx.
    unfold has_type; simpl.
    apply IHctx.
Qed.

Lemma lower_none : forall (mid c d : nat),
    lower_context (List.repeat None mid) c d = List.repeat None mid
.
Proof.
    intro mid; induction mid.
    easy.
    simpl; intros; rewrite IHmid.
    reflexivity.
Qed.

Lemma lift_context_merge : forall (ctx : context) (v n m : nat),
    lift_context (lift_context ctx v n) v m = lift_context ctx v (n + m)
.
Proof.
    intro ctx; induction ctx.
    easy.

    destruct a.
    destruct p.
    simpl.
    intros.
    rewrite lift_merge; rewrite IHctx.
    reflexivity.
    intros.
    simpl.
    rewrite IHctx.
    reflexivity.
Qed.