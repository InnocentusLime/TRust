Require List.
Require Import Term.
Require Import String.
Require Import Typing.
Require Import Relations.
Require Import TermReduction.

Lemma abs_typing : forall (ctx : context) (str : string) (arg_type body : term),
    ctx |- Abs str arg_type body := ? ->
    (ctx |- arg_type := ?) /\ (({str == arg_type} :: ctx) |- body := ?)
.
Proof.
    intros.
    destruct H.
    set (t := Abs str arg_type body).
    assert (t = Abs str arg_type body) by (now subst t).
    rewrite <- H0 in H.
    generalize ctx t x H str arg_type body H0.
    clear H H0 t arg_type body x str ctx.
    intros ctx t x H.
    induction H; try easy.

    intros.
    injection H1.
    intros.
    subst str0; subst arg_type0; subst body0.
    split.
    exists SmallKind; exact H.
    exists range; exact H0.

    intros.
    injection H1.
    intros.
    subst str0; subst arg_type0; subst body0.
    split.
    exists (TypeKind i); exact H.
    exists range; exact H0.

    intros.
    injection H1.
    intros.
    subst str0; subst arg_type0; subst body0.
    split.
    exists PropKind; exact H.
    exists range; exact H0.
Qed.

Lemma abs_arg_type : forall (ctx : context) (str : string) (arg_type body : term),
    ctx |- Abs str arg_type body := ? ->
    (ctx |- arg_type := SmallKind) \/ (ctx |- arg_type := PropKind) \/ (exists (i : nat), ctx |- arg_type := TypeKind i)
.
Proof.
    intros.
    destruct H.
    set (t := Abs str arg_type body).
    assert (t = Abs str arg_type body) by (now subst t).
    rewrite <- H0 in H.
    generalize ctx t x H str arg_type body H0.
    clear H H0 t arg_type body x str ctx.
    intros ctx t x H.
    induction H; try easy.

    intros.
    injection H1; intros.
    subst arg_type0.
    tauto.

    intros.
    injection H1; intros.
    subst arg_type0.
    eauto.

    intros.
    injection H1; intros.
    subst arg_type0.
    tauto.
Qed.

Corollary abs_typing_forall : forall (ctx : context) (str : string) (arg_type body : term),
    ctx |- Abs str arg_type body := ? ->
    exists T, ctx |- Abs str arg_type body := Forall str arg_type T
.
Proof.
    intros.
    assert (H0 := H).
    apply abs_typing in H.
    apply abs_arg_type in H0.
    destruct H.
    destruct H1.
    exists x.
    destruct H0.
    now apply TAbsSmall.
    destruct H0.
    now apply TAbsProp.
    destruct H0.
    now apply (TAbsType _ _ _ _ _ x0).
Qed.

Lemma app_typing : forall (ctx : context) (l r : term),
    ctx |- App l r := ? ->
    exists (str : string) (domain range : term), (ctx |- l := Forall str domain range) /\ (ctx |- r := domain)
.
Proof.
    intros ctx l r H.
    destruct H.
    set (t := App l r).
    assert (t = App l r) by (now subst t).
    rewrite <- H0 in H.
    generalize ctx t x H l r H0.
    clear H0 H t l r x ctx.
    intros ctx t x H.
    induction H; try easy.

    intros.
    injection H1; intros.
    subst r0; subst l0.
    exists str; exists domain; exists range.
    tauto.
Qed.

Lemma forall_typing : forall (ctx : context) (str : string) (domain range : term),
    ctx |- Forall str domain range := ? ->
    (exists (i : nat), (ctx |- domain := TypeKind i) /\ (({str == domain} :: ctx) |- range := TypeKind i)) \/
    ((ctx |- domain := SmallKind) /\ (({str == domain} :: ctx) |- range := PropKind)) \/
    ((ctx |- domain := PropKind) /\ (({str == domain} :: ctx) |- range := PropKind)) \/
    (exists (i : nat), (ctx |- domain := TypeKind i) /\ (({str == domain} :: ctx) |- range := PropKind)) \/
    ((ctx |- domain := SmallKind) /\ (({str == domain} :: ctx) |- range := SmallKind)) \/
    ((ctx |- domain := PropKind) /\ (({str == domain} :: ctx) |- range := SmallKind))
.
Proof.
    intros ctx str domain range H.
    destruct H.
    set (t := Forall str domain range).
    assert (t = Forall str domain range) by (now subst t).
    rewrite <- H0 in H.
    generalize ctx t x H str domain range H0.
    clear H0 H t str domain range x ctx.
    intros ctx t x H.
    induction H; try easy.

    intros.
    injection H1.
    intros.
    subst str0; subst domain0; subst range0.
    eauto.

    intros.
    injection H1.
    intros.
    subst str0; subst domain0; subst range0.
    eauto.

    intros.
    injection H1.
    intros.
    subst str0; subst domain0; subst range0.
    eauto.

    intros.
    injection H1.
    intros.
    subst str0; subst domain0; subst range0.
    right.
    right.
    right.
    left.
    eauto.

    intros.
    injection H1.
    intros.
    subst str0; subst domain0; subst range0.
    tauto.

    intros.
    injection H1.
    intros.
    subst str0; subst domain0; subst range0.
    tauto.
Qed.

Lemma nat_rec_typing : forall (ctx : context) (choice zero step num : term),
    ctx |- NatRec choice zero step num := ? ->
    (ctx |- choice := Nat ===> SmallKind) /\ 
    (ctx |- zero := App choice NatO) /\ 
    (ctx |- step := Forall "n"%string Nat (App (lift choice 0 1) (Var 0) ===> App (lift choice 0 2) (App NatSucc (Var 1)))) /\
    (ctx |- num := Nat)
.
Proof.
    intros ctx choice zero step num H.
    destruct H.
    set (t := NatRec choice zero step num).
    assert (t = NatRec choice zero step num) by (now subst t).
    rewrite <- H0 in H.
    generalize ctx t x H choice zero step num H0.
    clear H0 H t choice zero step num x ctx.
    intros ctx t x H.
    induction H; try easy.

    intros.
    injection H3.
    intros.
    subst num0; subst step0; subst zero0; subst choice0.
    tauto.
Qed.
