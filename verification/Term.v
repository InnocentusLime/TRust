(*
    The `Term.v` module declares the data which encodes unnamed terms of the
    interior representation. You may notice that that the term remembers
    strings at the abstractions. That is for easy naming of the unnamed terms
    which are then used for display.

    For the unnamed representation, we are using De Brujin indices.
    https://en.wikipedia.org/wiki/De_Bruijn_index
*)

Require Import Setoid.
Require Import String.
Require Import PeanoNat.
Require Import Peano_dec.
Require Import Relations.

(* A useful logical lemma *)
Lemma logic_or_impl : forall (A B C D : Prop), (A -> C) -> (B -> D) -> (A \/ B -> C \/ D).
Proof.
    tauto.
Qed.
Lemma or_iff : forall (A B C D : Prop), (A <-> B) -> (C <-> D) -> (A \/ C <-> B \/ D).
Proof.
    tauto.
Qed.

(*
    The term definition. Note that even though it stores the strings, they play
    no role on the theoretical level and only used to convert back to named
    terms without any problems, like Benjamin Pierce does in his ML impls of
    different calculi.

    Ironically, keeping the strings around brings in more complexities.
*)
Inductive term : Set :=
| NatO : term
| NatSucc : term
| Nat : term
| NatRec : term -> term -> term -> term -> term
| App : term -> term -> term
| Abs : string -> term -> term -> term
| Var : nat -> term
| SmallKind : term
| PropKind : term
| TypeKind : nat -> term
| Forall : string -> term -> term -> term
.

Notation "x ===> y" := (Forall "_"%string x y) (at level 80, right associativity).

(*
    To define substitution for De Brujin terms, a notion of
    lifting is used.
*)
Fixpoint lift (t : term) (c : nat) (d : nat) : term :=
    match t with
    | NatO => NatO
    | NatSucc => NatSucc
    | Nat => Nat
    | NatRec x1 x2 x3 x4 => NatRec (lift x1 c d) (lift x2 c d) (lift x3 c d) (lift x4 c d)
    | App l r => App (lift l c d) (lift r c d)
    | Abs str typ body => Abs str (lift typ c d) (lift body (c + 1) d)
    | Var x => if x <? c then Var x else Var (x + d)
    | SmallKind => SmallKind
    | PropKind => PropKind
    | TypeKind x => TypeKind x
    | Forall str typ body => Forall str (lift typ c d) (lift body (c + 1) d)
    end
.

(*
    Similary one can define a lowering function. That function
    is used in the definition of substitution too
*)
Fixpoint lower (t : term) (c : nat) (d : nat) : term :=
    match t with
    | NatO => NatO
    | NatSucc => NatSucc
    | Nat => Nat
    | NatRec x1 x2 x3 x4 => NatRec (lower x1 c d) (lower x2 c d) (lower x3 c d) (lower x4 c d)
    | App l r => App (lower l c d) (lower r c d)
    | Abs str typ body => Abs str (lower typ c d) (lower body (c + 1) d)
    | Var x => if x <? c then Var x else Var (x - d)
    | SmallKind => SmallKind
    | PropKind => PropKind
    | TypeKind x => TypeKind x
    | Forall str typ body => Forall str (lower typ c d) (lower body (c + 1) d)
    end
.

(* Some shortcuts *)
Definition lift1 (t : term) := lift t 0 1.
Definition lower1 (t : term) := lower t 0 1.
Definition clean_after_subst (t : term) : term := lower t 0 1.

(*
    The substitution itself.
*)
Fixpoint subst (t : term) (v : nat) (n : term) : term :=
    match t with
    | NatO => NatO
    | NatSucc => NatSucc
    | Nat => Nat
    | NatRec x1 x2 x3 x4 => NatRec (subst x1 v n) (subst x2 v n) (subst x3 v n) (subst x4 v n)
    | App l r => App (subst l v n) (subst r v n)
    | Abs str typ body => Abs str (subst typ v n) (subst body (v + 1) (lift1 n))
    | Var v' => if v =? v' then n else Var v'
    | SmallKind => SmallKind
    | PropKind => PropKind
    | TypeKind x => TypeKind x
    | Forall str typ body => Forall str (subst typ v n) (subst body (v + 1) (lift1 n))
    end
.

(*
    The top substitution is shortcut function, which is used
    in the definition of the reduction.
*)
Definition top_subst (target : term) (val : term) : term := clean_after_subst (subst target 0 (lift1 val)).

(*
    We define the equality of terms, because the default equality
    (`=`) will force to take the strings at the abstractions into
    account which is not what we want.
*)
Fixpoint term_eq (l r : term) : Prop :=
    match l, r with
    | NatO, NatO => True
    | NatSucc, NatSucc => True
    | Nat, Nat => True
    | NatRec x1 x2 x3 x4, NatRec y1 y2 y3 y4 => term_eq x1 y1 /\ term_eq x2 y2 /\ term_eq x3 y3 /\ term_eq x4 y4
    | App x1 x2, App y1 y2 => term_eq x1 y1 /\ term_eq x2 y2
    | Abs _ x1 x2, Abs _ y1 y2 => term_eq x1 y1 /\ term_eq x2 y2
    | Var x, Var y => x = y
    | SmallKind, SmallKind => True
    | PropKind, PropKind => True
    | TypeKind x, TypeKind y => x = y
    | Forall _ x1 x2, Forall _ y1 y2 => term_eq x1 y1 /\ term_eq x2 y2
    | _, _ => False
    end
.

(* 
    Some notations. We write "a" to distinguish from the default
    equality. "a" stands for "alpha".
*)
Notation "x =a y" := (term_eq x y) (at level 80, no associativity).
Notation "x <>a y" := (term_eq x y -> False) (at level 80, no associativity).

(*
    A small lemma that the alpha equality is a decidable relation.
*)
Lemma term_eq_dec : forall (l r : term), {l =a r} + {l <>a r}.
Proof.
    intro.
    induction l; intro; destruct r; 
    try (elim (IHl1 r1));
    try (elim (IHl2 r2));
    try (elim (IHl3 r3));
    try (elim (IHl4 r4));
    try intros;
    try (
        (left; simpl; exact I) || 
        (right; simpl; intro F; exact F) || 
        (left; simpl; (repeat split; assumption)) ||
        (right; simpl; easy) ||
        (simpl; apply Nat.eq_dec)
    ).
Qed.

(* 
    We then introduce a notation to use the equality inside
    some functions.
*)
Notation "x =a? y" := (term_eq_dec x y) (at level 80, no associativity).

(*
    Finally we prove that alpha equality is an equivalence
    relation...
*)
Lemma alpha_eq_equiv : equiv term term_eq.
Proof.
    repeat split.

    unfold reflexive.
    intro; induction x; try easy.

    unfold transitive.
    intro; 
    induction x; 
    intros;
    destruct y; destruct z; 
    simpl;
    repeat split;
    try (simpl in H; simpl in H0);
    try (
        easy || 
        (
            now (apply (IHx1 y1)) ||
            now (apply (IHx2 y2)) ||
            now (apply (IHx3 y3)) ||
            now (apply (IHx4 y4))
        ) ||
        now (transitivity n0)
    ).

    unfold symmetric.
    intro;
    induction x;
    intro;
    destruct y;
    simpl;
    repeat split;
    try (
        easy ||
        (
            now (apply (IHx1 y1)) ||
            now (apply (IHx2 y2)) ||
            now (apply (IHx3 y3)) ||
            now (apply (IHx4 y4))
        ) ||
        now (symmetry n)
    ).
Qed.

(*
    And declare that to make setoid rewriting work with
    it.
*)
Add Relation term term_eq
    reflexivity proved by (proj1 alpha_eq_equiv)
    symmetry proved by (proj2 (proj2 alpha_eq_equiv))
    transitivity proved by (proj1 (proj2 alpha_eq_equiv))
as nbu_relation_1.

(*
    We check that lifting respects alpha equality.
*)
Lemma lifting_respects_alpha_eq : forall (l r : term) (c d : nat), l =a r -> lift l c d =a lift r c d.
Proof.
    intro.
    induction l; intros; destruct r; 
    try (
        easy ||
        (
            simpl;
            simpl in H;
            repeat split;
            (apply IHl1; apply H || assumption) || 
            (apply IHl2; apply H || assumption) ||
            (apply IHl3; apply H || assumption) ||
            (apply IHl4; apply H || assumption)
        )
    ).

    simpl.
    simpl in H.
    assert ((n <? c) = (n0 <? c)).
    now rewrite H.
    rewrite H0; rewrite H.
    easy.
Qed.

(*
    We check that lowering respects alpha equality.
*)
Lemma lowering_respects_alpha_eq : forall (l r : term) (c d : nat), l =a r -> lower l c d =a lower r c d.
Proof.
    intro.
    induction l; intros; destruct r; 
    try (
        easy ||
        (
            simpl;
            simpl in H;
            repeat split;
            (apply IHl1; apply H || assumption) || 
            (apply IHl2; apply H || assumption) ||
            (apply IHl3; apply H || assumption) ||
            (apply IHl4; apply H || assumption)
        )
    ).

    simpl.
    simpl in H.
    assert ((n <? c) = (n0 <? c)).
    now rewrite H.
    rewrite H0; rewrite H.
    easy.
Qed.

(*
    Finally we check that substitution respecths alpha
    equality.
*)
Lemma subst_respects_alpha_eq : forall (l l' r r' : term) (n : nat), l =a l' -> r =a r' -> subst l n r =a subst l' n r'.
Proof.
    intro.
    induction l; intros; destruct l'; 
    try easy;
    try (
        simpl; simpl in H;
        repeat split;
        (apply IHl1; apply H || assumption || apply lifting_respects_alpha_eq) || 
        (apply IHl2; apply H || assumption || apply lifting_respects_alpha_eq) ||
        (apply IHl3; apply H || assumption || apply lifting_respects_alpha_eq) ||
        (apply IHl4; apply H || assumption || apply lifting_respects_alpha_eq) ||
        easy
    ).

    assumption.
    simpl in H; rewrite H.
    simpl.
    destruct (n0 =? n1); assumption || reflexivity.
    assumption.
Qed.

(*
=============================================================================================================================
The next theorems are properties of `lifting`, `lowering` and `subst` which are used in the proof of the theorems
related to typing. As result we develop some intuition and some tools to reason about these operations.
*)

(*
    A lemma about merging two lifts into one lift. The theorem can be generalized:

    forall (target : term) (v n m d : nat), d <= n -> lift (lift target v n) (v + d) m = lift target v (n + m)
*)
Lemma lift_merge : forall (target : term) (v n m : nat), lift (lift target v n) v m = lift target v (n + m).
Proof.
    intro.
    induction target; 
    try (
        easy ||
        (
            intros;
            simpl;
            repeat (
                rewrite IHtarget1 ||
                rewrite IHtarget2 ||
                rewrite IHtarget3 ||
                rewrite IHtarget4
            );
            reflexivity
        )
    ).

    intros.
    simpl.
    case_eq (n <? v).
    intros.
    simpl.
    rewrite H.
    reflexivity.
    intros.
    simpl.
    case_eq (n + n0 <? v).
    intros.
    exfalso.
    apply Nat.ltb_ge in H.
    apply Nat.ltb_lt in H0.
    assert (n + n0 < n).
    apply (Nat.lt_le_trans _ v _); assumption.
    set (H2 := Plus.le_plus_r n0 n).
    apply Lt.le_not_lt in H2.
    rewrite Nat.add_comm in H2.
    exact (H2 H1).
    intros.
    now rewrite Nat.add_assoc.
Qed.

(*
    A function which checks if a variable occurs inside the term
*)
Fixpoint var_occurs (t : term) (n : nat) : Prop :=
    match t with
    | NatO => False
    | NatSucc => False
    | Nat => False
    | NatRec x1 x2 x3 x4 => (var_occurs x1 n) \/ (var_occurs x2 n) \/ (var_occurs x3 n) \/ (var_occurs x4 n)
    | App x1 x2 => (var_occurs x1 n) \/ (var_occurs x2 n)
    | Abs _ typ body => (var_occurs typ n) \/ (var_occurs body (S n))
    | Var v => v =n 
    | SmallKind => False
    | PropKind => False
    | TypeKind _ => False
    | Forall _ typ body => (var_occurs typ n) \/ (var_occurs body (S n))
    end
.

(*
    Occurance is a decidable property
*)
Theorem var_occurs_dec : forall (t : term) (n : nat), { var_occurs t n } + { var_occurs t n -> False }.
Proof.
    intro.
    induction t;
    intro;
    try (elim (IHt1 n));
    try (elim (IHt2 n));
    try (elim (IHt2 (S n)));
    try (elim (IHt3 n));
    try (elim (IHt4 n));
    try intros;
    try ((right; easy) || (solve [left; simpl; auto]) || (solve [right; intro; simpl in H; intuition])).

    simpl.
    apply eq_nat_dec.
Qed.

(* If the var doesn't occur, we don't change anything with substituiton *)
Theorem subst_erase : forall (t : term) (v : nat) (N : term), (var_occurs t v -> False) -> subst t v N = t.
Proof.
    intro.
    induction t; 
    intros;
    simpl;
    simpl in H;
    try (
        easy || 
        (
            repeat (
                (rewrite IHt1; auto) ||
                (rewrite IHt2; auto) ||
                (rewrite IHt3; auto) ||
                (rewrite IHt4; auto)
            )
        )
    ).

    rewrite Nat.add_1_r; auto.
    case_eq (v =? n); try easy.
    intros; exfalso.
    apply EqNat.beq_nat_true in H0.
    symmetry in H0; exact (H H0).
    rewrite Nat.add_1_r; auto.
Qed.

(* Lift lets us get rid of some variables *)
Theorem lifting_destroys : forall (t : term) (c : nat) (d : nat), (forall (n : nat), (c <= n) -> (n < c + d) -> var_occurs (lift t c d) n -> False).
Proof.
    intro.
    induction t;
    intros;
    simpl in H1;
    try (
        easy || (
            repeat (
                destruct H1 || (now apply (IHt1 c d n)) || (now apply (IHt2 c d n)) || 
                (now apply (IHt3 c d n)) || (now apply (IHt4 c d n)) || 
                (
                    apply (IHt2 (c + 1) d (S n)); 
                    (
                        (rewrite Nat.add_1_r; now apply le_n_S) || 
                        (rewrite Nat.add_comm; rewrite Nat.add_assoc; rewrite Nat.add_1_r; apply Lt.lt_n_S; rewrite Nat.add_comm; assumption) ||
                        assumption
                    )
                ) || 
                easy
            )
        )
    ). (* Bless this proof script :3 *)

    case_eq (n <? c); intro; rewrite H2 in H1; simpl in H1.
    apply Nat.ltb_lt in H2.
    subst n0.
    apply Lt.le_lt_or_eq in H; destruct H.
    exact (Lt.lt_asym c n H H2).
    subst n.
    exact (Lt.lt_irrefl c H2).
    apply Nat.ltb_ge in H2.
    subst n0.
    apply Nat.le_lt_add_lt in H0.
    apply Lt.le_lt_or_eq in H2; destruct H2.
    exact (Lt.lt_asym c n H1 H0).
    subst c.
    exact (Lt.lt_irrefl n H0).
    apply le_n.
Qed.

(* 
    An algebraic lemma which lets you swap lifting around.
*)
Lemma lift_swap : forall N : term, forall c d p : nat, lift (lift N (d + c) p) c 1 = lift (lift N c 1) (d + 1 + c) p.
Proof.
    intro N.
    induction N; intros; simpl; 
    try (rewrite IHN1);
    try (rewrite IHN2);
    try (rewrite IHN3);
    try (rewrite IHN4);
    try easy.

    assert (lift (lift N2 (d + c + 1) p) (c + 1) 1 = lift (lift N2 (c + 1) 1) (d + 1 + c + 1) p).
    rewrite <- Nat.add_assoc.
    rewrite <- Nat.add_assoc.
    apply IHN2.
    now rewrite H.

    (* Reasoning about numbers in Coq is a bit of a pain for me for now xP *)
    case_eq (n <? c); intros.
    assert (n <? d + c = true).
    apply Nat.ltb_lt; apply Nat.ltb_lt in H.
    now apply Nat.lt_lt_add_l.
    rewrite H0.
    simpl.
    assert (n <? d + 1 + c = true).
    apply Nat.ltb_lt; apply Nat.ltb_lt in H0.
    rewrite <- Nat.add_assoc; rewrite (Nat.add_comm 1 c); rewrite Nat.add_assoc.
    now apply Nat.lt_lt_add_r.
    rewrite H; rewrite H1.
    reflexivity.
    case_eq (n <? d + c); intros.
    assert (n + 1 <? d + 1 + c = true).
    apply Nat.ltb_lt; apply Nat.ltb_lt in H0.
    rewrite <- Nat.add_assoc; rewrite (Nat.add_comm 1 c); rewrite Nat.add_assoc.
    now apply Plus.plus_lt_compat_r.
    simpl.
    rewrite H; rewrite H1.
    reflexivity.
    simpl.
    assert (n + p <? c = false).
    apply Nat.ltb_ge; apply Nat.ltb_ge in H.
    now apply Plus.le_plus_trans.
    assert (n + 1 <? d + 1 + c = false).
    apply Nat.ltb_ge; apply Nat.ltb_ge in H0.
    rewrite <- Nat.add_assoc; rewrite (Nat.add_comm 1 c); rewrite Nat.add_assoc.
    now apply Plus.plus_le_compat_r.
    rewrite H1; rewrite H2.
    rewrite <- Nat.add_assoc; rewrite (Nat.add_comm p 1); rewrite Nat.add_assoc.
    reflexivity.

    assert (lift (lift N2 (d + c + 1) p) (c + 1) 1 = lift (lift N2 (c + 1) 1) (d + 1 + c + 1) p).
    rewrite <- Nat.add_assoc.
    rewrite <- Nat.add_assoc.
    apply IHN2.
    now rewrite H.
Qed.

(*
    An algberaic theorem to swap substitution of to a lifted term in a
    lifted term to substitution and then lifting.
*)
Theorem lift_subst_unfold : forall (t N : term) (c d v : nat), 
    c <= v ->
    subst (lift t c d) (v + d) (lift N c d) = lift (subst t v N) c d.
Proof.
    intro.
    induction t; intros;
    simpl; 
    try (rewrite IHt1);
    try (rewrite IHt2);
    try (rewrite IHt3);
    try (rewrite IHt4);
    try easy.

    unfold lift1.
    assert (lift (lift N c d) 0 1 = lift (lift N 0 1) (c + 1) d).
    rewrite <- (Nat.add_0_r c).
    rewrite <- Nat.add_assoc; rewrite (Nat.add_comm 0 1); rewrite Nat.add_assoc.
    apply lift_swap.
    rewrite H0.
    set (N' := lift N 0 1).
    apply f_equal.
    rewrite (Nat.add_comm v d); rewrite <- Nat.add_assoc; rewrite (Nat.add_comm d (v + 1)).
    apply IHt2.
    exact (Plus.plus_le_compat_r c v 1 H).

    case_eq (n <? c); case_eq (v =? n); intros.
    exfalso.
    apply EqNat.beq_nat_true in H0; apply Nat.ltb_lt in H1; subst v; set (F := Nat.le_lt_trans _ _ _ H H1).
    exact (Lt.lt_irrefl _ F).
    simpl.
    rewrite H1.
    assert (v + d =? n = false).
    apply Nat.eqb_neq; apply Nat.eqb_neq in H0; apply Nat.ltb_lt in H1; intro.
    subst n.
    set (F := Nat.lt_le_trans _ _ _ H1 H).
    apply Nat.lt_nge in F; exact (F (Plus.le_plus_l _ _)).
    rewrite H2; reflexivity.
    simpl.
    assert (v + d =? n + d = true).
    apply Nat.eqb_eq; apply Nat.eqb_eq in H0.
    now apply Nat.add_cancel_r.
    rewrite H2; reflexivity.
    simpl.
    assert (v + d =? n + d = false).
    apply Nat.eqb_neq; apply Nat.eqb_neq in H0.
    intro.
    apply Nat.add_cancel_r in H2; exact (H0 H2).
    rewrite H2; rewrite H1; reflexivity.

    unfold lift1.
    assert (lift (lift N c d) 0 1 = lift (lift N 0 1) (c + 1) d).
    rewrite <- (Nat.add_0_r c).
    rewrite <- Nat.add_assoc; rewrite (Nat.add_comm 0 1); rewrite Nat.add_assoc.
    apply lift_swap.
    rewrite H0.
    set (N' := lift N 0 1).
    apply f_equal.
    rewrite (Nat.add_comm v d); rewrite <- Nat.add_assoc; rewrite (Nat.add_comm d (v + 1)).
    apply IHt2.
    exact (Plus.plus_le_compat_r c v 1 H).
Qed.

(*
    And algberaic theorem about lifting and lowering becoming an id.

    Possible generalization
    forall (t : term) (c d d1 : nat), d1 <= d -> lower (lift t c d) (c + d1) d = t.
*)
Theorem lift_lower_destruct : forall (t : term) (c d : nat), lower (lift t c d) c d = t.
Proof.
    intro.
    induction t; intros; 
    simpl;
    try (rewrite IHt1);
    try (rewrite IHt2);
    try (rewrite IHt3);
    try (rewrite IHt4);
    try easy.

    case_eq (n <? c); intro.
    simpl.
    rewrite H.
    reflexivity.
    simpl.
    assert (n + d <? c = false).
    apply Nat.ltb_ge; apply Nat.ltb_ge in H.
    now apply Plus.le_plus_trans.
    rewrite H0.
    rewrite Nat.add_sub.
    reflexivity.
Qed.

(*
    lower (lift t 0 (d + 1)) 1 = lift t 0 d
*)
Lemma lift_lower_compensate : forall (t : term) (c d : nat), lower (lift t c (d + 1)) (c + d) 1 = lift t c d.
Proof.
    intro; induction t; intros; 
    simpl;
    try (rewrite IHt1);
    try (rewrite IHt2);
    try (rewrite IHt3);
    try (rewrite IHt4);
    try easy.

    apply f_equal.
    rewrite <- (IHt2 (c + 1) d).
    rewrite <- Nat.add_assoc; rewrite (Nat.add_comm d 1); rewrite <- Nat.add_assoc.
    reflexivity.

    case_eq (n <? c); intro.
    assert (n <? c + d = true).
    apply Nat.ltb_lt; apply Nat.ltb_lt in H.
    now apply Nat.lt_lt_add_r.
    simpl.
    now rewrite H0.
    assert (n + (d + 1) <? c + d = false).
    apply Nat.ltb_ge; apply Nat.ltb_ge in H.
    rewrite (Nat.add_comm d 1); rewrite Nat.add_assoc.
    apply Plus.plus_le_compat_r.
    apply (Nat.le_trans _ n).
    assumption.
    rewrite Nat.add_1_r.
    constructor.
    constructor.
    simpl.
    rewrite H0.
    rewrite Nat.add_assoc.
    rewrite Nat.add_sub.
    reflexivity.

    apply f_equal.
    rewrite <- (IHt2 (c + 1) d).
    rewrite <- Nat.add_assoc; rewrite (Nat.add_comm d 1); rewrite <- Nat.add_assoc.
    reflexivity.
Qed.

Corollary lift_lower_compensate_simpl : forall (t : term) (d : nat), lower (lift t 0 (d + 1)) d 1 = lift t 0 d.
Proof.
    intros.
    exact (lift_lower_compensate t 0 d).
Qed.

(*
    A lemma to push lowering to the outside of substitution.
*)
Lemma defer_lower : forall (t N : term) (c d v : nat),
    c <= v ->
    lower (subst (lift t c d) (v + d) (lift N c d)) c d
    =
    subst t v N
.
Proof.
    intros.
    rewrite lift_subst_unfold.
    rewrite lift_lower_destruct.
    reflexivity.
    exact H.  
Qed.

(*
    A theorem which helps us to imagine terms as lifted
    ones.
*)
Theorem lifted_repr : forall (t : term) (c d : nat),
    (forall v : nat, var_occurs t v -> v < c \/ (c + d) <= v) ->
    exists t' : term, t = lift t' c d
.
Proof.
    intro t;
    induction t;
    intros.
    
    now exists NatO.
    now exists NatSucc.
    now exists Nat.
    elim (IHt4 c d); elim (IHt3 c d); elim (IHt2 c d); elim (IHt1 c d); intros.
    exists (NatRec x x0 x1 x2); subst t1; subst t2; subst t3; subst t4; reflexivity.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    intros; simpl in H; apply H; auto.
    elim (IHt2 c d); elim (IHt1 c d); intros.
    exists (App x x0); subst t1; subst t2; reflexivity.
    simpl in H; apply H; auto.
    simpl in H; apply H; auto.
    simpl in H; apply H; auto.

    elim (IHt2 (c + 1) d); elim (IHt1 c d); intros.
    exists (Abs s x x0); subst t1; subst t2; reflexivity.
    simpl in H; apply H; auto.
    simpl in H.
    destruct v.
    left.
    rewrite Nat.add_1_r; apply Nat.lt_0_succ.
    rewrite <- Nat.add_assoc; rewrite (Nat.add_comm 1 d); rewrite Nat.add_assoc; rewrite Nat.add_1_r; rewrite Nat.add_1_r.
    elim (H v (or_intror H1)).
    intros.
    left; exact (Lt.lt_n_S _ _ H2).
    intros.
    right; exact (le_n_S _ _ H2).
    simpl in H; apply H; auto.
    
    set (H' := H n).
    simpl in H'.
    set (H'' := H' (eq_refl n)).
    destruct H''.
    exists (Var n).
    simpl.
    assert (n <? c = true) by (now apply (Nat.ltb_lt n c)).
    now rewrite H1.
    assert (exists n0, n = n0 + d).
    exists (n - d).
    symmetry; apply Nat.sub_add.
    apply (Nat.le_trans d (c + d) n).
    rewrite Nat.add_comm.
    apply Nat.le_add_r.
    assumption.
    elim H1; intros.
    subst n; exists (Var x).
    simpl.
    assert (x <? c = false).
    apply Nat.ltb_ge.
    rewrite Nat.add_comm in H0; rewrite (Nat.add_comm x d) in H0; apply (Plus.plus_le_reg_l c x d) in H0.
    assumption.
    now rewrite H2.
    now exists SmallKind.
    now exists PropKind.
    now exists (TypeKind n).

    elim (IHt2 (c + 1) d); elim (IHt1 c d); intros.
    exists (Forall s x x0); subst t1; subst t2; reflexivity.
    simpl in H; apply H; auto.
    simpl in H.
    destruct v.
    left.
    rewrite Nat.add_1_r; apply Nat.lt_0_succ.
    rewrite <- Nat.add_assoc; rewrite (Nat.add_comm 1 d); rewrite Nat.add_assoc; rewrite Nat.add_1_r; rewrite Nat.add_1_r.
    elim (H v (or_intror H1)).
    intros.
    left; exact (Lt.lt_n_S _ _ H2).
    intros.
    right; exact (le_n_S _ _ H2).
    simpl in H; apply H; auto.
Qed.

(*
    When you lift, you preserve the occurance at some point
*)
Theorem lifting_respects_occurance : forall (t : term) (c d v : nat),
    var_occurs t v 
    <->
    (v < c -> var_occurs (lift t c d) v) /\ (c <= v -> var_occurs (lift t c d) (v + d))
.
Proof.
    intro; induction t; intros; split; 
    try (
        (solve [easy || (destruct (Nat.lt_ge_cases v c); intro H0; destruct H0; auto)]) || 
        (
            split;
            intro;
            simpl; simpl in H;
            repeat (
                destruct H || 
                (set (S1 := proj1 (proj1 (IHt1 c d v) H)); set (S2 := proj2 (proj1 (IHt1 c d v) H)); intuition) ||
                (set (S1 := proj1 (proj1 (IHt2 c d v) H)); set (S2 := proj2 (proj1 (IHt2 c d v) H)); intuition) ||
                (set (S1 := proj1 (proj1 (IHt3 c d v) H)); set (S2 := proj2 (proj1 (IHt3 c d v) H)); intuition) ||
                (set (S1 := proj1 (proj1 (IHt4 c d v) H)); set (S2 := proj2 (proj1 (IHt4 c d v) H)); intuition)
            )
        )
    ).

    intro H.
    inversion_clear H.
    simpl.
    destruct (Nat.lt_ge_cases v c).

    set (H2 := H0 H).
    repeat (destruct H2).

    assert (var_occurs t1 v); auto.
    apply (proj2 (IHt1 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.lt_not_le _ _ H F).

    assert (var_occurs t2 v); auto.
    apply (proj2 (IHt2 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.lt_not_le _ _ H F).

    assert (var_occurs t3 v); auto.
    apply (proj2 (IHt3 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.lt_not_le _ _ H F).

    assert (var_occurs t4 v); auto.
    apply (proj2 (IHt4 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.lt_not_le _ _ H F).

    set (H2 := H1 H).
    repeat (destruct H2).

    assert (var_occurs t1 v); auto.
    apply (proj2 (IHt1 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.le_not_lt _ _ H F).

    assert (var_occurs t2 v); auto.
    apply (proj2 (IHt2 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.le_not_lt _ _ H F).

    assert (var_occurs t3 v); auto.
    apply (proj2 (IHt3 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.le_not_lt _ _ H F).

    assert (var_occurs t4 v); auto.
    apply (proj2 (IHt4 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.le_not_lt _ _ H F).





    intro H.
    inversion_clear H.
    simpl.
    destruct (Nat.lt_ge_cases v c).

    set (H2 := H0 H).
    repeat (destruct H2).

    assert (var_occurs t1 v); auto.
    apply (proj2 (IHt1 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.lt_not_le _ _ H F).

    assert (var_occurs t2 v); auto.
    apply (proj2 (IHt2 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.lt_not_le _ _ H F).

    set (H2 := H1 H).
    repeat (destruct H2).

    assert (var_occurs t1 v); auto.
    apply (proj2 (IHt1 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.le_not_lt _ _ H F).

    assert (var_occurs t2 v); auto.
    apply (proj2 (IHt2 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.le_not_lt _ _ H F).


    right.
    rewrite Nat.add_1_r.
    refine (proj1 (proj1 (IHt2 _ _ _) H) _).
    exact (Lt.lt_n_S _ _ H0).
    right.
    rewrite Nat.add_1_r.
    refine (proj2 (proj1 (IHt2 _ _ _) H) _).
    exact (le_n_S _ _ H0).

    intro H.
    inversion_clear H.
    simpl.
    destruct (Nat.lt_ge_cases v c).

    set (H2 := H0 H).
    repeat (destruct H2).

    assert (var_occurs t1 v); auto.
    apply (proj2 (IHt1 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.lt_not_le _ _ H F).

    rewrite Nat.add_1_r in H2.
    assert (var_occurs t2 (S v)); auto.
    apply (proj2 (IHt2 (S c) d _)).
    split; try easy.
    intro F; exfalso.
    apply Le.le_S_n in F.
    exact (Lt.lt_not_le _ _ H F).

    set (H2 := H1 H).
    repeat (destruct H2).

    assert (var_occurs t1 v); auto.
    apply (proj2 (IHt1 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.le_not_lt _ _ H F).

    rewrite Nat.add_1_r in H2.
    assert (S (v + d) = S v + d) by easy.
    rewrite H3 in H2.
    assert (var_occurs t2 (S v)); auto.
    apply (proj2 (IHt2 (S c) d (S v))).
    split; try easy.
    intro F; exfalso.
    apply Lt.lt_S_n in F.
    exact (Lt.le_not_lt _ _ H F).

    assert (n <? c = true).
    now apply Nat.ltb_lt.
    now rewrite H.

    assert (n <? c = false).
    now apply Nat.ltb_ge.
    now rewrite H.

    intro H.
    destruct (Nat.lt_ge_cases v c).
    set (H1 := proj1 H H0).
    simpl in H1.
    case_eq (n <? c); intro.
    rewrite H2 in H1.
    exact H1.
    rewrite H2 in H1.
    simpl in H1.
    subst v.
    apply Nat.ltb_ge in H2.
    assert (n < c).
    apply (Nat.le_lt_trans n (n + d) c).
    apply Nat.le_add_r.
    assumption.
    exfalso.
    exact (Lt.le_not_lt _ _ H2 H1).
    set (H1 := proj2 H H0).
    simpl in H1.
    case_eq (n <? c); intro.
    rewrite H2 in H1.
    simpl in H1; subst n.
    apply Nat.ltb_lt in H2.
    exfalso.
    assert (v < c).
    apply (Nat.le_lt_trans v (v + d) c).
    apply Nat.le_add_r.
    assumption.
    exact (Lt.le_not_lt _ _ H0 H1).
    rewrite H2 in H1.
    simpl in H1; simpl.
    now apply (Nat.add_cancel_r) in H1.

    right.
    rewrite Nat.add_1_r.
    refine (proj1 (proj1 (IHt2 _ _ _) H) _).
    exact (Lt.lt_n_S _ _ H0).
    right.
    rewrite Nat.add_1_r.
    refine (proj2 (proj1 (IHt2 _ _ _) H) _).
    exact (le_n_S _ _ H0).

    intro H.
    inversion_clear H.
    simpl.
    destruct (Nat.lt_ge_cases v c).

    set (H2 := H0 H).
    repeat (destruct H2).

    assert (var_occurs t1 v); auto.
    apply (proj2 (IHt1 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.lt_not_le _ _ H F).

    rewrite Nat.add_1_r in H2.
    assert (var_occurs t2 (S v)); auto.
    apply (proj2 (IHt2 (S c) d _)).
    split; try easy.
    intro F; exfalso.
    apply Le.le_S_n in F.
    exact (Lt.lt_not_le _ _ H F).

    set (H2 := H1 H).
    repeat (destruct H2).

    assert (var_occurs t1 v); auto.
    apply (proj2 (IHt1 c d v)).
    split; try easy.
    intro F; exfalso.
    exact (Lt.le_not_lt _ _ H F).

    rewrite Nat.add_1_r in H2.
    assert (S (v + d) = S v + d) by easy.
    rewrite H3 in H2.
    assert (var_occurs t2 (S v)); auto.
    apply (proj2 (IHt2 (S c) d (S v))).
    split; try easy.
    intro F; exfalso.
    apply Lt.lt_S_n in F.
    exact (Lt.le_not_lt _ _ H F).
Qed.

(* Weaker version *)
Corollary lifting_respects_occurance_l : forall (t : term) (c d v : nat),
    v < c ->
    var_occurs t v <-> var_occurs (lift t c d) v
.
Proof.
    intros.
    split.
    intros.
    apply lifting_respects_occurance; easy.
    intros.
    refine (proj2 (lifting_respects_occurance t c d v) (conj (fun _ => H0) _)).
    intros.
    exfalso.
    exact (Lt.le_not_lt _ _ H1 H).
Qed.

(* Another weaker version *)
Corollary lifting_respects_occurance_r : forall (t : term) (c d v : nat),
    c <= v ->
    var_occurs t v <-> var_occurs (lift t c d) (v + d)
.
Proof.
    intros.
    split.
    intros.
    apply lifting_respects_occurance; easy.
    intros.
    refine (proj2 (lifting_respects_occurance t c d v) (conj _ (fun _ => H0))).
    intros.
    exfalso.
    exact (Lt.le_not_lt _ _ H H1).
Qed.

(* A theorem about splitting two substs *)
Theorem subst_split : forall (N1 : term) (v1 v2 : nat) (N2 N3 : term), 
    v1 <> v2 ->
    (var_occurs N3 v1 -> False) ->
    subst (subst N1 v1 N2) v2 N3 = subst (subst N1 v2 N3) v1 (subst N2 v2 N3)
.
Proof.
    intro.
    induction N1; try easy; intros.

    simpl.
    rewrite (IHN1_1 v1 v2 _ _ H H0).
    rewrite (IHN1_2 v1 v2 _ _ H H0).
    rewrite (IHN1_3 v1 v2 _ _ H H0).
    rewrite (IHN1_4 v1 v2 _ _ H H0).
    reflexivity.

    simpl.
    rewrite (IHN1_1 v1 v2 _ _ H H0).
    rewrite (IHN1_2 v1 v2 _ _ H H0).
    reflexivity.

    simpl.
    rewrite (IHN1_1 v1 v2 _ _ H H0).
    apply f_equal.
    unfold lift1.
    rewrite <- (lift_subst_unfold N2 N3 0 1 v2).
    apply (IHN1_2 (v1 + 1) (v2 + 1) _ _).
    intro.
    apply Nat.add_cancel_r in H1; exact (H H1).
    intro.
    apply lifting_respects_occurance_r in H1.
    exact (H0 H1).
    apply le_0_n.
    apply le_0_n.

    simpl.
    case_eq (v1 =? n); case_eq (v2 =? n); intros.
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    subst n.
    exfalso; exact (H H2).
    simpl.
    rewrite H2.
    reflexivity.
    simpl.
    rewrite H1.
    symmetry.
    now apply subst_erase.
    simpl.
    rewrite H1; rewrite H2.
    reflexivity.

    simpl.
    rewrite (IHN1_1 v1 v2 _ _ H H0).
    apply f_equal.
    unfold lift1.
    rewrite <- (lift_subst_unfold N2 N3 0 1 v2).
    apply (IHN1_2 (v1 + 1) (v2 + 1) _ _).
    intro.
    apply Nat.add_cancel_r in H1; exact (H H1).
    intro.
    apply lifting_respects_occurance_r in H1.
    exact (H0 H1).
    apply le_0_n.
    apply le_0_n.
Qed.

(*
    A theorem about substitution
    destroying a variable.
*)
Theorem subst_destroys : forall (t : term) (v : nat) (N : term),
    (var_occurs N v -> False) ->
    (var_occurs (subst t v N) v -> False)
.
Proof.
    intro; induction t; try easy.

    intros.
    simpl in H0.
    repeat (destruct H0).
    now apply (IHt1 v N).
    now apply (IHt2 v N).
    now apply (IHt3 v N).
    now apply (IHt4 v N).

    intros.
    simpl in H0.
    repeat (destruct H0).
    now apply (IHt1 v N).
    now apply (IHt2 v N).

    intros.
    simpl in H0.
    repeat (destruct H0).
    now apply (IHt1 v N).
    rewrite Nat.add_1_r in H0.
    apply (IHt2 (S v) (lift1 N)).
    unfold lift1.
    rewrite <- (Nat.add_1_r v).
    rewrite <- lifting_respects_occurance_r.
    assumption.
    apply le_0_n.
    exact H0.

    intros.
    simpl in H0.
    case_eq (v =? n); intro.
    rewrite H1 in H0.
    exact (H H0).
    rewrite H1 in H0.
    simpl in H0.
    apply Nat.eqb_neq in H1.
    symmetry in H0; exact (H1 H0).

    intros.
    simpl in H0.
    repeat (destruct H0).
    now apply (IHt1 v N).
    rewrite Nat.add_1_r in H0.
    apply (IHt2 (S v) (lift1 N)).
    unfold lift1.
    rewrite <- (Nat.add_1_r v).
    rewrite <- lifting_respects_occurance_r.
    assumption.
    apply le_0_n.
    exact H0.
Qed.

(* `lift t c 0` behaves like `id` *)
Theorem lift_c_0 : forall (t : term) (c : nat), lift t c 0 = t.
Proof.
    intro t; induction t; try easy.
    intro c; simpl; rewrite IHt1; rewrite IHt2; rewrite IHt3; rewrite IHt4; reflexivity.
    intro c; simpl; rewrite IHt1; rewrite IHt2; reflexivity.
    intro c; simpl; rewrite IHt1; rewrite IHt2; reflexivity.
    intro c.
    simpl.
    destruct (n <? c); try easy.
    now rewrite Nat.add_0_r.
    intro c; simpl; rewrite IHt1; rewrite IHt2; reflexivity.
Qed.

(* A theorem about preservation of a variable *)
Theorem subst_respects_occurance : forall (t N : term) (v1 v2 : nat),
    ((var_occurs N v1 /\ var_occurs t v2) \/ (var_occurs t v1 /\ v1 <> v2))
    <->
    (var_occurs (subst t v2 N) v1)
.
Proof.
    intro t; induction t; try (solve [tauto]).
    intros.
    split.
    intro H; destruct H.
    inversion_clear H.
    simpl in H1; destruct H1.
    simpl.
    left.
    apply IHt1.
    left; exact (conj H0 H).
    destruct H.
    right; left.
    apply IHt2.
    left; exact (conj H0 H).
    destruct H.
    right; right; left.
    apply IHt3; left; exact (conj H0 H).
    right; right; right.
    apply IHt4; left; exact (conj H0 H).
    inversion_clear H.
    simpl in H0; destruct H0.
    left.
    apply IHt1; right; exact (conj H H1).
    destruct H.
    right; left.
    apply IHt2; right; exact (conj H H1).
    destruct H.
    right; right; left.
    apply IHt3; right; exact (conj H H1).
    right; right; right.
    apply IHt4; right; exact (conj H H1).
    intros.
    simpl in H.
    destruct H.
    assert (var_occurs N v1 /\ var_occurs t1 v2 \/ var_occurs t1 v1 /\ v1 <> v2) by (now apply IHt1).
    simpl; destruct H0; (left; tauto) || (right; tauto).
    destruct H.
    assert (var_occurs N v1 /\ var_occurs t2 v2 \/ var_occurs t2 v1 /\ v1 <> v2) by (now apply IHt2).
    simpl; destruct H0; (left; tauto) || (right; tauto).
    destruct H.
    assert (var_occurs N v1 /\ var_occurs t3 v2 \/ var_occurs t3 v1 /\ v1 <> v2) by (now apply IHt3).
    simpl; destruct H0; (left; tauto) || (right; tauto).
    assert (var_occurs N v1 /\ var_occurs t4 v2 \/ var_occurs t4 v1 /\ v1 <> v2) by (now apply IHt4).
    simpl; destruct H0; (left; tauto) || (right; tauto).
    intros.
    split.
    intros.
    destruct H.
    inversion_clear H.
    simpl in H1; destruct H1.
    left; apply IHt1; auto.
    right; apply IHt2; auto.
    inversion_clear H.
    destruct H0.
    left; apply IHt1; auto.
    right; apply IHt2; auto.
    intros.
    destruct H.
    assert (var_occurs N v1 /\ var_occurs t1 v2 \/ var_occurs t1 v1 /\ v1 <> v2) by (now apply IHt1).
    simpl; destruct H0; (left; tauto) || (right; tauto).
    assert (var_occurs N v1 /\ var_occurs t2 v2 \/ var_occurs t2 v1 /\ v1 <> v2) by (now apply IHt2).
    simpl; destruct H0; (left; tauto) || (right; tauto).

    intros.
    split.
    intros.
    destruct H.
    inversion_clear H.
    simpl in H1; destruct H1.
    left; apply IHt1; auto.
    right; rewrite Nat.add_1_r; apply IHt2.    
    left.
    split; try assumption.
    rewrite <- Nat.add_1_r.
    unfold lift1; apply lifting_respects_occurance_r.
    apply le_0_n.
    assumption.
    inversion_clear H.
    destruct H0.
    left; apply IHt1; auto.
    right; apply IHt2.
    rewrite Nat.add_1_r.
    rewrite <- Nat.add_1_r at 1.
    unfold lift1; rewrite <- lifting_respects_occurance_r.
    right; split; try easy.
    injection.
    exact H1.
    apply le_0_n.
    intros. 
    intros.
    destruct H.
    assert (var_occurs N v1 /\ var_occurs t1 v2 \/ var_occurs t1 v1 /\ v1 <> v2) by (now apply IHt1).
    simpl; destruct H0; (left; tauto) || (right; tauto).
    assert (var_occurs (lift1 N) (S v1) /\ var_occurs t2 (S v2) \/ var_occurs t2 (S v1) /\ (S v1) <> (S v2)).
    apply IHt2.
    rewrite Nat.add_1_r in H.
    exact H.
    rewrite <- (Nat.add_1_r v1) in H.
    simpl; destruct H0.
    left.
    inversion_clear H0.
    rewrite <- (Nat.add_1_r v1) in H1.
    unfold lift1 in H1; apply <- lifting_respects_occurance_r in H1.
    split; try easy.
    right; exact H2.
    apply le_0_n.
    right.
    inversion_clear H0.
    split.
    right; exact H1.
    congruence.

    intros.
    split; intros.
    simpl.
    case_eq (v2 =? n); intros.
    destruct H.
    apply H.
    inversion_clear H.
    simpl in H1.
    apply Nat.eqb_eq in H0.
    congruence.
    destruct H.
    apply Nat.eqb_neq in H0.
    simpl in H.
    inversion_clear H.
    congruence.
    apply H.
    simpl in H.
    case_eq (v2 =? n); intro.
    rewrite H0 in H.
    left; auto.
    simpl.
    apply Nat.eqb_eq in H0.
    auto.
    rewrite H0 in H.
    right; split; try easy.
    apply Nat.eqb_neq in H0.
    congruence.

    intros.
    split.
    intros.
    destruct H.
    inversion_clear H.
    simpl in H1; destruct H1.
    left; apply IHt1; auto.
    right; rewrite Nat.add_1_r; apply IHt2.    
    left.
    split; try assumption.
    rewrite <- Nat.add_1_r.
    unfold lift1; apply lifting_respects_occurance_r.
    apply le_0_n.
    assumption.
    inversion_clear H.
    destruct H0.
    left; apply IHt1; auto.
    right; apply IHt2.
    rewrite Nat.add_1_r.
    rewrite <- Nat.add_1_r at 1.
    unfold lift1; rewrite <- lifting_respects_occurance_r.
    right; split; try easy.
    injection.
    exact H1.
    apply le_0_n.
    intros. 
    intros.
    destruct H.
    assert (var_occurs N v1 /\ var_occurs t1 v2 \/ var_occurs t1 v1 /\ v1 <> v2) by (now apply IHt1).
    simpl; destruct H0; (left; tauto) || (right; tauto).
    assert (var_occurs (lift1 N) (S v1) /\ var_occurs t2 (S v2) \/ var_occurs t2 (S v1) /\ (S v1) <> (S v2)).
    apply IHt2.
    rewrite Nat.add_1_r in H.
    exact H.
    rewrite <- (Nat.add_1_r v1) in H.
    simpl; destruct H0.
    left.
    inversion_clear H0.
    rewrite <- (Nat.add_1_r v1) in H1.
    unfold lift1 in H1; apply <- lifting_respects_occurance_r in H1.
    split; try easy.
    right; exact H2.
    apply le_0_n.
    right.
    inversion_clear H0.
    split.
    right; exact H1.
    congruence.
Qed.

Corollary subst_respects_occurance_l : forall (t N : term) (v1 v2 : nat),
    var_occurs N v1 /\ var_occurs t v2 
    ->
    var_occurs (subst t v2 N) v1
.
Proof.
    intros.
    intros.
    apply subst_respects_occurance.
    auto.
Qed.

Corollary subst_respects_occurance_r : forall (t N : term) (v1 v2 : nat),
    var_occurs t v1 /\ v1 <> v2
    ->
    var_occurs (subst t v2 N) v1
.
Proof.
    intros.
    intros.
    apply subst_respects_occurance.
    auto.
Qed.

(* A silly lemma used in a typing theorem *)
Lemma top_subst_subst_swap : forall (t N1 N2 : term) (v : nat), 
    top_subst (subst t (v + 1) (lift1 N2)) (subst N1 v N2) 
    = 
    subst (top_subst t N1) v N2
.
Proof.
    intros.
    unfold top_subst.
    unfold lift1.
    rewrite <- (lift_subst_unfold _ _ _ _ _ (le_0_n v)).
    rewrite <- subst_split.
    unfold clean_after_subst.
    set (T := subst t 0 (lift N1 0 1)).
    assert (exists T', T = lift T' 0 1).
    apply lifted_repr.
    intros.
    destruct v0.
    exfalso.
    subst T.
    generalize H.
    apply subst_destroys.
    apply lifting_destroys.
    apply le_0_n.
    constructor.
    right.
    rewrite Nat.add_1_r; apply le_n_S; apply le_0_n.
    destruct H.
    rewrite H.
    rewrite defer_lower.
    rewrite lift_lower_destruct.
    reflexivity.
    apply le_0_n.
    rewrite Nat.add_1_r; easy.
    apply lifting_destroys.
    apply le_0_n.
    constructor.
Qed.

(*
    A lemma about merging two lifts, but a more
    general one
*)
Lemma lift_merge_ex : forall (t : term) (c1 c2 : nat) (d1 d2 : nat),
    c1 <= c2 ->
    c2 <= c1 + d1 ->
    lift (lift t c1 d1) c2 d2 = lift t c1 (d1 + d2)
.
Proof.
    intro t.
    induction t; 
    try (
        easy ||
        (
            simpl;
            intros;
            assert (c1 + 1 <= c2 + 1) by (exact (Plus.plus_le_compat_r _ _ _ H));
            assert (c2 + 1 <= c1 + 1 + d1) by (rewrite <- PeanoNat.Nat.add_assoc; rewrite (PeanoNat.Nat.add_comm 1 d1); rewrite PeanoNat.Nat.add_assoc; exact (Plus.plus_le_compat_r _ _ _ H0));
            repeat (
                rewrite (IHt1 _ _ _ _ H H0) ||
                rewrite (IHt2 _ _ _ _ H H0) ||
                rewrite (IHt3 _ _ _ _ H H0) ||
                rewrite (IHt4 _ _ _ _ H H0) ||
                rewrite (IHt2 (c1 + 1) _ _ _ H1 H2)
            );
            reflexivity
        )
    ).

    intros.
    simpl.
    case_eq (n <? c1); intros.
    simpl.
    assert (n <? c2 = true).
    apply PeanoNat.Nat.ltb_lt.
    apply PeanoNat.Nat.ltb_lt in H1.
    exact (Nat.lt_le_trans _ _ _ H1 H).
    rewrite H2; reflexivity.
    simpl.
    assert (n + d1 <? c2 = false).
    apply PeanoNat.Nat.ltb_ge in H1; apply PeanoNat.Nat.ltb_ge.
    refine (Le.le_trans _ _ _ H0 (Plus.plus_le_compat_r _ _ _ H1)).
    rewrite H2.
    now rewrite PeanoNat.Nat.add_assoc.
Qed.

Lemma lift_swap_ex : forall N : term, forall c d p v : nat, 
    lift (lift N (d + c) p) c v = lift (lift N c v) (d + v + c) p
.
Proof.
    intro N; induction N; try easy.
    intros; simpl.
    rewrite IHN1; rewrite IHN2; rewrite IHN3; rewrite IHN4.
    reflexivity.
    intros; simpl.
    rewrite IHN1; rewrite IHN2.
    reflexivity.
    intros; simpl.
    rewrite IHN1.
    rewrite <- (PeanoNat.Nat.add_assoc d c 1).
    rewrite <- (PeanoNat.Nat.add_assoc (d + v) c 1).
    rewrite IHN2.
    reflexivity.
    intros; simpl.
    case_eq (n <? c); intros.
    assert (n <? d + c = true).
    apply PeanoNat.Nat.ltb_lt.
    apply PeanoNat.Nat.ltb_lt in H.
    refine (Nat.lt_le_trans _ _ _ H _).
    apply Plus.le_plus_r.
    rewrite H0.
    simpl.
    rewrite H.
    assert (n <? d + v + c = true).
    apply PeanoNat.Nat.ltb_lt.
    apply PeanoNat.Nat.ltb_lt in H0.
    rewrite (PeanoNat.Nat.add_comm d v).
    refine (Nat.lt_le_trans _ _ _ H0 _).
    rewrite (PeanoNat.Nat.add_comm v d).
    rewrite <- PeanoNat.Nat.add_assoc.
    apply Plus.plus_le_compat_l.
    apply (Plus.plus_le_compat_r 0).
    apply le_0_n.
    rewrite H1.
    reflexivity.
    case_eq (n <? d + c); intros.
    simpl.
    rewrite H.
    assert (n + v <? d + v + c = true).
    apply PeanoNat.Nat.ltb_lt.
    apply PeanoNat.Nat.ltb_lt in H0.
    rewrite (PeanoNat.Nat.add_comm n v); rewrite (PeanoNat.Nat.add_comm d v).
    rewrite <- PeanoNat.Nat.add_assoc.
    apply Plus.plus_lt_compat_l.
    exact H0.
    rewrite H1.
    reflexivity.
    simpl.
    assert (n + p <? c = false).
    apply PeanoNat.Nat.ltb_ge.
    apply PeanoNat.Nat.ltb_ge in H.
    rewrite PeanoNat.Nat.add_comm.
    refine (Le.le_trans _ _ _ H _).
    apply Plus.le_plus_r.
    rewrite H1.
    assert (n + v <? d + v + c = false).
    apply PeanoNat.Nat.ltb_ge.
    apply PeanoNat.Nat.ltb_ge in H0.
    rewrite (PeanoNat.Nat.add_comm d v); rewrite (PeanoNat.Nat.add_comm n v).
    rewrite <- PeanoNat.Nat.add_assoc.
    apply Plus.plus_le_compat_l.
    exact H0.
    rewrite H2.
    rewrite <- PeanoNat.Nat.add_assoc; rewrite (PeanoNat.Nat.add_comm p v); rewrite PeanoNat.Nat.add_assoc.
    reflexivity.
    intros.
    intros; simpl.
    rewrite IHN1.
    rewrite <- (PeanoNat.Nat.add_assoc d c 1).
    rewrite <- (PeanoNat.Nat.add_assoc (d + v) c 1).
    rewrite IHN2.
    reflexivity.
Qed.

Theorem lift_subst_unfold_alt : forall (t N : term) (c d v : nat),
    v < c ->
    subst (lift t c d) v (lift N c d) = lift (subst t v N) c d
.
Proof.
    intro t; induction t; 
    try (
        easy ||
        (
            intros; simpl;
            now repeat (rewrite (IHt1 _ _ _ _ H) || rewrite (IHt2 _ _ _ _ H) || rewrite (IHt3 _ _ _ _ H) || rewrite (IHt4 _ _ _ _ H))
        ) ||
        (
            intros; simpl;
            rewrite (IHt1 _ _ _ _ H); rewrite <- (IHt2 (lift1 N) _ _ _ (Plus.plus_lt_compat_r _ _ 1 H));
            unfold lift1;
            rewrite <- (PeanoNat.Nat.add_0_r c) at 3; rewrite lift_swap_ex; rewrite PeanoNat.Nat.add_0_r;
            reflexivity
        )
    ).

    intros; simpl.
    case_eq (v =? n); intros.
    assert (n <? c = true) by (apply PeanoNat.Nat.ltb_lt; apply PeanoNat.Nat.eqb_eq in H0; now subst v).
    rewrite H1.
    simpl; now rewrite H0.
    simpl.
    case_eq (n <? c); intros.
    simpl; now rewrite H0.
    simpl.
    assert (v =? n + d = false).
    apply PeanoNat.Nat.eqb_neq.
    intro F.
    assert (v < n).
    refine (Nat.lt_le_trans _ _ _ H _).
    now apply PeanoNat.Nat.ltb_ge in H1.
    assert (v < n + d).
    apply (Nat.lt_lt_add_r _ _ _ H2).
    exact (Nat.lt_neq _ _ H3 F).
    now rewrite H2.
Qed.

Theorem lift_injection : forall (t1 t2 : term) (c d : nat),
    lift t1 c d = lift t2 c d -> t1 = t2
.
Proof.
    intro t1; induction t1; intro t2; destruct t2; 
    try (
        easy ||
        (intros; exfalso; simpl in H; destruct (n <? c); easy)
    ).

    simpl; intros.
    injection H.
    intros.
    rewrite (IHt1_1 _ _ _ H3).
    rewrite (IHt1_2 _ _ _ H2).
    rewrite (IHt1_3 _ _ _ H1).
    rewrite (IHt1_4 _ _ _ H0).
    reflexivity.

    simpl; intros.
    injection H.
    intros.
    rewrite (IHt1_1 _ _ _ H1).
    rewrite (IHt1_2 _ _ _ H0).
    reflexivity.

    simpl; intros.
    injection H.
    intros.
    subst s0.
    rewrite (IHt1_1 _ _ _ H1).
    rewrite (IHt1_2 _ _ _ H0).
    reflexivity.

    simpl; intros.
    case_eq (n <? c); case_eq (n0 <? c); intros.
    rewrite H0 in H; rewrite H1 in H; easy.
    rewrite H0 in H; rewrite H1 in H.
    assert (n < n0).
    apply PeanoNat.Nat.ltb_lt in H1.
    apply PeanoNat.Nat.ltb_ge in H0.
    exact (Lt.lt_le_trans _ _ _ H1 H0).
    assert (n < n0 + d).
    now apply Nat.lt_lt_add_r.
    apply Nat.lt_neq in H3; exfalso; congruence.
    rewrite H0 in H; rewrite H1 in H.
    assert (n0 < n).
    apply PeanoNat.Nat.ltb_lt in H0.
    apply PeanoNat.Nat.ltb_ge in H1.
    exact (Lt.lt_le_trans _ _ _ H0 H1).
    assert (n0 < n + d).
    now apply Nat.lt_lt_add_r.
    apply Nat.lt_neq in H3; exfalso; congruence.
    rewrite H0 in H; rewrite H1 in H.
    injection H; intros.
    apply PeanoNat.Nat.add_cancel_r in H2.
    congruence.

    simpl.
    intros; destruct (n0 <? c); easy.

    simpl; intros.
    injection H.
    intros.
    subst s0.
    rewrite (IHt1_1 _ _ _ H1).
    rewrite (IHt1_2 _ _ _ H0).
    reflexivity.
Qed.

Theorem lift_move_away : forall (t : term) (Dc c d : nat),
    (forall v, var_occurs t v -> c + Dc <= v \/ v < c) ->
    lift t c d = lift t (c + Dc) d
.
Proof.
    intro t; induction t; 
    try (
        easy ||
        (
            simpl; intros;
            try repeat (
                (rewrite (IHt1 Dc c d); intuition) ||
                (rewrite (IHt2 Dc c d); intuition) ||
                (rewrite (IHt3 Dc c d); intuition) ||
                (rewrite (IHt4 Dc c d); intuition)
            );
            reflexivity
        )
    ).

    simpl; intros.
    rewrite (IHt1 Dc c d); intuition.
    rewrite <- PeanoNat.Nat.add_assoc; 
    rewrite (PeanoNat.Nat.add_comm Dc); 
    rewrite PeanoNat.Nat.add_assoc;
    rewrite (IHt2 Dc (c + 1) d).
    reflexivity.
    intros;
    destruct v;
    (right; rewrite PeanoNat.Nat.add_1_r; apply PeanoNat.Nat.lt_0_succ) ||
    (
        rewrite <- PeanoNat.Nat.add_assoc; 
        rewrite (PeanoNat.Nat.add_comm 1 Dc); 
        rewrite PeanoNat.Nat.add_assoc;
        repeat rewrite PeanoNat.Nat.add_1_r;
        destruct (H _ (or_intror H0));
        (left; exact (Le.le_n_S _ _ H1)) || (right; exact (Lt.lt_n_S _ _ H1))
    ).

    simpl; intros.
    destruct (H n (eq_refl _)).
    assert (n <? c + Dc = false) by (now apply PeanoNat.Nat.ltb_ge).
    assert (n <? c = false).
    apply PeanoNat.Nat.ltb_ge.
    exact (Le.le_trans _ _ _ (Plus.le_plus_l _ _) H0).
    now (rewrite H1; rewrite H2).
    assert (n <? c = true) by (now apply PeanoNat.Nat.ltb_lt).
    assert (n <? c + Dc = true).
    apply PeanoNat.Nat.ltb_lt.
    exact (Lt.lt_le_trans _ _ _ H0 (Plus.le_plus_l _ _)).
    now (rewrite H1; rewrite H2).

    simpl; intros.
    rewrite (IHt1 Dc c d); intuition.
    rewrite <- PeanoNat.Nat.add_assoc; 
    rewrite (PeanoNat.Nat.add_comm Dc); 
    rewrite PeanoNat.Nat.add_assoc;
    rewrite (IHt2 Dc (c + 1) d).
    reflexivity.
    intros;
    destruct v;
    (right; rewrite PeanoNat.Nat.add_1_r; apply PeanoNat.Nat.lt_0_succ) ||
    (
        rewrite <- PeanoNat.Nat.add_assoc; 
        rewrite (PeanoNat.Nat.add_comm 1 Dc); 
        rewrite PeanoNat.Nat.add_assoc;
        repeat rewrite PeanoNat.Nat.add_1_r;
        destruct (H _ (or_intror H0));
        (left; exact (Le.le_n_S _ _ H1)) || (right; exact (Lt.lt_n_S _ _ H1))
    ).
Qed.

Lemma lift_lower_swap_ex : forall N : term, forall c d p v : nat, 
    (forall v, var_occurs N v -> d + c <= v -> d + c + p <= v) ->
    lift (lower N (d + c) p) c v = lower (lift N c v) (d + v + c) p
.
Proof.
    intro N; induction N; 
    try (
        easy ||
        (
            simpl; intros;
            now repeat (
                try (rewrite (IHN1 _ _ _ _); intuition);
                try (rewrite (IHN2 _ _ _ _); intuition);
                try (rewrite (IHN3 _ _ _ _); intuition);
                try (rewrite (IHN4 _ _ _ _); intuition)
            )
        )
    ).

    simpl; intros.
    rewrite (IHN1 _ _ _ _); intuition.
    repeat rewrite <- PeanoNat.Nat.add_assoc.
    rewrite (IHN2 _ _ _ _).
    now repeat rewrite PeanoNat.Nat.add_assoc.
    intros; 
    simpl;
    rewrite PeanoNat.Nat.add_assoc in H1; rewrite PeanoNat.Nat.add_1_r in H1;
    destruct v0.
    exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H1).
    rewrite PeanoNat.Nat.add_assoc; rewrite PeanoNat.Nat.add_1_r.
    rewrite PeanoNat.Nat.add_succ_l.
    exact (Le.le_n_S _ _ (H _ (or_intror H0) (Le.le_S_n _ _ H1))).

    intros; simpl.
    case_eq (n <? c); intros.
    assert (n <? d + c = true).
    apply PeanoNat.Nat.ltb_lt; apply PeanoNat.Nat.ltb_lt in H0.
    now apply PeanoNat.Nat.lt_lt_add_l.
    rewrite H1.
    simpl.
    assert (n <? d + v + c = true).
    apply PeanoNat.Nat.ltb_lt; apply PeanoNat.Nat.ltb_lt in H1.
    rewrite (PeanoNat.Nat.add_comm d v); rewrite <- PeanoNat.Nat.add_assoc; now apply PeanoNat.Nat.lt_lt_add_l.
    now (rewrite H0; rewrite H2).
    simpl.
    case_eq (n <? d + c); intros.
    assert (n + v <? d + v + c = true).
    apply PeanoNat.Nat.ltb_lt; apply PeanoNat.Nat.ltb_lt in H1.
    rewrite <- PeanoNat.Nat.add_assoc; rewrite (PeanoNat.Nat.add_comm v c); rewrite PeanoNat.Nat.add_assoc.
    now apply PeanoNat.Nat.add_lt_mono_r.
    rewrite H2.
    simpl; now rewrite H0.
    assert (n + v <? d + v + c = false).
    apply PeanoNat.Nat.ltb_ge; apply PeanoNat.Nat.ltb_ge in H1.
    rewrite <- PeanoNat.Nat.add_assoc; rewrite (PeanoNat.Nat.add_comm v c); rewrite PeanoNat.Nat.add_assoc.
    now apply PeanoNat.Nat.add_le_mono_r.
    rewrite H2.
    simpl.
    assert (n - p <? c = false).
    apply PeanoNat.Nat.ltb_ge; apply PeanoNat.Nat.ltb_ge in H0.
    apply (PeanoNat.Nat.add_le_mono_r c (n - p) p).
    rewrite PeanoNat.Nat.sub_add.
    refine (Le.le_trans _ _ _ (PeanoNat.Nat.le_add_r _ d) _).
    rewrite PeanoNat.Nat.add_shuffle0.
    rewrite (PeanoNat.Nat.add_comm c d).
    exact (H _ (eq_refl _) (proj1 (PeanoNat.Nat.ltb_ge _ _) H1)).
    generalize (H n (eq_refl _) (proj1 (PeanoNat.Nat.ltb_ge _ _) H1)).
    intros.
    rewrite (PeanoNat.Nat.add_comm (d + c) p) in H3; refine (Le.le_trans _ _ _ (PeanoNat.Nat.le_add_r _ (d + c)) H3).
    rewrite H3.
    rewrite Nat.add_sub_swap.
    reflexivity.
    apply PeanoNat.Nat.ltb_ge in H1.
    set (H4 := H n (eq_refl _) H1).
    rewrite (PeanoNat.Nat.add_comm (d + c) p) in H4; refine (Le.le_trans _ _ _ (PeanoNat.Nat.le_add_r _ (d + c)) H4).

    simpl; intros.
    rewrite (IHN1 _ _ _ _); intuition.
    repeat rewrite <- PeanoNat.Nat.add_assoc.
    rewrite (IHN2 _ _ _ _).
    now repeat rewrite PeanoNat.Nat.add_assoc.
    intros; 
    simpl;
    rewrite PeanoNat.Nat.add_assoc in H1; rewrite PeanoNat.Nat.add_1_r in H1;
    destruct v0.
    exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H1).
    rewrite PeanoNat.Nat.add_assoc; rewrite PeanoNat.Nat.add_1_r.
    rewrite PeanoNat.Nat.add_succ_l.
    exact (Le.le_n_S _ _ (H _ (or_intror H0) (Le.le_S_n _ _ H1))).
Qed.

Theorem lower_subst_unfold_alt : forall (t N : term) (c d v : nat),
    (forall v, var_occurs N v -> c <= v -> c + d <= v) ->
    (forall v, var_occurs t v -> c <= v -> c + d <= v) ->
    v < c ->
    subst (lower t c d) v (lower N c d) = lower (subst t v N) c d
.
Proof.
    intro t; induction t; try easy.

    simpl.
    intros.
    rewrite (IHt1 _ _ _ _ H); intuition.
    rewrite (IHt2 _ _ _ _ H); intuition.
    rewrite (IHt3 _ _ _ _ H); intuition.
    rewrite (IHt4 _ _ _ _ H); intuition.

    simpl.
    intros.
    rewrite (IHt1 _ _ _ _ H); intuition.
    rewrite (IHt2 _ _ _ _ H); intuition.
    
    simpl.
    intros.
    rewrite (IHt1 _ _ _ _ H); intuition.
    rewrite <- (IHt2 _ _ _ (v + 1)); intuition.
    unfold lift1.
    rewrite <- (PeanoNat.Nat.add_0_r c) at 3.
    rewrite (lift_lower_swap_ex _ _ _ _ _).
    now rewrite PeanoNat.Nat.add_0_r.
    now repeat rewrite PeanoNat.Nat.add_0_r.
    destruct v0.
    rewrite PeanoNat.Nat.add_1_r in H3; exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H3).
    rewrite PeanoNat.Nat.add_1_r in H3.
    rewrite Nat.add_shuffle0; rewrite PeanoNat.Nat.add_1_r.
    rewrite <- PeanoNat.Nat.add_1_r in H2; unfold lift1 in H2.
    apply (lifting_respects_occurance_r _ _ _ _ (le_0_n _)) in H2.
    apply Le.le_n_S; exact (H _ H2 (Le.le_S_n _ _ H3)).
    rewrite PeanoNat.Nat.add_1_r in H3.
    destruct v0.
    exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H3).
    rewrite Nat.add_shuffle0; rewrite PeanoNat.Nat.add_1_r.
    apply Le.le_n_S; exact (H0 _ (or_intror H2) (Le.le_S_n _ _ H3)).

    simpl; intros.
    generalize (H0 _ (eq_refl _)); clear H0; intros.
    case_eq (v =? n); intros.
    assert (n <? c = true).
    apply PeanoNat.Nat.ltb_lt; apply PeanoNat.Nat.eqb_eq in H2; now subst n.
    rewrite H3.
    simpl.
    now rewrite H2.
    case_eq (n <? c); intros.
    simpl.
    now (rewrite H2; rewrite H3).
    simpl.
    rewrite H3.
    assert (v =? n - d = false).
    apply PeanoNat.Nat.ltb_ge in H3.
    generalize (H0 H3); intros.
    apply (PeanoNat.Nat.sub_le_mono_r _ _ d) in H4.
    rewrite PeanoNat.Nat.add_sub in H4.
    generalize (Lt.lt_le_trans _ _ _ H1 H4); intros.
    apply PeanoNat.Nat.eqb_neq; exact (PeanoNat.Nat.lt_neq _ _ H5).
    now rewrite H4.

    simpl.
    intros.
    rewrite (IHt1 _ _ _ _ H); intuition.
    rewrite <- (IHt2 _ _ _ (v + 1)); intuition.
    unfold lift1.
    rewrite <- (PeanoNat.Nat.add_0_r c) at 3.
    rewrite (lift_lower_swap_ex _ _ _ _ _).
    now rewrite PeanoNat.Nat.add_0_r.
    now repeat rewrite PeanoNat.Nat.add_0_r.
    destruct v0.
    rewrite PeanoNat.Nat.add_1_r in H3; exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H3).
    rewrite PeanoNat.Nat.add_1_r in H3.
    rewrite Nat.add_shuffle0; rewrite PeanoNat.Nat.add_1_r.
    rewrite <- PeanoNat.Nat.add_1_r in H2; unfold lift1 in H2.
    apply (lifting_respects_occurance_r _ _ _ _ (le_0_n _)) in H2.
    apply Le.le_n_S; exact (H _ H2 (Le.le_S_n _ _ H3)).
    rewrite PeanoNat.Nat.add_1_r in H3.
    destruct v0.
    exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H3).
    rewrite Nat.add_shuffle0; rewrite PeanoNat.Nat.add_1_r.
    apply Le.le_n_S; exact (H0 _ (or_intror H2) (Le.le_S_n _ _ H3)).
Qed.

Theorem lower_swap_ex : forall N : term, forall c d p v : nat, 
    (forall V, var_occurs N V -> d + v + c <= V -> d + v + c + p <= V) ->
    lower (lower N (d + v + c) p) c v = lower (lower N c v) (d + c) p
.
Proof.
    intro N; induction N; try easy.

    simpl; intros.
    rewrite IHN1; intuition.
    rewrite IHN2; intuition.
    rewrite IHN3; intuition.
    rewrite IHN4; intuition.

    simpl; intros.
    rewrite IHN1; intuition.
    rewrite IHN2; intuition.

    simpl; intros.
    rewrite IHN1; intuition.
    repeat rewrite <- PeanoNat.Nat.add_assoc.
    rewrite (PeanoNat.Nat.add_assoc d).
    rewrite IHN2.
    reflexivity.
    intros.
    repeat rewrite PeanoNat.Nat.add_assoc in H1.
    rewrite PeanoNat.Nat.add_1_r in H1.
    destruct V.
    exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H1).
    rewrite <- PeanoNat.Nat.add_assoc.
    rewrite <- (PeanoNat.Nat.add_assoc c 1 p).
    rewrite (PeanoNat.Nat.add_comm 1).
    repeat rewrite PeanoNat.Nat.add_assoc.
    rewrite PeanoNat.Nat.add_1_r.
    apply le_n_S.
    exact (H _ (or_intror H0) (le_S_n _ _ H1)).

    simpl; intros.
    case_eq (n <? c); intros.
    assert (n <? d + v + c = true).
    apply PeanoNat.Nat.ltb_lt; apply PeanoNat.Nat.ltb_lt in H0.
    now apply (PeanoNat.Nat.lt_lt_add_l _ _ (d + v)).
    rewrite H1.
    simpl.
    assert (n <? d + c = true).
    apply PeanoNat.Nat.ltb_lt; apply PeanoNat.Nat.ltb_lt in H0.
    now apply (PeanoNat.Nat.lt_lt_add_l _ _ d).
    now (rewrite H0; rewrite H2).
    simpl.
    destruct (PeanoNat.Nat.lt_ge_cases n v).
    case_eq (n <? d + v + c); case_eq (n - v <? d + c); intros.
    simpl.
    now rewrite H0.
    simpl; rewrite H0.
    rewrite Minus.not_le_minus_0.
    rewrite PeanoNat.Nat.sub_0_l.
    reflexivity.
    now apply Lt.lt_not_le.
    simpl.
    assert (n - p <? c = false).
    apply PeanoNat.Nat.ltb_ge; apply PeanoNat.Nat.ltb_ge in H3.
    generalize (H _ (eq_refl _) H3); intros.
    apply (PeanoNat.Nat.sub_le_mono_r _ _ p) in H4.
    rewrite PeanoNat.Nat.add_sub in H4.
    refine (Le.le_trans _ _ _ _ H4).
    apply Plus.le_plus_r.
    rewrite H4.
    rewrite <- PeanoNat.Nat.sub_add_distr; rewrite PeanoNat.Nat.add_comm; rewrite PeanoNat.Nat.sub_add_distr.
    rewrite (Minus.not_le_minus_0 n v).
    rewrite PeanoNat.Nat.sub_0_l.
    reflexivity.
    now apply Lt.lt_not_le.
    simpl.
    assert (n - p <? c = false).
    apply PeanoNat.Nat.ltb_ge; apply PeanoNat.Nat.ltb_ge in H3.
    generalize (H _ (eq_refl _) H3); intros.
    apply (PeanoNat.Nat.sub_le_mono_r _ _ p) in H4.
    rewrite PeanoNat.Nat.add_sub in H4.
    refine (Le.le_trans _ _ _ _ H4).
    apply Plus.le_plus_r.
    rewrite H4.
    repeat rewrite <- PeanoNat.Nat.sub_add_distr; now rewrite PeanoNat.Nat.add_comm.
    case_eq (n <? d + v + c); intros.
    assert (n - v <? d + c = true).
    apply PeanoNat.Nat.ltb_lt; apply PeanoNat.Nat.ltb_lt in H2.
    apply (PeanoNat.Nat.add_lt_mono_r _ _ v).
    rewrite (PeanoNat.Nat.sub_add _ _ H1).
    now rewrite PeanoNat.Nat.add_shuffle0.
    rewrite H3.
    simpl.
    now rewrite H0.
    assert (n - v <? d + c = false).
    apply PeanoNat.Nat.ltb_ge; apply PeanoNat.Nat.ltb_ge in H2.
    rewrite PeanoNat.Nat.add_shuffle0 in H2.
    apply (PeanoNat.Nat.sub_le_mono_r _ _ v) in H2.
    now rewrite PeanoNat.Nat.add_sub in H2.
    rewrite H3.
    simpl.
    assert (n - p <? c = false).
    apply PeanoNat.Nat.ltb_ge; apply PeanoNat.Nat.ltb_ge in H2.
    generalize (H _ (eq_refl _) H2); intros.
    apply (PeanoNat.Nat.sub_le_mono_r _ _ p) in H4.
    rewrite PeanoNat.Nat.add_sub in H4.
    refine (Le.le_trans _ _ _ _ H4).
    apply Plus.le_plus_r.
    rewrite H4.
    repeat rewrite <- PeanoNat.Nat.sub_add_distr; now rewrite PeanoNat.Nat.add_comm.

    simpl; intros.
    rewrite IHN1; intuition.
    repeat rewrite <- PeanoNat.Nat.add_assoc.
    rewrite (PeanoNat.Nat.add_assoc d).
    rewrite IHN2.
    reflexivity.
    intros.
    repeat rewrite PeanoNat.Nat.add_assoc in H1.
    rewrite PeanoNat.Nat.add_1_r in H1.
    destruct V.
    exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H1).
    rewrite <- PeanoNat.Nat.add_assoc.
    rewrite <- (PeanoNat.Nat.add_assoc c 1 p).
    rewrite (PeanoNat.Nat.add_comm 1).
    repeat rewrite PeanoNat.Nat.add_assoc.
    rewrite PeanoNat.Nat.add_1_r.
    apply le_n_S.
    exact (H _ (or_intror H0) (le_S_n _ _ H1)).
Qed.

Theorem lowering_and_occurance : forall (t : term) (c d v : nat),
    c <= v ->
    d <= v ->
    var_occurs t (v + d) <-> var_occurs (lower t c d) v
.
Proof.
    intro t; induction t;
    intros c d v H0 H1;
    try easy.
    simpl.
    apply or_iff.
    now apply IHt1.
    apply or_iff.
    now apply IHt2.
    apply or_iff.
    now apply IHt3.
    now apply IHt4.

    simpl.
    apply or_iff.
    now apply IHt1.
    now apply IHt2.

    simpl.
    apply or_iff.
    now apply IHt1.
    assert (S (v + d) = S v + d) by easy.
    rewrite H.
    apply IHt2.
    rewrite Nat.add_1_r.
    now apply le_n_S.
    now apply le_S.
    
    simpl.
    split; intros.
    subst n; assert (v + d <? c = false).
    apply Nat.ltb_ge.
    apply (Le.le_trans _ v _); try easy.
    apply Nat.le_add_r.
    rewrite H.
    now rewrite Nat.add_sub.
    case_eq (n <? c); intro.
    rewrite H2 in H.
    simpl in H.
    subst n; exfalso.
    apply Nat.ltb_lt in H2.
    exact (Lt.lt_not_le _ _ H2 H0).
    rewrite H2 in H.
    simpl in H.
    subst v.
    symmetry.
    apply Nat.sub_add.
    apply (Le.le_trans _ (n - d) _).
    assumption.
    apply Nat.le_sub_l.

    simpl.
    apply or_iff.
    now apply IHt1.
    assert (S (v + d) = S v + d) by easy.
    rewrite H.
    apply IHt2.
    rewrite Nat.add_1_r.
    now apply le_n_S.
    now apply le_S.
Qed.

Theorem lowering_and_occurance_alt : forall (t : term) (c d v : nat),
    (forall v', var_occurs t v' -> c <= v' -> c + d <= v') ->
    var_occurs (lower t c d) v -> 
    var_occurs t (v + d) \/ v < c
.
Proof.
    intro t; induction t; try easy.
    simpl; intros.
    intuition.
    generalize (IHt1 c _ _ (fun v H' => H v (or_introl H')) H1).
    tauto.
    generalize (IHt2 c _ _ (fun v H' => H v (or_intror (or_introl H'))) H0).
    tauto.
    generalize (IHt3 c _ _ (fun v H' => H v (or_intror (or_intror (or_introl H')))) H1).
    tauto.
    generalize (IHt4 c _ _ (fun v H' => H v (or_intror (or_intror (or_intror H')))) H1).
    tauto.
    simpl; intros.
    destruct H0.
    generalize (IHt1 c _ _ (fun v H' => H v (or_introl H')) H0).
    tauto.
    generalize (IHt2 c _ _ (fun v H' => H v (or_intror H')) H0).
    tauto.

    simpl; intros.
    destruct H0.
    generalize (IHt1 c _ _ (fun v H' => H v (or_introl H')) H0).
    tauto.
    rewrite <- plus_Sn_m.
    rewrite PeanoNat.Nat.add_1_r in H0.
    assert (forall v', var_occurs t2 v' -> S c <= v' -> S c + d <= v').
    intros.
    destruct v'.
    exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H2).
    apply Le.le_S_n in H2.
    rewrite plus_Sn_m.
    apply Le.le_n_S.
    exact (H _ (or_intror H1) H2).
    generalize (IHt2 _ _ _ H1 H0).
    rewrite <- PeanoNat.Nat.succ_lt_mono.
    tauto.

    simpl; intros.
    generalize (H _ (eq_refl _)); intros.
    case_eq (n <? c); intros.
    rewrite H2 in H0.
    simpl in H0; subst n.
    right; now apply PeanoNat.Nat.ltb_lt in H2.
    rewrite H2 in H0.
    simpl in H0; subst v.
    apply PeanoNat.Nat.ltb_ge in H2.
    generalize (H1 H2); intros; left.
    rewrite PeanoNat.Nat.sub_add.
    reflexivity.
    refine (Le.le_trans _ _ _ _ H0).
    apply Plus.le_plus_r.

    simpl; intros.
    destruct H0.
    generalize (IHt1 c _ _ (fun v H' => H v (or_introl H')) H0).
    tauto.
    rewrite <- plus_Sn_m.
    rewrite PeanoNat.Nat.add_1_r in H0.
    assert (forall v', var_occurs t2 v' -> S c <= v' -> S c + d <= v').
    intros.
    destruct v'.
    exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H2).
    apply Le.le_S_n in H2.
    rewrite plus_Sn_m.
    apply Le.le_n_S.
    exact (H _ (or_intror H1) H2).
    generalize (IHt2 _ _ _ H1 H0).
    rewrite <- PeanoNat.Nat.succ_lt_mono.
    tauto.
Qed.

Lemma lift_swap_same_c : forall (t : term) (c d1 d2 : nat),
    lift (lift t c d1) c d2 = lift (lift t c d2) c d1
.
Proof.
    intros.
    repeat rewrite lift_merge.
    rewrite PeanoNat.Nat.add_comm.
    repeat rewrite <- lift_merge.
    reflexivity.
Qed.

Lemma lower_merge : forall (t : term) (c d1 d2 : nat),
    (forall v, var_occurs t v -> c <= v -> c + d1 <= v) ->
    lower (lower t c d1) c d2 = lower t c (d1 + d2)
.
Proof.
    intro t; induction t; try easy.

    simpl; intros.
    rewrite IHt1 by intuition.
    rewrite IHt2 by intuition.
    rewrite IHt3 by intuition.
    rewrite IHt4 by intuition.
    reflexivity.

    simpl; intros.
    rewrite IHt1 by intuition.
    rewrite IHt2 by intuition.
    reflexivity.

    simpl; intros.
    rewrite IHt1 by intuition.
    rewrite IHt2.
    reflexivity.
    intro v; destruct v.
    rewrite PeanoNat.Nat.add_1_r; intros H0 H1; exfalso; generalize H1.
    apply PeanoNat.Nat.nle_succ_0.
    intro H0.
    rewrite PeanoNat.Nat.add_shuffle0.
    repeat rewrite PeanoNat.Nat.add_1_r.
    intro H1; apply Le.le_S_n in H1; apply Le.le_n_S.
    intuition.

    intros; simpl.
    assert (H1 := H _ (eq_refl _)).
    clear H.
    case_eq (n <? c); intros.
    simpl.
    now rewrite H.
    simpl.
    assert (n - d1 <? c = false).
    apply PeanoNat.Nat.ltb_ge.
    apply PeanoNat.Nat.ltb_ge in H.
    assert (H2 := H1 H).
    apply (PeanoNat.Nat.sub_le_mono_r _ _ d1) in H2.
    now rewrite PeanoNat.Nat.add_sub in H2.
    rewrite H0.
    now rewrite Nat.sub_add_distr.

    simpl; intros.
    rewrite IHt1 by intuition.
    rewrite IHt2.
    reflexivity.
    intro v; destruct v.
    rewrite PeanoNat.Nat.add_1_r; intros H0 H1; exfalso; generalize H1.
    apply PeanoNat.Nat.nle_succ_0.
    intro H0.
    rewrite PeanoNat.Nat.add_shuffle0.
    repeat rewrite PeanoNat.Nat.add_1_r.
    intro H1; apply Le.le_S_n in H1; apply Le.le_n_S.
    intuition.
Qed.

Lemma lower_lift_destruct : forall (t : term) (c d : nat),
    (forall v, var_occurs t v -> c <= v -> c + d <= v) ->
    lift (lower t c d) c d = t
.
Proof.
    intro t; induction t; try easy.

    simpl; intros.
    rewrite IHt1 by intuition.
    rewrite IHt2 by intuition.
    rewrite IHt3 by intuition.
    rewrite IHt4 by intuition.
    reflexivity.

    simpl; intros.
    rewrite IHt1 by intuition.
    rewrite IHt2 by intuition.
    reflexivity.

    simpl; intros.
    rewrite IHt1 by intuition.
    rewrite IHt2.
    reflexivity.
    intro v; destruct v.
    intros.
    exfalso; rewrite PeanoNat.Nat.add_1_r in H1; generalize H1; apply PeanoNat.Nat.nle_succ_0.
    rewrite PeanoNat.Nat.add_shuffle0.
    repeat rewrite PeanoNat.Nat.add_1_r.
    intros.
    apply Le.le_n_S; apply Le.le_S_n in H1.
    intuition.

    simpl; intros.
    assert (H0 := H _ (eq_refl _)).
    case_eq (n <? c); intros.
    simpl.
    now rewrite H1.
    simpl.
    assert (n - d <? c = false).
    apply PeanoNat.Nat.ltb_ge; apply PeanoNat.Nat.ltb_ge in H1.
    assert (H2 := H0 H1).
    apply (PeanoNat.Nat.sub_le_mono_r _ _ d) in H2.
    now rewrite PeanoNat.Nat.add_sub in H2.
    rewrite H2.
    rewrite PeanoNat.Nat.sub_add.
    reflexivity.
    apply PeanoNat.Nat.ltb_ge in H1.
    exact (Le.le_trans _ _ _ (Plus.le_plus_r _ _) (H0 H1)).

    simpl; intros.
    rewrite IHt1 by intuition.
    rewrite IHt2.
    reflexivity.
    intro v; destruct v.
    intros.
    exfalso; rewrite PeanoNat.Nat.add_1_r in H1; generalize H1; apply PeanoNat.Nat.nle_succ_0.
    rewrite PeanoNat.Nat.add_shuffle0.
    repeat rewrite PeanoNat.Nat.add_1_r.
    intros.
    apply Le.le_n_S; apply Le.le_S_n in H1.
    intuition.
Qed.

Lemma lower_c_0 : forall (t : term) (c : nat),
    lower t c 0 = t
.
Proof.
    intro t; induction t; try easy.
    intros; simpl.
    now (rewrite IHt1; rewrite IHt2; rewrite IHt3; rewrite IHt4).
    intros; simpl.
    now (rewrite IHt1; rewrite IHt2).
    intros; simpl.
    now (rewrite IHt1; rewrite IHt2).
    intros; simpl.
    now (destruct (n <? c); try rewrite Nat.sub_0_r).
    intros; simpl.
    now (rewrite IHt1; rewrite IHt2).
Qed.

Lemma alpha_eq_respects_occurance : forall (l r : term) (v : nat),
    var_occurs l v ->
    l =a r ->
    var_occurs r v
.
Proof.
    intro l; induction l; try easy.

    intro r; destruct r; try easy.
    simpl; intros.
    intuition.

    intro r; destruct r; try easy.
    simpl; intros.
    intuition.

    intro r; destruct r; try easy.
    simpl; intros.
    intuition.

    intro r; destruct r; try easy.
    simpl.
    intros; congruence.

    intro r; destruct r; try easy.
    simpl; intros.
    intuition.
Qed.