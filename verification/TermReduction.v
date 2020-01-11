(*
    Here we define the reduction of terms. We do not prove any properties
    about the reduction, because anything like strong weak or strong
    normalization and decidability of beta equality are true for
    *typable* terms.
*)

Require Import Term.
Require Import String.
Require Import Setoid.
Require Import Relations.
Require Import Relation_Operators.

(*
    Here we define the one-step reduction of the terms. Later we'll extend
    it into multistep reduction and beta equality.

    This is a binary relation which is read as "x can be reduced to y by applying one reduction rule".
    The reduction rules are a bit complex, because we are not using using De Brujin indices purely we
    are, as we said in Term.v, using strings on binders and foralls and to work with these terms we
    introduce alpha equality which we must take into account.

    Simply making a separate constructor like
        AlphaEqLaw : forall x x' y y' : term, (x ->b y) -> x =a x' -> y =a y' -> (x' ->b y')
    Makes it hard to prove simple things like:
        forall t : term, (NatO ->b t) -> False
    So we make all the rules like. "x reduces to whatever that is alpha-equal to expected redex".
*)
Reserved Notation "x ->b y" (at level 80, no associativity).
Inductive small_red : relation term :=
| RedAppL : 
    forall l l' r : term, 
    forall res : term,
    (l ->b l') -> 
    (App l' r =a res) -> 
    (App l r ->b res)
| RedAppR :
    forall l r r' : term, 
    forall res : term,
    (r ->b r') -> 
    (App l r' =a res) ->
    (App l r ->b res)

| RedAbsTyp : 
    forall str : string, 
    forall typ typ' body : term, 
    forall res : term,
    (typ ->b typ') -> 
    (Abs str typ' body =a res) -> 
    (Abs str typ body ->b res)
| RedAbsBody : 
    forall str : string, 
    forall typ body body' : term, 
    forall res : term,
    (body ->b body') -> 
    (Abs str typ body' =a res) ->
    (Abs str typ body ->b res)

| RedForallTyp : 
    forall str : string, 
    forall typ typ' body : term, 
    forall res : term,
    (typ ->b typ') -> 
    (Forall str typ' body =a res) -> 
    (Forall str typ body ->b res)
| RedForallBody : 
    forall str : string, 
    forall typ body body' : term, 
    forall res : term,
    (body ->b body') -> 
    (Forall str typ body' =a res) ->
    (Forall str typ body ->b res)

| RedAppAbs : 
    forall str : string, 
    forall typ body val res : term, 
    (top_subst body val =a res) -> 
    (App (Abs str typ body) val ->b res)

| NatRecRed : 
    forall type_choice step terminate num num' : term,
    forall res : term, 
    (num ->b num') -> 
    (NatRec type_choice step terminate num' =a res) ->
    (NatRec type_choice step terminate num ->b res)
| NatRecTerminate : 
    forall type_choice step terminate : term, 
    forall res : term,
    (terminate =a res) -> 
    (NatRec type_choice terminate step NatO ->b res)
| NatRecStep : 
    forall type_choice step terminate num : term,
    forall res : term,
    (App (App step num) (NatRec type_choice terminate step num) =a res) ->
    (NatRec type_choice terminate step (App NatSucc num) ->b res)
where "x ->b y" := (small_red x y).

(*
    A large proof about reduciton respecting alpha equality on
    the left
*)
Lemma small_red_respects_alpha_eq_l : forall l l' r : term, (l ->b r) -> l =a l' -> (l' ->b r).
Proof.
    intros.
    generalize H0; generalize l'; clear H0; clear l'.
    induction H.

    intros.
    destruct l'0; try easy.
    set (H2 := IHsmall_red l'0_1 (proj1 H1)).
    apply (RedAppL l'0_1 l' l'0_2); try easy.
    transitivity (App l' r).
    simpl; split; reflexivity || (symmetry; apply H1).
    assumption.

    intros.
    destruct l'; try easy.
    set (H2 := IHsmall_red l'2 (proj2 H1)).
    apply (RedAppR l'1 l'2 r'); try easy.
    transitivity (App l r').
    simpl; split; (symmetry; apply H1) || reflexivity.
    assumption.

    intros.
    destruct l'; try easy.
    set (H2 := IHsmall_red l'1 (proj1 H1)).
    apply (RedAbsTyp s l'1 typ'); try assumption.
    transitivity (Abs str typ' body); (split; reflexivity || (symmetry; apply H1)) || assumption.

    intros.
    destruct l'; try easy.
    set (H2 := IHsmall_red l'2 (proj2 H1)).
    apply (RedAbsBody _ _ _ body'); try assumption.
    transitivity (Abs str typ body'); (split; reflexivity || (symmetry; apply H1)) || assumption.

    intros.
    destruct l'; try easy.
    set (H2 := IHsmall_red l'1 (proj1 H1)).
    apply (RedForallTyp s l'1 typ'); try assumption.
    transitivity (Forall str typ' body); (split; reflexivity || (symmetry; apply H1)) || assumption.

    intros.
    destruct l'; try easy.
    set (H2 := IHsmall_red l'2 (proj2 H1)).
    apply (RedForallBody _ _ _ body'); try assumption.
    transitivity (Forall str typ body'); (split; reflexivity || (symmetry; apply H1)) || assumption.

    intros.
    destruct l'; try easy.
    simpl in H0; inversion_clear H0.
    destruct l'1; try easy.
    apply RedAppAbs.
    transitivity (top_subst body val); (apply lowering_respects_alpha_eq; apply subst_respects_alpha_eq; (symmetry; apply H1) || (apply lifting_respects_alpha_eq; symmetry; apply H2)) || assumption.

    intros.
    destruct l'; try easy.
    set (H2 := IHsmall_red l'4 (proj2 (proj2 (proj2 H1)))).
    apply (NatRecRed _ _ _ _ num'); try easy.
    transitivity (NatRec type_choice step terminate num'); (repeat split; symmetry; apply H1 || reflexivity) || assumption.

    intros.
    destruct l'; try easy.
    simpl in H0; inversion_clear H0.
    inversion_clear H2.
    inversion_clear H3.
    destruct l'4; try easy.
    apply NatRecTerminate; transitivity terminate; assumption || (symmetry; assumption).

    intros.
    destruct l'; try easy.
    simpl in H0; inversion_clear H0.
    inversion_clear H2.
    inversion_clear H3.
    destruct l'4; try easy.
    destruct l'4_1; try easy.
    apply NatRecStep; transitivity (App (App step num) (NatRec type_choice terminate step num)).
    inversion_clear H4; repeat split; symmetry; assumption.
    assumption.
Qed.

(*
    ...And on the right.
*)
Lemma small_red_respects_alpha_eq_r : forall l r r' : term, (l ->b r) -> r =a r' -> (l ->b r').
Proof.
    intros.
    destruct H.

    apply (RedAppL _ l').
    assumption.
    transitivity res; assumption.

    apply (RedAppR _ _ r'0).    
    assumption.
    transitivity res; assumption.

    apply (RedAbsTyp _ _ typ').
    assumption.
    transitivity res; assumption.

    apply (RedAbsBody _ _ _ body').
    assumption.
    transitivity res; assumption.

    apply (RedForallTyp _ _ typ').
    assumption.
    transitivity res; assumption.

    apply (RedForallBody _ _ _ body').
    assumption.
    transitivity res; assumption.

    apply RedAppAbs.
    transitivity res; assumption.

    apply (NatRecRed _ _ _ _ num').
    assumption.
    transitivity res; assumption.

    apply NatRecTerminate.
    transitivity res; assumption.

    apply NatRecStep.
    transitivity res; assumption.
Qed.

(*
    And then we glue them into respecting alpha equality
    on both sides.
*)
Theorem small_red_respects_alpha_eq : forall l l' r r' : term, (l ->b r) -> (l =a l') -> (r =a r') -> (l' ->b r').
Proof.
    intros.
    apply (small_red_respects_alpha_eq_l l).
    apply (small_red_respects_alpha_eq_r _ r).
    assumption.
    assumption.
    assumption.
Qed.

(* We define multistep reduction as transitive closure of one step reduction *)
Definition multistep_red (l r : term) : Prop := clos_trans term small_red l r.
Notation "x ->>b y" := (multistep_red x y) (at level 80, no associativity).
Add Relation term multistep_red
    transitivity proved by (fun x y z H1 H2 => t_trans term small_red x y z H1 H2)
as nbu_relation_2.

Theorem multistep_red_respects_alpha_eq : forall l l' r r' : term, (l ->>b r) -> (l =a l') -> (r =a r') -> (l' ->>b r').
Proof.
    intros.
    generalize H0; generalize H1; generalize l'; generalize r'; clear H0; clear H1; clear l'; clear r'.
    induction H.

    intros.
    apply t_step.
    now apply (small_red_respects_alpha_eq x _ y _).

    intros.
    assert (l' ->>b y) by (apply IHclos_trans1; reflexivity || assumption).
    assert (y ->>b r') by (apply IHclos_trans2; reflexivity || assumption).
    now apply (t_trans _ _ _ y).
Qed.

(* Beta equality is the transitive-simmetrycal-(alpha-reflexive) closure of one step reduction *)
Reserved Notation "x =b y" (at level 80, no associativity).
Inductive beta_eq : term -> term -> Prop :=
| beta_refl : forall x y : term, (x =a y) -> (x =b y)
| beta_symm : forall x y : term, (x =b y) -> (y =b x)
| beta_trans : forall x y z : term, (x =b y) -> (y =b z) -> (x =b z)
| bet_one_step : forall x y, (x ->b y) -> (x =b y)
where "x =b y" := (beta_eq x y).

Add Relation term beta_eq
    reflexivity proved by (fun x => beta_refl x x (proj1 alpha_eq_equiv x))
    symmetry proved by (fun l r H => beta_symm l r H)
    transitivity proved by (fun x y z H1 H2 => beta_trans x y z H1 H2)
as nbu_relation_3.

Theorem multistep_implies_beta_eq : forall (l r : term), (l ->>b r) -> (l =b r).
Proof.
    intros.
    induction H.
    now apply bet_one_step.
    now apply (beta_trans x y z).
Qed.

Theorem beta_eq_respects_alpha_eq : forall l l' r r' : term, (l =b r) -> (l =a l') -> (r =a r') -> (l' =b r').
Proof.
    intros.
    transitivity l.
    apply beta_refl; symmetry; assumption.
    transitivity r.
    assumption.
    apply beta_refl; assumption.
Qed.

(* Two basic properties *)
Definition reducable (t : term) : Prop := exists t' : term, t ->b t'.
Definition irreducable (t : term) : Prop := forall t' : term, t ->b t' -> False.

(* A small lemma about the reducability *)
Lemma not_both_red_and_irred : forall t : term, (reducable t /\ irreducable t) -> False.
Proof. 
    intros.
    inversion_clear H.
    unfold reducable in H0; elim H0; clear H0; intros.
    exact (H1 x H).
Qed.

(* We define the specification of the reduction strategy *)
Definition reduction_strategy (f : term -> term) : Prop := forall t : term, t ->b f t \/ t =a f t.

(* One lifting respects step reduction *)
Theorem lifting_respects_one_step : forall (l r : term) (c d : nat), (l ->b r) -> (lift l c d ->b lift r c d).
Proof.
    intros.
    generalize c d.
    clear c d.
    induction H.

    intros; simpl.
    apply (RedAppL (lift l c d) (lift l' c d) (lift r c d)).
    apply IHsmall_red.
    apply (lifting_respects_alpha_eq _ _ _ _ H0).

    intros; simpl.
    apply (RedAppR (lift l c d) (lift r c d) (lift r' c d)).
    apply IHsmall_red.
    apply (lifting_respects_alpha_eq _ _ _ _ H0).

    intros; simpl.
    apply (RedAbsTyp str (lift typ c d) (lift typ' c d) (lift body (c + 1) d)).
    apply IHsmall_red.
    apply (lifting_respects_alpha_eq _ _ _ _ H0).

    intros; simpl.
    apply (RedAbsBody str (lift typ c d) (lift body (c + 1) d) (lift body' (c + 1) d)).
    apply IHsmall_red.
    apply (lifting_respects_alpha_eq _ _ _ _ H0).

    intros; simpl.
    apply (RedForallTyp str (lift typ c d) (lift typ' c d) (lift body (c + 1) d)).
    apply IHsmall_red.
    apply (lifting_respects_alpha_eq _ _ _ _ H0).

    intros; simpl.
    apply (RedForallBody str (lift typ c d) (lift body (c + 1) d) (lift body' (c + 1) d)).
    apply IHsmall_red.
    apply (lifting_respects_alpha_eq _ _ _ _ H0).

    intros; simpl.
    apply (RedAppAbs str (lift typ c d) (lift body (c + 1) d) (lift val c d)).
    unfold top_subst.
    unfold lift1.
    rewrite <- (PeanoNat.Nat.add_0_r c) at 2.
    rewrite lift_swap_ex.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite lift_subst_unfold_alt.
    elim (lifted_repr (subst body 0 (lift val 0 1)) 0 1).
    intros.
    rewrite H0.
    rewrite <- (PeanoNat.Nat.add_0_r (c + 1)).
    rewrite <- lift_swap_ex.
    unfold clean_after_subst.
    rewrite lift_lower_destruct; rewrite PeanoNat.Nat.add_0_r.
    assert (lower (subst body 0 (lift val 0 1)) 0 1 = x).
    rewrite H0; now rewrite lift_lower_destruct.
    subst x.
    apply (lifting_respects_alpha_eq _ _ _ _ H).
    intros.
    destruct v.
    exfalso; generalize H0; apply subst_destroys; apply lifting_destroys.
    constructor.
    constructor.
    right; apply le_n_S; apply le_0_n.
    rewrite PeanoNat.Nat.add_1_r; apply PeanoNat.Nat.lt_0_succ.

    intros; simpl.
    apply (NatRecRed (lift type_choice c d) (lift step c d) (lift terminate c d) (lift num c d) (lift num' c d)).
    apply IHsmall_red.
    apply (lifting_respects_alpha_eq _ _ _ _ H0).

    intros; simpl.
    apply (NatRecTerminate (lift type_choice c d) (lift step c d) (lift terminate c d)).
    apply (lifting_respects_alpha_eq _ _ _ _ H).

    intros; simpl.
    apply (NatRecStep (lift type_choice c d) (lift step c d) (lift terminate c d) (lift num c d)).
    apply (lifting_respects_alpha_eq _ _ _ _ H).
Qed.

(* Lifting respects beta eq *)
Theorem lifting_respects_beta_eq : forall (l r : term) (c d : nat), (l =b r) -> (lift l c d =b lift r c d).
Proof.
    intros.
    induction H.
    apply beta_refl.
    now apply lifting_respects_alpha_eq.
    now symmetry.
    now transitivity (lift y c d).
    apply bet_one_step.
    now apply lifting_respects_one_step.
Qed.

(* Lowering respects one step *)
Theorem lowering_respects_one_step : forall (l r : term),
    (l ->b r) ->
    forall (c d : nat),
    (forall v, var_occurs l v -> c <= v -> c + d <= v) ->
    (lower l c d ->b lower r c d)
.
Proof.
    intros l r H.
    induction H; simpl; intros.

    apply (RedAppL _ (lower l' c d)).
    apply IHsmall_red.
    intuition.
    apply (lowering_respects_alpha_eq _ _ _ _ H0).

    apply (RedAppR _ _ (lower r' c d)).
    apply IHsmall_red.
    intuition.
    apply (lowering_respects_alpha_eq _ _ _ _ H0).

    apply (RedAbsTyp _ _ (lower typ' c d)).
    apply IHsmall_red.
    intuition.
    apply (lowering_respects_alpha_eq _ _ _ _ H0).

    apply (RedAbsBody _ _ _ (lower body' (c + 1) d)).
    apply IHsmall_red.
    intuition.
    intros.
    destruct v.
    exfalso; rewrite PeanoNat.Nat.add_1_r in H3; exact (PeanoNat.Nat.nle_succ_0 _ H3).
    rewrite PeanoNat.Nat.add_shuffle0.
    rewrite PeanoNat.Nat.add_1_r in H3; rewrite PeanoNat.Nat.add_1_r.
    apply Le.le_S_n in H3; apply Le.le_n_S.
    intuition.
    apply (lowering_respects_alpha_eq _ _ _ _ H0).
    
    apply (RedForallTyp _ _ (lower typ' c d)).
    apply IHsmall_red.
    intuition.
    apply (lowering_respects_alpha_eq _ _ _ _ H0).

    apply (RedForallBody _ _ _ (lower body' (c + 1) d)).
    apply IHsmall_red.
    intuition.
    destruct v.
    exfalso; rewrite PeanoNat.Nat.add_1_r in H3; exact (PeanoNat.Nat.nle_succ_0 _ H3).
    rewrite PeanoNat.Nat.add_shuffle0.
    rewrite PeanoNat.Nat.add_1_r in H3; rewrite PeanoNat.Nat.add_1_r.
    apply Le.le_S_n in H3; apply Le.le_n_S.
    intuition.
    apply (lowering_respects_alpha_eq _ _ _ _ H0).

    apply RedAppAbs.
    unfold top_subst.
    unfold lift1.
    rewrite <- (PeanoNat.Nat.add_0_r c) at 2.
    rewrite lift_lower_swap_ex.
    rewrite PeanoNat.Nat.add_0_r.
    rewrite lower_subst_unfold_alt.
    unfold clean_after_subst.
    rewrite <- (PeanoNat.Nat.add_0_r (c + 1)).
    rewrite lower_swap_ex.
    rewrite PeanoNat.Nat.add_0_r.
    change (lower (subst body 0 (lift val 0 1)) 0 1) with (top_subst body val).
    apply (lowering_respects_alpha_eq _ _ _ _ H).
    intros V H1.
    apply subst_respects_occurance in H1.
    destruct H1.
    destruct H1.
    destruct V.
    rewrite PeanoNat.Nat.add_0_r; intro H3; rewrite PeanoNat.Nat.add_1_r in H3; exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H3).
    rewrite <- (PeanoNat.Nat.add_1_r V) in H1.
    apply (lifting_respects_occurance_r _ _ _ _ (le_0_n _)) in H1.
    rewrite PeanoNat.Nat.add_0_r.
    intro H3.
    rewrite PeanoNat.Nat.add_shuffle0.
    rewrite PeanoNat.Nat.add_1_r; rewrite PeanoNat.Nat.add_1_r in H3.
    apply Le.le_n_S; apply Le.le_S_n in H3.
    intuition.
    destruct H1.
    destruct V; try easy.
    rewrite PeanoNat.Nat.add_0_r.
    intro H3.
    rewrite PeanoNat.Nat.add_shuffle0.
    rewrite PeanoNat.Nat.add_1_r; rewrite PeanoNat.Nat.add_1_r in H3.
    apply Le.le_n_S; apply Le.le_S_n in H3.
    intuition.
    intros v H1 H2.
    rewrite PeanoNat.Nat.add_1_r in H2.
    destruct v.
    exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H2).
    rewrite PeanoNat.Nat.add_shuffle0; rewrite PeanoNat.Nat.add_1_r.
    apply Le.le_n_S; apply Le.le_S_n in H2.
    rewrite <- (PeanoNat.Nat.add_1_r v) in H1.
    apply (lifting_respects_occurance_r _ _ _ _ (le_0_n _)) in H1.
    intuition.
    intros.
    rewrite PeanoNat.Nat.add_1_r in H2.
    destruct v.
    exfalso; exact (PeanoNat.Nat.nle_succ_0 _ H2).
    rewrite PeanoNat.Nat.add_shuffle0; rewrite PeanoNat.Nat.add_1_r.
    apply Le.le_n_S; apply Le.le_S_n in H2.
    intuition.
    rewrite PeanoNat.Nat.add_1_r; apply PeanoNat.Nat.lt_0_succ.
    rewrite PeanoNat.Nat.add_0_r.
    intuition.

    apply (NatRecRed _ _ _ _ (lower num' c d)).
    apply IHsmall_red.
    intuition.
    apply (lowering_respects_alpha_eq _ _ _ _ H0).

    apply NatRecTerminate.
    apply (lowering_respects_alpha_eq _ _ _ _ H).

    apply NatRecStep.
    apply (lowering_respects_alpha_eq _ _ _ _ H).
Qed.

(* Substitution respects one step *)
Theorem subst_respects_one_step : forall (l r : term) (v : nat) (N : term),
    (l ->b r) ->
    (subst l v N ->b subst r v N)
.
Proof.
    intros l r v N H.
    generalize v N; clear v N.
    induction H.

    simpl; intros.
    apply (RedAppL _ (subst l' v N)).
    apply IHsmall_red.
    apply (subst_respects_alpha_eq (App l' r) res N N).
    exact H0.
    reflexivity.

    simpl; intros.
    apply (RedAppR _ _ (subst r' v N)).
    apply IHsmall_red.
    apply (subst_respects_alpha_eq (App l r') res N N).
    exact H0.
    reflexivity.

    simpl; intros.
    apply (RedAbsTyp _ _ (subst typ' v N)).
    apply IHsmall_red.
    apply (subst_respects_alpha_eq (Abs str typ' body) res N N).
    exact H0.
    reflexivity.
    
    simpl; intros.
    apply (RedAbsBody _ _ _ (subst body' (v + 1) (lift1 N))).
    apply IHsmall_red.
    apply (subst_respects_alpha_eq (Abs str typ body') res N N).
    exact H0.
    reflexivity.

    simpl; intros.
    apply (RedForallTyp _ _ (subst typ' v N)).
    apply IHsmall_red.
    apply (subst_respects_alpha_eq (Forall str typ' body) res N N).
    exact H0.
    reflexivity.

    simpl; intros.
    apply (RedForallBody _ _ _ (subst body' (v + 1) (lift1 N))).
    apply IHsmall_red.
    apply (subst_respects_alpha_eq (Forall str typ body') res N N).
    exact H0.
    reflexivity.

    simpl; intros.
    apply RedAppAbs.
    rewrite top_subst_subst_swap.
    apply (subst_respects_alpha_eq (top_subst body val) res N N).
    exact H.
    reflexivity.

    simpl; intros.
    apply (NatRecRed _ _ _ _ (subst num' v N)).
    apply IHsmall_red.
    apply (subst_respects_alpha_eq (NatRec type_choice step terminate num') res N N).
    exact H0.
    reflexivity.

    simpl; intros.
    apply NatRecTerminate.
    apply (subst_respects_alpha_eq terminate res N N).
    exact H.
    reflexivity.

    simpl; intros.
    apply NatRecStep.
    apply (subst_respects_alpha_eq (App (App step num) (NatRec type_choice terminate step num)) res N N).
    exact H.
    reflexivity.
Qed.

(*TODO: one-step reduction is a decidable relation*)