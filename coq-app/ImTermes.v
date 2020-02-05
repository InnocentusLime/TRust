(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(*
  This is eventually the `coq-in-coq` project with
  natural numbers
*)

Require Export Arith.
Require Export Compare_dec.
Require Export Relations.

Require Import Termes.
Definition strict_term := Termes.term.

Implicit Types i k m n p : nat.

Section ImTermes.

  (* Scheme to split between kind and the lower level sorts *)
  Lemma sort_level_ind :
   forall P : sort -> Prop,
   P kind -> (forall s, is_prop s -> P s) -> forall s, P s.
  Proof.
    unfold is_prop in |- *.
    simple destruct s; auto.
  Qed.

  (* The De Brujin term *)
  Inductive term : Set :=
  | Ref : nat -> term
  | Abs : Termes.term -> term -> term
  | App : term -> term -> term
  (* Natural number eliminators *)
  | NatDestruct : Termes.term -> term -> term -> term -> term
  (* Bool and SumBool *)
  | BoolRec : Termes.term -> term -> term -> term -> term
  (* Recursion *)
  | Rec : Termes.term -> Termes.term -> Termes.term -> term -> term
  (* Box for strict terms *)
  | StrictBox : Termes.term -> term
  .

  (*
    TODO:
    replace the `NatRec` and `NatInd` with
    `NatRecKind`. Do that for other destructors
    and recursors which spread to more than one
    kind.
  *)

  Implicit Types A B M N T t u v : term.

  (* Term lifting *)
  Fixpoint lift_rec n t {struct t} : nat -> term :=
    fun k =>
    match t with
    | Ref i =>
        match le_gt_dec k i with
        | left _ => Ref (n + i)
        | right _ => Ref i
        end
    | Abs T M => Abs (Termes.lift_rec n T k) (lift_rec n M (S k))
    | App u v => App (lift_rec n u k) (lift_rec n v k)
    (* Natural numbers *)
    (* Eliminators *)
    | NatDestruct choice on_zero on_succ num => NatDestruct (Termes.lift_rec n choice k) (lift_rec n on_zero k) (lift_rec n on_succ k) (lift_rec n num k)
    (* Bool *)
    | BoolRec choice on_true on_false bool => BoolRec (Termes.lift_rec n choice k) (lift_rec n on_true k) (lift_rec n on_false k) (lift_rec n bool k)
    (* Refinment types *)
    (* well-founded recursion scheme *)
    | Rec type rel choice f => Rec (Termes.lift_rec n type k) (Termes.lift_rec n rel k) (Termes.lift_rec n choice k) (lift_rec n f k)
    | StrictBox x => StrictBox (Termes.lift_rec n x k)
    end
  .

  (* A shortcut *)
  Definition lift n t := lift_rec n t 0.

  (* 
    Substitution. A quit tricky definition, 
    but it does do lifting, just in a tricky
    hacky delayed way
  *)
  Fixpoint subst_rec (N : Termes.term) M {struct M} : nat -> term :=
    fun k =>
    match M with
    | Ref i =>
        match lt_eq_lt_dec k i with
        | inleft C =>
            match C with
            | left _ => Ref (pred i)
            | right _ => StrictBox (Termes.lift k N)
            end
        | inright _ => Ref i
        end
    | Abs A B => Abs (Termes.subst_rec N A k) (subst_rec N B (S k))
    | App u v => App (subst_rec N u k) (subst_rec N v k)
    (* Natural numbers *)
    (* Eliminators of natural numbers *)
    | NatDestruct choice on_zero on_succ num => NatDestruct (Termes.subst_rec N choice k) (subst_rec N on_zero k) (subst_rec N on_succ k) (subst_rec N num k)
    (* Bool and SumBool *)
    | BoolRec choice on_true on_false bool => BoolRec (Termes.subst_rec N choice k) (subst_rec N on_true k) (subst_rec N on_false k) (subst_rec N bool k)
    (* well-founded recursion scheme *)
    | Rec type rel choice f => Rec (Termes.subst_rec N type k) (Termes.subst_rec N rel k) (Termes.subst_rec N choice k) (subst_rec N f k)
    | StrictBox x => StrictBox (Termes.subst_rec N x k)
    end
  .

  (* Shortcut *)
  Definition subst (N : Termes.term) M := subst_rec N M 0.

End ImTermes.

Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Section ImBeta_Reduction.

  (* The one-step reduction *)
  Inductive red1 : term -> term -> Prop :=
  | beta : forall M (N T : Termes.term), red1 (App (Abs T M) (StrictBox N)) (subst N M)
  | abs_red_l :
    forall (M M' : Termes.term), Termes.red1 M M' -> forall N, red1 (Abs M N) (Abs M' N)
  | app_red_l :
    forall M1 N1, red1 M1 N1 -> forall M2, red1 (App M1 M2) (App N1 M2)
  | app_red_r :
    forall M2 N2, red1 M2 N2 -> forall M1, red1 (App M1 M2) (App M1 N2)
  (* Natrual numebers eliminators *)
  | nat_destruct_choice :
    forall choice on_zero on_succ num choice', Termes.red1 choice choice' -> red1 (NatDestruct choice on_zero on_succ num) (NatDestruct choice' on_zero on_succ num)
  | nat_destruct_num :
    forall choice on_zero on_succ num num', red1 num num' -> red1 (NatDestruct choice on_zero on_succ num) (NatDestruct choice on_zero on_succ num')
  | nat_destruct_choose_zero :
    forall choice on_zero on_succ, red1 (NatDestruct choice on_zero on_succ (StrictBox NatO)) on_zero
  | nat_destruct_choose_succ :
    forall choice on_zero on_succ num, red1 (NatDestruct choice on_zero on_succ (StrictBox (NatSucc num))) (App on_succ (StrictBox num))
  (* Bool and SumBool *)
  | bool_rec_choice : 
    forall choice choice' on_true on_false bool, Termes.red1 choice choice' -> red1 (BoolRec choice on_true on_false bool) (BoolRec choice' on_true on_false bool)
  | bool_rec_bool : 
    forall choice on_true on_false bool bool', red1 bool bool' -> red1 (BoolRec choice on_true on_false bool) (BoolRec choice on_true on_false bool')
  | bool_rec_true :
    forall choice on_true on_false, red1 (BoolRec choice on_true on_false (StrictBox BoolTrue)) on_true
  | bool_rec_false :
    forall choice on_true on_false, red1 (BoolRec choice on_true on_false (StrictBox BoolFalse)) on_false
  (* recursion *)
  | rec_type : 
    forall type type' rel choice f, Termes.red1 type type' -> red1 (Rec type rel choice f) (Rec type' rel choice f)
  | rec_rel : 
    forall type rel rel' choice f, Termes.red1 rel rel' -> red1 (Rec type rel choice f) (Rec type rel' choice f)
  | rec_choice : 
    forall type rel choice choice' f, Termes.red1 choice choice' -> red1 (Rec type rel choice f) (Rec type rel choice' f)
  | rec_step : 
    forall type rel choice f x,     
    red1 (App (Rec type rel choice f) x) (App (App f (Rec type rel choice f)) x)
  (* Greedy strict box *)
  | box_abs :
    forall (a b : Termes.term), red1 (Abs a (StrictBox b)) (StrictBox (Termes.Abs a b))
  | box_app :
    forall (a b : Termes.term), red1 (App (StrictBox a) (StrictBox b)) (StrictBox (Termes.App a b))
  | box : 
    forall (a b : Termes.term), Termes.red1 a b -> red1 (StrictBox a) (StrictBox b)
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

  (* The parallel one-step reduction *)
  Inductive par_red1 : term -> term -> Prop :=
  | par_beta :
    forall (N N' : Termes.term), Termes.par_red1 N N' -> 
    forall (T : Termes.term) M, par_red1 (App (Abs T M) (StrictBox N)) (subst N' M)
  | ref_par_red : forall n, par_red1 (Ref n) (Ref n)
  | abs_par_red :
    forall (T T' : Termes.term), Termes.par_red1 T T' -> 
    forall M, par_red1 (Abs T M) (Abs T' M)
  | app_par_red :
    forall M M', par_red1 M M' ->
    forall N N', par_red1 N N' -> 
    par_red1 (App M N) (App M' N')
  (* Natural number eliminators *)
  | nat_destruct_par_red :
    forall choice choice', Termes.par_red1 choice choice' ->
    forall num num', par_red1 num num' ->
    forall on_zero on_succ, par_red1 (NatDestruct choice on_zero on_succ num) (NatDestruct choice' on_zero on_succ num')
  | nat_destruct_on_zero_par_red :
    forall choice on_zero on_succ, par_red1 (NatDestruct choice on_zero on_succ (StrictBox Termes.NatO)) on_zero
  | nat_destruct_on_succ_par_red :
    forall num num', Termes.par_red1 num num' ->
    forall choice on_zero on_succ, par_red1 (NatDestruct choice on_zero on_succ (StrictBox (NatSucc num))) (App on_succ (StrictBox num')) 
  (* Bool and SumBool *)
  | bool_rec_par_red : 
    forall choice choice', Termes.par_red1 choice choice' -> 
    forall bool bool', par_red1 bool bool' ->
    forall on_true on_false, par_red1 (BoolRec choice on_true on_false bool) (BoolRec choice' on_true on_false bool')
  | bool_rec_true_par :
    forall choice on_true on_false, par_red1 (BoolRec choice on_true on_false (StrictBox (BoolTrue))) on_true
  | bool_rec_false_par :
    forall choice on_true on_false, par_red1 (BoolRec choice on_true on_false (StrictBox (BoolFalse))) on_false
  (* well-founded recursion scheme *)
  | rec_par_red : 
    forall type type', Termes.par_red1 type type' ->
    forall rel rel', Termes.par_red1 rel rel' ->
    forall choice choice', Termes.par_red1 choice choice' ->
    forall f f', par_red1 f f' -> 
    par_red1 (Rec type rel choice f) (Rec type' rel' choice' f')
  | rec_step_par : 
    forall type type', Termes.par_red1 type type' ->
    forall rel rel', Termes.par_red1 rel rel' ->
    forall choice choice', Termes.par_red1 choice choice' ->
    forall x x', par_red1 x x' ->
    forall f f', par_red1 f f' -> 
    par_red1 (App (Rec type rel choice f) x) (App (App f' (Rec type' rel' choice' f')) x')
  (* greedy box *)
  | box_abs_par :
    forall (a a' b b' : Termes.term), 
      Termes.par_red1 a a' ->
      Termes.par_red1 b b' ->
      par_red1 (Abs a (StrictBox b)) (StrictBox (Termes.Abs a' b'))
  | box_app_par :
    forall (a a' b b' : Termes.term), 
      Termes.par_red1 a a' ->
      Termes.par_red1 b b' ->
      par_red1 (App (StrictBox a) (StrictBox b)) (StrictBox (Termes.App a' b'))
  | box_par : 
    forall (a b : Termes.term), Termes.par_red1 a b -> par_red1 (StrictBox a) (StrictBox b)
  .

  (* Multistep parallel reduction *)
  Definition par_red := clos_trans term par_red1.

End ImBeta_Reduction.


Hint Resolve beta abs_red_l app_red_l app_red_r prod_red_l prod_red_r nat_destruct_choice 
  nat_destruct_num nat_destruct_choose_zero nat_destruct_choose_succ nat_succ_red
  bool_rec_choice bool_rec_bool bool_rec_true bool_rec_false refine_type refine_property
  rec_type rec_rel rec_choice rec_step box
  : coc.
Hint Resolve refl_red refl_conv: coc.
Hint Resolve par_beta sort_par_red ref_par_red abs_par_red app_par_red prod_par_red
  nat_destruct_par_red nat_destruct_on_zero_par_red nat_destruct_on_succ_par_red
  nat_succ_par_red nat_par_red nat_o_par_red bool_par_red bool_true_par_red bool_false_par_red
  bool_rec_par_red bool_rec_true_par bool_rec_false_par refine_par_red unit_par_red nil_par_red
  rec_par_red rec_step_par box_par
  : coc.

Hint Unfold par_red: coc.

(*)
Section Normalisation_Forte.

  (* Irreducable term *)
  Definition normal t : Prop := forall u, ~ red1 t u.

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
  elim (le_gt_dec p n); auto with coc core arith sets.
  intro; absurd (p <= n); auto with coc core arith sets.
Qed.


Lemma lift_ref_lt : forall k n p, p > n -> lift_rec k (Ref n) p = Ref n.
Proof.
  intros; simpl in |- *.
  elim (le_gt_dec p n); auto with coc core arith sets.
  intro; absurd (p <= n); auto with coc core arith sets.
Qed.


Lemma subst_ref_lt : forall u n k, k > n -> subst_rec u (Ref n) k = Ref n.
Proof.
  simpl in |- *; intros.
  elim (lt_eq_lt_dec k n); [ intro a | intro b; auto with coc core arith sets ].
  elim a; clear a; [ intro a | intro b ].
  absurd (k <= n); auto with coc core arith sets.

  inversion_clear b in H.
  elim gt_irrefl with n; auto with coc core arith sets.
Qed.


Lemma subst_ref_gt : forall u n k, n > k -> subst_rec u (Ref n) k = Ref (pred n).
Proof.
  simpl in |- *; intros.
  elim (lt_eq_lt_dec k n); [ intro a | intro b ].
  elim a; clear a; [ intro a; auto with coc core arith sets | intro b ].
  inversion_clear b in H.
  elim gt_irrefl with n; auto with coc core arith sets.

  absurd (k <= n); auto with coc core arith sets.
Qed.


Lemma subst_ref_eq : forall u n, subst_rec u (Ref n) n = lift n u.
Proof.
  intros; simpl in |- *.
  elim (lt_eq_lt_dec n n); [ intro a | intro b ].
  elim a; intros; auto with coc core arith sets.
  elim lt_irrefl with n; auto with coc core arith sets.

  elim gt_irrefl with n; auto with coc core arith sets.
Qed.



Lemma lift_rec0 : forall M k, lift_rec 0 M k = M.
Proof.
  simple induction M; 
  simpl in |- *; intros; 
  try rewrite H;
  try rewrite H0;
  try rewrite H1;
  try rewrite H2;
  try rewrite H3;
  try rewrite H4;
  auto with coc core arith sets.
  elim (le_gt_dec k n); auto with coc core arith sets.
Qed.

Lemma lift0 : forall M, lift 0 M = M.
Proof.
  intros; unfold lift in |- *.
  apply lift_rec0; auto with coc core arith sets.
Qed.

Lemma simpl_lift_rec :
  forall M n k p i,
  i <= k + n ->
  k <= i -> lift_rec p (lift_rec n M k) i = lift_rec (p + n) M k
.
Proof.
  simple induction M; 
  simpl in |- *; intros; 
  try (rewrite H by (auto with coc core arith sets); simpl in |- * );
  try (rewrite H0 by (auto with coc core arith sets); simpl in |- * );
  try (rewrite H1 by (auto with coc core arith sets); simpl in |- * );
  try (rewrite H2 by (auto with coc core arith sets); simpl in |- * );
  try (rewrite H3 by (auto with coc core arith sets); simpl in |- * );
  try (rewrite H4 by (auto with coc core arith sets); simpl in |- * );
  auto with coc core arith sets.

  elim (le_gt_dec k n); intros.
  rewrite lift_ref_ge; auto with coc core arith sets.
  rewrite plus_comm; apply le_trans with (k + n0);
  auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  apply le_gt_trans with k; auto with coc core arith sets.

  rewrite H0; simpl in |- *; auto with coc core arith sets.

  rewrite H0; simpl in |- *; auto with coc core arith sets.
Qed.


Lemma simpl_lift : forall M n, lift (S n) M = lift 1 (lift n M).
Proof.
  intros; unfold lift in |- *.
  rewrite simpl_lift_rec; auto with coc core arith sets.
Qed.


Lemma permute_lift_rec :
  forall M n k p i,
  i <= k ->
  lift_rec p (lift_rec n M k) i = lift_rec n (lift_rec p M i) (p + k)
.
Proof.
  simple induction M; 
  simpl in |- *; intros; 
  try rewrite H by (auto with coc core arith sets);
  try rewrite H0 by (auto with coc core arith sets);
  try rewrite H1 by (auto with coc core arith sets);
  try rewrite H2 by (auto with coc core arith sets);
  try rewrite H3 by (auto with coc core arith sets);
  try rewrite H4 by (auto with coc core arith sets);
  auto with coc core arith sets.
  
  elim (le_gt_dec k n); elim (le_gt_dec i n); intros.
  rewrite lift_ref_ge; auto with coc core arith sets.
  rewrite lift_ref_ge; auto with coc core arith sets.
  elim plus_assoc_reverse with p n0 n.
  elim plus_assoc_reverse with n0 p n.
  elim plus_comm with p n0; auto with coc core arith sets.
  apply le_trans with n; auto with coc core arith sets.
  absurd (i <= n); auto with coc core arith sets.
  apply le_trans with k; auto with coc core arith sets.
  rewrite lift_ref_ge; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  apply le_gt_trans with k; auto with coc core arith sets.

  rewrite plus_n_Sm; auto with coc core arith sets.

  rewrite plus_n_Sm; auto with coc core arith sets.
Qed.


Lemma permute_lift : forall M k, lift 1 (lift_rec 1 M k) = lift_rec 1 (lift 1 M) (S k).
Proof.
  intros.
  change (lift_rec 1 (lift_rec 1 M k) 0 = lift_rec 1 (lift_rec 1 M 0) (1 + k))
  in |- *.
  apply permute_lift_rec; auto with coc core arith sets.
Qed.


Lemma simpl_subst_rec :
  forall N M n p k,
  p <= n + k ->
  k <= p -> subst_rec N (lift_rec (S n) M k) p = lift_rec n M k
.
Proof.
  simple induction M; 
  simpl in |- *; intros; 
  try rewrite H by (auto with coc core arith sets);
  try rewrite H0 by (auto with coc core arith sets);
  try rewrite H1 by (auto with coc core arith sets);
  try rewrite H2 by (auto with coc core arith sets);
  try rewrite H3 by (auto with coc core arith sets);
  try rewrite H4 by (auto with coc core arith sets);
  auto with coc core arith sets.
  
  elim (le_gt_dec k n); intros.
  rewrite subst_ref_gt; auto with coc core arith sets.
  red in |- *; red in |- *.
  apply le_trans with (S (n0 + k)); auto with coc core arith sets.
  rewrite subst_ref_lt; auto with coc core arith sets.
  apply le_gt_trans with k; auto with coc core arith sets.

  rewrite H0; elim plus_n_Sm with n k; auto with coc core arith sets.

  rewrite H0; elim plus_n_Sm with n k; auto with coc core arith sets.
Qed.


Lemma simpl_subst :
  forall N M n p, p <= n -> subst_rec N (lift (S n) M) p = lift n M
.
Proof.
  intros; unfold lift in |- *.
  apply simpl_subst_rec; auto with coc core arith sets.
Qed.


Lemma commut_lift_subst_rec :
  forall M N n p k,
  k <= p ->
  lift_rec n (subst_rec N M p) k = subst_rec N (lift_rec n M k) (n + p).
Proof.
  simple induction M; 
  intros; 
  try (
    solve [
      simpl in |- *;
      try rewrite H by (auto with coc core arith sets);
      try rewrite H0 by (auto with coc core arith sets);
      try rewrite H1 by (auto with coc core arith sets);
      try rewrite H2 by (auto with coc core arith sets);
      try rewrite H3 by (auto with coc core arith sets);
      try rewrite H4 by (auto with coc core arith sets);
      auto with coc core arith sets
    ]
  );
  auto with coc core arith sets.

  unfold subst_rec at 1, lift_rec at 2 in |- *.
  elim (lt_eq_lt_dec p n);
  [ intro Hlt_eq; elim (le_gt_dec k n); [ intro Hle | intro Hgt ]
  | intro Hlt; elim (le_gt_dec k n); [ intro Hle | intro Hgt ] ].
  elim Hlt_eq; clear Hlt_eq.
  case n; [ intro Hlt | intros ].
  inversion_clear Hlt.
  unfold pred in |- *.
  rewrite lift_ref_ge; auto with coc core arith sets.
  rewrite subst_ref_gt; auto with coc core arith sets.
  elim plus_n_Sm with n0 n1.
  auto with coc core arith sets.
  apply le_trans with p; auto with coc core arith sets.
  simple induction 1.
  rewrite subst_ref_eq.
  unfold lift in |- *.
  rewrite simpl_lift_rec; auto with coc core arith sets.
  absurd (k <= n); auto with coc core arith sets.
  apply le_trans with p; auto with coc core arith sets.
  elim Hlt_eq; auto with coc core arith sets.
  simple induction 1; auto with coc core arith sets.
  rewrite lift_ref_ge; auto with coc core arith sets.
  rewrite subst_ref_lt; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_lt; auto with coc core arith sets.
  apply le_gt_trans with p; auto with coc core arith sets.

  simpl in |- *.
  rewrite plus_n_Sm.
  rewrite H; auto with coc core arith sets; rewrite H0;
  auto with coc core arith sets.

  simpl in |- *; rewrite plus_n_Sm.
  rewrite H; auto with coc core arith sets; rewrite H0;
  auto with coc core arith sets.
Qed.


Lemma commut_lift_subst :
   forall M N k, subst_rec N (lift 1 M) (S k) = lift 1 (subst_rec N M k).
Proof.
  intros; unfold lift in |- *.
  rewrite commut_lift_subst_rec; auto with coc core arith sets.
Qed.


Lemma distr_lift_subst_rec :
  forall M N n p k,
  lift_rec n (subst_rec N M p) (p + k) =
  subst_rec (lift_rec n N k) (lift_rec n M (S (p + k))) p.
Proof.
  simple induction M; intros; 
  try (
    solve [
      simpl in |- *;
      try rewrite H;
      try rewrite H0;
      try rewrite H1;
      try rewrite H2;
      try rewrite H3;
      try rewrite H4;
      auto with coc core arith sets
    ]
  );
  auto with coc core arith sets.

  unfold subst_rec at 1 in |- *.
  elim (lt_eq_lt_dec p n); [ intro a | intro b ].
  elim a; clear a.
  case n; [ intro a | intros n1 b ].
  inversion_clear a.
  unfold pred, lift_rec at 1 in |- *.
  elim (le_gt_dec (p + k) n1); intro.
  rewrite lift_ref_ge; auto with coc core arith sets.
  elim plus_n_Sm with n0 n1.
  rewrite subst_ref_gt; auto with coc core arith sets.
  red in |- *; red in |- *; apply le_n_S.
  apply le_trans with (n0 + (p + k)); auto with coc core arith sets.
  apply le_trans with (p + k); auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_gt; auto with coc core arith sets.
  simple induction 1.
  unfold lift in |- *.
  rewrite <- permute_lift_rec; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_eq; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite lift_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_lt; auto with coc core arith sets.

  simpl in |- *; replace (S (p + k)) with (S p + k);
  auto with coc core arith sets.
  rewrite H; rewrite H0; auto with coc core arith sets.

  simpl in |- *; replace (S (p + k)) with (S p + k);
  auto with coc core arith sets.
  rewrite H; rewrite H0; auto with coc core arith sets.
Qed.


Lemma distr_lift_subst :
  forall M N n k,
  lift_rec n (subst N M) k = subst (lift_rec n N k) (lift_rec n M (S k))
.
Proof.
  intros; unfold subst in |- *.
  pattern k at 1 3 in |- *.
  replace k with (0 + k); auto with coc core arith sets.
  apply distr_lift_subst_rec.
Qed.


Lemma distr_subst_rec :
  forall M N (P : term) n p,
  subst_rec P (subst_rec N M p) (p + n) =
  subst_rec (subst_rec P N n) (subst_rec P M (S (p + n))) p
.
Proof.
  simple induction M; 
  auto with coc core arith sets; intros;
  try (
    solve [
      simpl in |- *;
      try rewrite H;
      try rewrite H0;
      try rewrite H1;
      try rewrite H2;
      try rewrite H3;
      try rewrite H4;
      auto with coc core arith sets
    ]
  ).

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
  rewrite subst_ref_gt; auto with coc core arith sets.
  rewrite subst_ref_gt; auto with coc core arith sets.
  apply gt_le_trans with (p + n0); auto with coc core arith sets.
  simple induction 1.
  rewrite subst_ref_eq; auto with coc core arith sets.
  rewrite simpl_subst; auto with coc core arith sets.
  rewrite subst_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_gt; auto with coc core arith sets.
  simple induction 1.
  rewrite subst_ref_lt; auto with coc core arith sets.
  rewrite subst_ref_eq.
  unfold lift in |- *.
  rewrite commut_lift_subst_rec; auto with coc core arith sets.
  do 3 (rewrite subst_ref_lt; auto with coc core arith sets).

  simpl in |- *; replace (S (p + n)) with (S p + n);
  auto with coc core arith sets.
  rewrite H; auto with coc core arith sets; rewrite H0;
  auto with coc core arith sets.

  simpl in |- *; replace (S (p + n)) with (S p + n);
  auto with coc core arith sets.
  rewrite H; rewrite H0; auto with coc core arith sets.
Qed.


Lemma distr_subst :
  forall (P : term) N M k,
  subst_rec P (subst N M) k = subst (subst_rec P N k) (subst_rec P M (S k))
.
Proof.
  intros; unfold subst in |- *.
  pattern k at 1 3 in |- *.
  replace k with (0 + k); auto with coc core arith sets.
  apply distr_subst_rec.
Qed.

(*
LEMMAS ABOUT BETA REDUCTION
===================================================================================
*)


Lemma one_step_red : forall M N, red1 M N -> red M N.
Proof.
  intros.
  apply trans_red with M; auto with coc core arith sets.
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
  apply (H M N); auto with coc core arith sets.

  simple induction 1; intros; auto with coc core arith sets.
  apply H1; auto with coc core arith sets.
  apply H4 with N0; auto with coc core arith sets.

  intros.
  apply H4 with R; auto with coc core arith sets.
  apply trans_red with P; auto with coc core arith sets.
Qed.


Lemma trans_red_red : forall M N (P : term), red M N -> red N P -> red M P.
Proof.
  intros.
  generalize H0 M H.
  simple induction 1; auto with coc core arith sets.
  intros.
  apply trans_red with P0; auto with coc core arith sets.
Qed.
 

Lemma red_red_app :
  forall u u0 v v0, red u u0 -> red v v0 -> red (App u v) (App u0 v0)
.
Proof.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.
  apply trans_red with (App u P); auto with coc core arith sets.

  intros.
  apply trans_red with (App P v0); auto with coc core arith sets.
Qed.


Lemma red_red_abs :
  forall u u0 v v0, red u u0 -> red v v0 -> red (Abs u v) (Abs u0 v0)
.
Proof.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.
  apply trans_red with (Abs u P); auto with coc core arith sets.

  intros.
  apply trans_red with (Abs P v0); auto with coc core arith sets.
Qed.


Lemma red_red_prod :
  forall u u0 v v0, red u u0 -> red v v0 -> red (Prod u v) (Prod u0 v0)
.
Proof.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.
  apply trans_red with (Prod u P); auto with coc core arith sets.

  intros.
  apply trans_red with (Prod P v0); auto with coc core arith sets.
Qed.

Lemma red_red_nat_destruct :
  forall choice choice0 on_zero on_zero0 on_succ on_succ0 num num0,
  red choice choice0 -> red on_zero on_zero0 -> red on_succ on_succ0 ->
  red num num0 -> red (NatDestruct choice on_zero on_succ num) (NatDestruct choice0 on_zero0 on_succ0 num0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (NatDestruct choice on_zero on_succ P); auto with coc core arith sets.

  intros.
  apply trans_red with (NatDestruct choice on_zero P num0); auto with coc core arith sets.

  intros.
  apply trans_red with (NatDestruct choice P on_succ0 num0); auto with coc core arith sets.

  intros.
  apply trans_red with (NatDestruct P on_zero0 on_succ0 num0); auto with coc core arith sets.
Qed.

Lemma red_red_nat_cases :
  forall choice choice0 on_zero on_zero0 on_succ on_succ0 num num0,
  red choice choice0 -> red on_zero on_zero0 -> red on_succ on_succ0 ->
  red num num0 -> red (NatCases choice on_zero on_succ num) (NatCases choice0 on_zero0 on_succ0 num0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (NatCases choice on_zero on_succ P); auto with coc core arith sets.

  intros.
  apply trans_red with (NatCases choice on_zero P num0); auto with coc core arith sets.

  intros.
  apply trans_red with (NatCases choice P on_succ0 num0); auto with coc core arith sets.

  intros.
  apply trans_red with (NatCases P on_zero0 on_succ0 num0); auto with coc core arith sets.
Qed.

Lemma red_red_nat_succ :
  forall x x0,
  red x x0 -> red (NatSucc x) (NatSucc x0)
.
Proof.
  simple induction 1; auto with coc core arith sets.

  intros.
  apply trans_red with (NatSucc P); auto with coc core arith sets.
Qed.

Lemma red_red_nat_rec :
  forall choice choice0 on_zero on_zero0 on_succ on_succ0 num num0,
  red choice choice0 -> red on_zero on_zero0 -> red on_succ on_succ0 ->
  red num num0 -> red (NatRec choice on_zero on_succ num) (NatRec choice0 on_zero0 on_succ0 num0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (NatRec choice on_zero on_succ P); auto with coc core arith sets.

  intros.
  apply trans_red with (NatRec choice on_zero P num0); auto with coc core arith sets.

  intros.
  apply trans_red with (NatRec choice P on_succ0 num0); auto with coc core arith sets.

  intros.
  apply trans_red with (NatRec P on_zero0 on_succ0 num0); auto with coc core arith sets.
Qed.

Lemma red_red_nat_ind :
  forall choice choice0 on_zero on_zero0 on_succ on_succ0 num num0,
  red choice choice0 -> red on_zero on_zero0 -> red on_succ on_succ0 ->
  red num num0 -> red (NatInd choice on_zero on_succ num) (NatInd choice0 on_zero0 on_succ0 num0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (NatInd choice on_zero on_succ P); auto with coc core arith sets.

  intros.
  apply trans_red with (NatInd choice on_zero P num0); auto with coc core arith sets.

  intros.
  apply trans_red with (NatInd choice P on_succ0 num0); auto with coc core arith sets.

  intros.
  apply trans_red with (NatInd P on_zero0 on_succ0 num0); auto with coc core arith sets.
Qed.

Lemma red_red_acc_prop :
  forall type type0 rel rel0 val val0,
  red type type0 -> red rel rel0 -> red val val0 ->
  red (AccProp type rel val) (AccProp type0 rel0 val0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (AccProp type rel P); auto with coc core arith sets.

  intros.
  apply trans_red with (AccProp type P val0); auto with coc core arith sets.

  intros.
  apply trans_red with (AccProp P rel0 val0); auto with coc core arith sets.
Qed.

Lemma red_red_acc_intro :
  forall type type0 rel rel0 val val0 proof proof0,
  red type type0 -> red rel rel0 -> red val val0 -> red proof proof0 ->
  red (AccIntro type rel val proof) (AccIntro type0 rel0 val0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (AccIntro type rel val P); auto with coc core arith sets.

  intros.
  apply trans_red with (AccIntro type rel P proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (AccIntro type P val0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (AccIntro P rel0 val0 proof0); auto with coc core arith sets.
Qed.

Lemma red_red_acc_rec :
  forall type type0 rel rel0 choice choice0 f f0 val val0 proof proof0,
  red type type0 -> red rel rel0 -> red choice choice0 -> red f f0 ->
  red val val0 -> red proof proof0 ->
  red (AccRec type rel choice f val proof) (AccRec type0 rel0 choice0 f0 val0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (AccRec type rel choice f val P); auto with coc core arith sets.

  intros.
  apply trans_red with (AccRec type rel choice f P proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (AccRec type rel choice P val0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (AccRec type rel P f0 val0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (AccRec type P choice0 f0 val0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (AccRec P rel0 choice0 f0 val0 proof0); auto with coc core arith sets.
Qed.

Lemma red_red_acc_ind :
  forall type type0 rel rel0 choice choice0 f f0 val val0 proof proof0,
  red type type0 -> red rel rel0 -> red choice choice0 -> red f f0 ->
  red val val0 -> red proof proof0 ->
  red (AccInd type rel choice f val proof) (AccInd type0 rel0 choice0 f0 val0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (AccInd type rel choice f val P); auto with coc core arith sets.

  intros.
  apply trans_red with (AccInd type rel choice f P proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (AccInd type rel choice P val0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (AccInd type rel P f0 val0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (AccInd type P choice0 f0 val0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (AccInd P rel0 choice0 f0 val0 proof0); auto with coc core arith sets.
Qed. 

Lemma red_red_le :
  forall l l0 r r0,
  red l l0 -> red r r0 -> red (Le l r) (Le l0 r0)
.
Proof.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (Le l P); auto with coc core arith sets.

  intros.
  apply trans_red with (Le P r0); auto with coc core arith sets.
Qed.

Lemma red_red_le_n :
  forall n n0 : term,
  red n n0 -> red (LeN n) (LeN n0)
.
Proof.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (LeN P); auto with coc core arith sets.
Qed.

Lemma red_red_le_s :
  forall l l0 r r0 proof proof0,
  red l l0 -> red r r0 -> red proof proof0 ->
  red (LeS l r proof) (LeS l0 r0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (LeS l r P); auto with coc core arith sets.

  intros.
  apply trans_red with (LeS l P proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (LeS P r0 proof0); auto with coc core arith sets.
Qed.

Lemma red_red_le_cases :
  forall choice choice0 on_le_n on_le_n0 on_le_s on_le_s0 l l0 r r0 proof proof0,
  red choice choice0 -> red on_le_n on_le_n0 -> red on_le_s on_le_s0 -> red l l0 ->
  red r r0 -> red proof proof0 ->
  red (LeCases choice on_le_n on_le_s l r proof) (LeCases choice0 on_le_n0 on_le_s0 l0 r0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (LeCases choice on_le_n on_le_s l r P); auto with coc core arith sets.

  intros.
  apply trans_red with (LeCases choice on_le_n on_le_s l P proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (LeCases choice on_le_n on_le_s P r0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (LeCases choice on_le_n P l0 r0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (LeCases choice P on_le_s0 l0 r0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (LeCases P on_le_n0 on_le_s0 l0 r0 proof0); auto with coc core arith sets.
Qed.

Lemma red_red_le_ind :
  forall choice choice0 on_le_n on_le_n0 on_le_s on_le_s0 l l0 r r0 proof proof0,
  red choice choice0 -> red on_le_n on_le_n0 -> red on_le_s on_le_s0 -> red l l0 ->
  red r r0 -> red proof proof0 ->
  red (LeInd choice on_le_n on_le_s l r proof) (LeInd choice0 on_le_n0 on_le_s0 l0 r0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (LeInd choice on_le_n on_le_s l r P); auto with coc core arith sets.

  intros.
  apply trans_red with (LeInd choice on_le_n on_le_s l P proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (LeInd choice on_le_n on_le_s P r0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (LeInd choice on_le_n P l0 r0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (LeInd choice P on_le_s0 l0 r0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (LeInd P on_le_n0 on_le_s0 l0 r0 proof0); auto with coc core arith sets.
Qed.

Lemma red_red_sumbool :
  forall l l0 r r0,
  red l l0 -> red r r0 -> 
  red (SumBool l r) (SumBool l0 r0)
.
Proof.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (SumBool l P); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBool P r0); auto with coc core arith sets.
Qed.

Lemma red_red_sumbool_left :
  forall left_pred left_pred0 right_pred right_pred0 proof proof0,
  red left_pred left_pred0 -> red right_pred right_pred0 -> red proof proof0 ->
  red (SumBoolLeft left_pred right_pred proof) (SumBoolLeft left_pred0 right_pred0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (SumBoolLeft left_pred right_pred P); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolLeft left_pred P proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolLeft P right_pred0 proof0); auto with coc core arith sets.
Qed.

Lemma red_red_sumbool_right :
  forall left_pred left_pred0 right_pred right_pred0 proof proof0,
  red left_pred left_pred0 -> red right_pred right_pred0 -> red proof proof0 ->
  red (SumBoolRight left_pred right_pred proof) (SumBoolRight left_pred0 right_pred0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (SumBoolRight left_pred right_pred P); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolRight left_pred P proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolRight P right_pred0 proof0); auto with coc core arith sets.
Qed.

Lemma red_red_bool_ind :
  forall choice choice0 on_true on_true0 on_false on_false0 bool bool0 : term,
  red choice choice0 -> red on_true on_true0 -> red on_false on_false0 ->
  red bool bool0 ->
  red (BoolInd choice on_true on_false bool) (BoolInd choice0 on_true0 on_false0 bool0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (BoolInd choice on_true on_false P); auto with coc core arith sets.

  intros.
  apply trans_red with (BoolInd choice on_true P bool0); auto with coc core arith sets.

  intros.
  apply trans_red with (BoolInd choice P on_false0 bool0); auto with coc core arith sets.

  intros.
  apply trans_red with (BoolInd P on_true0 on_false0 bool0); auto with coc core arith sets.
Qed.

Lemma red_red_bool_rec :
  forall choice choice0 on_true on_true0 on_false on_false0 bool bool0 : term,
  red choice choice0 -> red on_true on_true0 -> red on_false on_false0 ->
  red bool bool0 ->
  red (BoolRec choice on_true on_false bool) (BoolRec choice0 on_true0 on_false0 bool0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (BoolRec choice on_true on_false P); auto with coc core arith sets.

  intros.
  apply trans_red with (BoolRec choice on_true P bool0); auto with coc core arith sets.

  intros.
  apply trans_red with (BoolRec choice P on_false0 bool0); auto with coc core arith sets.

  intros.
  apply trans_red with (BoolRec P on_true0 on_false0 bool0); auto with coc core arith sets.
Qed.

Lemma red_red_sumbool_ind :
  forall left_pred left_pred0 right_pred right_pred0 choice choice0 on_left on_left0
  on_right on_right0 val val0,
  red left_pred left_pred0 -> red right_pred right_pred0 -> red choice choice0 ->
  red on_left on_left0 -> red on_right on_right0 -> red val val0 ->
  red (SumBoolInd left_pred right_pred choice on_left on_right val) (SumBoolInd left_pred0 right_pred0 choice0 on_left0 on_right0 val0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (SumBoolInd left_pred right_pred choice on_left on_right P); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolInd left_pred right_pred choice on_left P val0); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolInd left_pred right_pred choice P on_right0 val0); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolInd left_pred right_pred P on_left0 on_right0 val0); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolInd left_pred P choice0 on_left0 on_right0 val0); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolInd P right_pred0 choice0 on_left0 on_right0 val0); auto with coc core arith sets.
Qed.

Lemma red_red_sumbool_rec :
  forall left_pred left_pred0 right_pred right_pred0 choice choice0 on_left on_left0
  on_right on_right0 val val0,
  red left_pred left_pred0 -> red right_pred right_pred0 -> red choice choice0 ->
  red on_left on_left0 -> red on_right on_right0 -> red val val0 ->
  red (SumBoolRec left_pred right_pred choice on_left on_right val) (SumBoolRec left_pred0 right_pred0 choice0 on_left0 on_right0 val0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (SumBoolRec left_pred right_pred choice on_left on_right P); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolRec left_pred right_pred choice on_left P val0); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolRec left_pred right_pred choice P on_right0 val0); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolRec left_pred right_pred P on_left0 on_right0 val0); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolRec left_pred P choice0 on_left0 on_right0 val0); auto with coc core arith sets.

  intros.
  apply trans_red with (SumBoolRec P right_pred0 choice0 on_left0 on_right0 val0); auto with coc core arith sets.
Qed.

Lemma red_red_refine :
  forall type type0 property property0,
  red type type0 -> red property property0 ->
  red (Refine type property) (Refine type0 property0)
.
Proof.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (Refine type P); auto with coc core arith sets.

  intros.
  apply trans_red with (Refine P property0); auto with coc core arith sets.
Qed.

Lemma red_red_refine_constr :
  forall type type0 property property0 val val0 proof proof0,
  red type type0 -> red property property0 -> red val val0 ->
  red proof proof0 ->
  red (RefineConstr type property val proof) (RefineConstr type0 property0 val0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (RefineConstr type property val P); auto with core coc arith sets.

  intros.
  apply trans_red with (RefineConstr type property P proof0); auto with core coc arith sets.

  intros.
  apply trans_red with (RefineConstr type P val0 proof0); auto with core coc arith sets.

  intros.
  apply trans_red with (RefineConstr P property0 val0 proof0); auto with core coc arith sets.
Qed.

Lemma red_red_proj_val :
  forall x x0,
  red x x0 -> red (RefineProjVal x) (RefineProjVal x0)
.
Proof.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (RefineProjVal P); auto with coc core arith sets.
Qed.

Lemma red_red_proj_proof :
  forall x x0,
  red x x0 -> red (RefineProjProof x) (RefineProjProof x0)
.
Proof.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (RefineProjProof P); auto with coc core arith sets.
Qed.

Lemma red_red_eq :
  forall type type0 l l0 r r0,
  red type type0 -> red l l0 -> red r r0 ->
  red (Eq type l r) (Eq type0 l0 r0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (Eq type l P); auto with coc core arith sets.

  intros.
  apply trans_red with (Eq type P r0); auto with coc core arith sets.

  intros.
  apply trans_red with (Eq P l0 r0); auto with coc core arith sets.
Qed.

Lemma red_red_eq_refl :
  forall type type0 val val0,
  red type type0 -> red val val0 ->
  red (EqRefl type val) (EqRefl type0 val0)
.
Proof.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (EqRefl type P); auto with coc core arith sets.

  intros.
  apply trans_red with (EqRefl P val0); auto with coc core arith sets.
Qed.

Lemma red_red_eq_ind :
  forall type type0 l l0 r r0 property property0 impl impl0 proof proof0,
  red type type0 -> red l l0 -> red r r0 -> red property property0 -> 
  red impl impl0 -> red proof proof0 ->
  red (EqInd type l r property impl proof) (EqInd type0 l0 r0 property0 impl0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (EqInd type l r property impl P); auto with coc core arith sets.

  intros.
  apply trans_red with (EqInd type l r property P proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (EqInd type l r P impl0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (EqInd type l P property0 impl0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (EqInd type P r0 property0 impl0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (EqInd P l0 r0 property0 impl0 proof0); auto with coc core arith sets.
Qed.

Lemma red_red_eq_rec :
  forall type type0 l l0 r r0 property property0 impl impl0 proof proof0,
  red type type0 -> red l l0 -> red r r0 -> red property property0 -> 
  red impl impl0 -> red proof proof0 ->
  red (EqRec type l r property impl proof) (EqRec type0 l0 r0 property0 impl0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (EqRec type l r property impl P); auto with coc core arith sets.

  intros.
  apply trans_red with (EqRec type l r property P proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (EqRec type l r P impl0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (EqRec type l P property0 impl0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (EqRec type P r0 property0 impl0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (EqRec P l0 r0 property0 impl0 proof0); auto with coc core arith sets.
Qed.

Lemma red_red_false_ind :
  forall proof proof0 property property0,
  red proof proof0 -> red property property0 ->
  red (FalseInd proof property) (FalseInd proof0 property0)
.
Proof.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (FalseInd proof P); auto with coc core arith sets.

  intros.
  apply trans_red with (FalseInd P property0); auto with coc core arith sets.
Qed.

Lemma red_red_false_rec :
  forall proof proof0 property property0,
  red proof proof0 -> red property property0 ->
  red (FalseRec proof property) (FalseRec proof0 property0)
.
Proof.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (FalseRec proof P); auto with coc core arith sets.

  intros.
  apply trans_red with (FalseRec P property0); auto with coc core arith sets.
Qed.

Lemma red_red_wf_rec :
  forall type type0 rel rel0 choice choice0 f f0 proof proof0,
  red type type0 -> red rel rel0 -> red choice choice0 -> red f f0 ->
  red proof proof0 -> 
  red (WFrec type rel choice f proof) (WFrec type0 rel0 choice0 f0 proof0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (WFrec type rel choice f P); auto with coc core arith sets.

  intros.
  apply trans_red with (WFrec type rel choice P proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (WFrec type rel P f0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (WFrec type P choice0 f0 proof0); auto with coc core arith sets.

  intros.
  apply trans_red with (WFrec P rel0 choice0 f0 proof0); auto with coc core arith sets.
Qed.

Lemma red_red_bool_prop_choice :
  forall on_true on_true0 on_false on_false0 val val0,
  red on_true on_true0 -> red on_false on_false0 -> red val val0 ->
  red (BoolPropChoice on_true on_false val) (BoolPropChoice on_true0 on_false0 val0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red_red with (BoolPropChoice on_true on_false P); auto with coc.

  intros.
  apply trans_red_red with (BoolPropChoice on_true P val0); auto with coc.

  intros.
  apply trans_red_red with (BoolPropChoice P on_false0 val0); auto with coc.
Qed.

Hint Resolve 
  red_red_app red_red_abs red_red_prod red_red_nat_destruct 
  red_red_nat_cases red_red_nat_succ
  red_red_nat_rec red_red_nat_ind red_red_acc_prop red_red_acc_intro
  red_red_acc_rec red_red_acc_ind red_red_le red_red_le_n 
  red_red_le_s red_red_le_cases red_red_le_ind red_red_sumbool 
  red_red_sumbool_left red_red_sumbool_right red_red_bool_ind
  red_red_bool_rec red_red_sumbool_ind red_red_sumbool_rec
  red_red_refine red_red_refine_constr red_red_proj_val red_red_proj_proof
  red_red_eq red_red_eq_refl red_red_eq_ind red_red_eq_rec red_red_false_ind
  red_red_false_rec red_red_wf_rec red_red_bool_prop_choice
  : coc.



(* lifting preserves one-step reduction *)
Lemma red1_lift :
  forall u v, red1 u v -> forall n k, red1 (lift_rec n u k) (lift_rec n v k)
.
Proof.
  simple induction 1; simpl in |- *; intros; auto with coc core arith sets.
  rewrite distr_lift_subst; auto with coc core arith sets.

  change (S (S k)) with (2 + k).
  unfold lift.
  repeat (rewrite <- permute_lift_rec by auto with coc core arith sets).
  apply acc_rec_exec.
  
  change (S (S k)) with (2 + k).
  unfold lift.
  repeat rewrite <- permute_lift_rec by auto with coc core arith sets.
  apply acc_ind_exec.

  change (S (S (S (S k)))) with (4 + k).
  change (S (S (S k))) with (3 + k).
  change (S (S k)) with (2 + k).
  unfold lift.
  repeat rewrite <- permute_lift_rec by auto with coc core arith sets.
  apply wf_rec_expand.
Qed.

Hint Resolve red1_lift: coc.

(* substituition respects one step reduction V1 *)
Lemma red1_subst_r :
  forall t u,
  red1 t u -> forall (a : term) k, red1 (subst_rec a t k) (subst_rec a u k)
.
Proof.
  simple induction 1; simpl in |- *; intros; auto with coc core arith sets.
  rewrite distr_subst; auto with coc core arith sets.

  change (S (S k)) with (2 + k).
  unfold lift.
  repeat rewrite <- commut_lift_subst_rec by auto with coc core arith sets.
  apply acc_rec_exec.

  change (S (S k)) with (2 + k).
  unfold lift.
  repeat rewrite <- commut_lift_subst_rec by auto with coc core arith sets.
  apply acc_ind_exec.

  change (S (S (S (S k)))) with (4 + k).
  change (S (S (S k))) with (3 + k).
  change (S (S k)) with (2 + k).
  unfold lift.
  repeat rewrite <- commut_lift_subst_rec by auto with coc core arith sets.
  apply wf_rec_expand.
Qed.


(* substituition respects one step reduction V2 *)
Lemma red1_subst_l :
  forall (a : term) t u k,
  red1 t u -> red (subst_rec t a k) (subst_rec u a k)
.
Proof.
  simple induction a; simpl in |- *; auto with coc core arith sets.

  intros.
  elim (lt_eq_lt_dec k n);
  [ intro a0 | intro b; auto with coc core arith sets ].
  elim a0; auto with coc core arith sets.
  unfold lift in |- *; auto with coc core arith sets.
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
  apply H0 with u v; auto with coc core arith sets.

  apply H1; intros.
  inversion_clear H4 in H2.
  inversion H2.
  apply H3 with N1 b; auto with coc core arith sets.
  apply trans_red with a; auto with coc core arith sets.

  apply H3 with a N2; auto with coc core arith sets.
  apply trans_red with b; auto with coc core arith sets.
Qed.


(* A sort doesn't reduce to anything than itself *)
Lemma red_sort_sort : forall s t, red (Srt s) t -> t <> Srt s -> False.
Proof.
  simple induction 1; intros; auto with coc core arith sets.
  apply H1.
  generalize H2.
  case P; intros; try discriminate.
  inversion_clear H4.
Qed.



(* relation between one-step reduction and convertibility *)
Lemma one_step_conv_exp : forall M N, red1 M N -> conv N M.
Proof.
  intros.
  apply trans_conv_exp with N; auto with coc core arith sets.
Qed.


(* relation between reduction and convertability *)
Lemma red_conv : forall M N, red M N -> conv M N.
Proof.
  simple induction 1; auto with coc core arith sets.
  intros; apply trans_conv_red with P; auto with coc core arith sets.
Qed.

Hint Resolve one_step_conv_exp red_conv: coc.


(* Convertability is symmetric *)
Lemma sym_conv : forall M N, conv M N -> conv N M.
Proof.
  simple induction 1; auto with coc core arith sets.
  simple induction 2; intros; auto with coc core arith sets.
  apply trans_conv_red with P0; auto with coc core arith sets.

  apply trans_conv_exp with P0; auto with coc core arith sets.

  simple induction 2; intros; auto with coc core arith sets.
  apply trans_conv_red with P0; auto with coc core arith sets.

  apply trans_conv_exp with P0; auto with coc core arith sets.
Qed.

Hint Immediate sym_conv: coc.


(* Convertability is transitive *)
Lemma trans_conv_conv :
  forall M N (P : term), conv M N -> conv N P -> conv M P
.
Proof.
  intros.
  generalize M H; elim H0; intros; auto with coc core arith sets.
  apply trans_conv_red with P0; auto with coc core arith sets.

  apply trans_conv_exp with P0; auto with coc core arith sets.
Qed.


(* Convertability and product *)
Lemma conv_conv_prod :
  forall a b c d : term, conv a b -> conv c d -> conv (Prod a c) (Prod b d).
Proof.
  intros.
  apply trans_conv_conv with (Prod a d).
  elim H0; intros; auto with coc core arith sets.
  apply trans_conv_red with (Prod a P); auto with coc core arith sets.

  apply trans_conv_exp with (Prod a P); auto with coc core arith sets.

  elim H; intros; auto with coc core arith sets.
  apply trans_conv_red with (Prod P d); auto with coc core arith sets.

  apply trans_conv_exp with (Prod P d); auto with coc core arith sets.
Qed.


Lemma conv_conv_lift :
  forall (a b : term) n k,
  conv a b -> conv (lift_rec n a k) (lift_rec n b k)
.
Proof.
  intros.
  elim H; intros; auto with coc core arith sets.
  apply trans_conv_red with (lift_rec n P k); auto with coc core arith sets.

  apply trans_conv_exp with (lift_rec n P k); auto with coc core arith sets.
Qed.
 

Lemma conv_conv_subst :
  forall (a b c d : term) k,
  conv a b -> conv c d -> conv (subst_rec a c k) (subst_rec b d k)
.
Proof.
  intros.
  apply trans_conv_conv with (subst_rec a d k).
  elim H0; intros; auto with coc core arith sets.
  apply trans_conv_red with (subst_rec a P k); auto with coc core arith sets.

  apply trans_conv_exp with (subst_rec a P k); auto with coc core arith sets.

  elim H; intros; auto with coc core arith sets.
  apply trans_conv_conv with (subst_rec P d k); auto with coc core arith sets.

  apply trans_conv_conv with (subst_rec P d k); auto with coc core arith sets.
  apply sym_conv; auto with coc core arith sets.
Qed.

Hint Resolve conv_conv_prod conv_conv_lift conv_conv_subst: coc.


Lemma refl_par_red1 : forall M, par_red1 M M.
Proof.
  simple induction M; auto with coc core arith sets.
Qed.

Hint Resolve refl_par_red1: coc.


Lemma red1_par_red1 : forall M N, red1 M N -> par_red1 M N.
Proof.
  simple induction 1; auto with coc core arith sets; intros.
Qed.

Hint Resolve red1_par_red1: coc.


Lemma red_par_red : forall M N, red M N -> par_red M N.
Proof.
  red in |- *; simple induction 1; intros; auto with coc core arith sets.
  apply t_trans with P; auto with coc core arith sets.
Qed.

Hint Resolve red_par_red: coc.

Lemma red_lift :
  forall u v, red u v -> forall n k, red (lift_rec n u k) (lift_rec n v k)
.
Proof.
  simple induction 1; intros; auto with coc core arith sets.
  apply trans_red with (lift_rec n P k); auto with coc core arith sets.
Qed.

Hint Resolve red_lift: coc.

Lemma par_red_red : forall M N, par_red M N -> red M N.
Proof.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.
  apply trans_red with (App (Abs T M') N'); auto with coc core arith sets.

  intros.
  apply trans_red_red with on_zero; auto with coc core arith sets.

  intros.
  apply trans_red_red with (App on_succ num); auto with coc core arith sets.

  intros.
  apply trans_red_red with on_zero; auto with coc core arith sets.

  intros.
  apply trans_red_red with (App on_succ num); auto with coc core arith sets.

  intros.
  apply trans_red_red with on_zero; auto with coc core arith sets.

  intros.
  apply trans_red_red with (App (App on_succ num) (NatRec choice on_zero on_succ num)); auto with coc core arith sets.

  intros.
  apply trans_red_red with on_zero; auto with coc core arith sets.

  intros.
  apply trans_red_red with (App (App on_succ num) (NatInd choice on_zero on_succ num)); auto with coc core arith sets.  

  apply trans_red_red with (
    App
    (App f val_a)
    (
      Abs type_a (
        Abs (App (App (lift 1 rel_a) (Ref 0)) (lift 1 val_a)) (
          AccRec
          (lift 2 type_a)
          (lift 2 rel_a)
          (lift 2 choice)
          (lift 2 f)
          (Ref 1)
          (App (App (lift 2 proof) (Ref 1)) (Ref 0))
        )
      )
    )
  ); auto with coc core arith sets.
  unfold lift; auto 11 with coc core arith sets.

  apply trans_red_red with (
    App
    (App f val_a)
    (
      Abs type_a (
        Abs (App (App (lift 1 rel_a) (Ref 0)) (lift 1 val_a)) (
          AccInd
          (lift 2 type_a)
          (lift 2 rel_a)
          (lift 2 choice)
          (lift 2 f)
          (Ref 1)
          (App (App (lift 2 proof) (Ref 1)) (Ref 0))
        )
      )
    )
  ); auto with coc core arith sets.
  unfold lift; auto 11 with coc core arith sets.

  apply trans_red_red with on_le_n; auto with coc core arith sets.

  apply trans_red_red with (App (App on_le_s r_b) proof); auto with coc core arith sets.

  apply trans_red_red with on_le_n; auto with coc core arith sets.
  
  apply trans_red_red with (
    App (
      App (App on_le_s r_b) proof 
    )
    (
      LeInd choice on_le_n on_le_s l_b r_b proof
    )
  ); auto with coc core arith sets.

  apply trans_red_red with on_true; auto with coc core arith sets.

  apply trans_red_red with on_false; auto with coc core arith sets.

  apply trans_red_red with on_true; auto with coc core arith sets.

  apply trans_red_red with on_false; auto with coc core arith sets.

  apply trans_red_red with (App on_left proof); auto with coc core arith sets.

  apply trans_red_red with (App on_right proof); auto with coc core arith sets.

  apply trans_red_red with (App on_left proof); auto with coc core arith sets.

  apply trans_red_red with (App on_right proof); auto with coc core arith sets.

  apply trans_red_red with val; auto with coc core arith sets.

  apply trans_red_red with proof; auto with coc core arith sets.

  apply trans_red_red with impl; auto with coc core arith sets.

  apply trans_red_red with impl; auto with coc core arith sets.

  apply trans_red_red with (
    Abs type 
    (
      AccRec 
      (lift 1 type)
      (lift 1 rel)
      (lift 1 choice)
      (
        Abs (lift 1 type) (
          Abs (
            Prod (lift 2 type)
            (
              Prod (App (App (lift 3 rel) (Ref 0)) (Ref 1))
              (App (lift 4 choice) (Ref 1))
            )
          ) (
            App (App (lift 3 f) (Ref 1))
            (
              Abs (
                Refine
                (lift 3 type)
                (App (App (lift 3 rel) (Ref 0)) (Ref 2))
              )
              (
                App (App (Ref 1) (RefineProjVal (Ref 0))) (RefineProjProof (Ref 0)) 
              )
            )
          )  
        )
      )
      (Ref 0)
      (App (lift 1 proof) (Ref 0))
    )
  ); auto with coc core arith sets.
  unfold lift; auto 11 with coc core arith sets.

  apply trans_red_red with on_true; auto with coc.

  apply trans_red_red with on_false; auto with coc.
  
  intros.
  apply trans_red_red with y; auto with coc core arith sets.
Qed.

Hint Resolve red_par_red par_red_red: coc.


Lemma par_red1_lift :
  forall n (a b : term),
  par_red1 a b -> forall k, par_red1 (lift_rec n a k) (lift_rec n b k)
.
Proof.
  simple induction 1; simpl in |- *; auto with coc core arith sets.
  intros.
  rewrite distr_lift_subst; auto with coc core arith sets.

  intros.
  change (S (S k)) with (2 + k).
  unfold lift.
  repeat rewrite <- permute_lift_rec by auto with coc core arith sets.
  apply acc_rec_exec_par; auto with coc core arith sets.

  intros.
  change (S (S k)) with (2 + k).
  unfold lift.
  repeat rewrite <- permute_lift_rec by auto with coc core arith sets.
  apply acc_ind_exec_par; auto with coc core arith sets.

  intros.
  change (S (S (S (S k)))) with (4 + k).
  change (S (S (S k))) with (3 + k).
  change (S (S k)) with (2 + k).
  unfold lift.
  repeat rewrite <- permute_lift_rec by auto with coc core arith sets.
  apply wf_rec_expand_par; auto with coc core arith sets.
Qed.


Lemma par_red1_subst :
  forall c d : term,
  par_red1 c d ->
  forall a b : term,
  par_red1 a b -> forall k, par_red1 (subst_rec a c k) (subst_rec b d k)
.
Proof.
  simple induction 1; simpl in |- *; auto with coc core arith sets; intros.
  rewrite distr_subst; auto with coc core arith sets.

  elim (lt_eq_lt_dec k n); auto with coc core arith sets; intro a0.
  elim a0; intros; auto with coc core arith sets.
  unfold lift in |- *.
  apply par_red1_lift; auto with coc core arith sets.

  change (S (S k)) with (2 + k).
  unfold lift.
  repeat rewrite <- commut_lift_subst_rec by auto with coc core arith sets.
  apply acc_rec_exec_par; auto with coc core arith sets.

  change (S (S k)) with (2 + k).
  unfold lift.
  repeat rewrite <- commut_lift_subst_rec by auto with coc core arith sets.
  apply acc_ind_exec_par; auto with coc core arith sets.

  change (S (S (S (S k)))) with (4 + k).
  change (S (S (S k))) with (3 + k).
  change (S (S k)) with (2 + k).
  unfold lift.
  repeat rewrite <- commut_lift_subst_rec by auto with coc core arith sets.
  apply wf_rec_expand_par; auto with coc core arith sets.
Qed.

Lemma inv_par_red_abs :
  forall (P : Prop) T (U x : term),
  par_red1 (Abs T U) x ->
  (forall T' (U' : term), x = Abs T' U' -> par_red1 U U' -> P) -> P
.
Proof.
  do 5 intro.
  inversion_clear H; intros.
  apply H with T' M'; auto with coc core arith sets.
Qed.

Hint Resolve par_red1_lift par_red1_subst: coc.



Lemma subterm_abs : forall t (m : term), subterm m (Abs t m).
Proof.
  intros.
  apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

Lemma subterm_prod : forall t (m : term), subterm m (Prod t m).
Proof.
  intros.
  apply Sbtrm_bind with t; auto with coc core arith sets.
Qed.

Hint Resolve subterm_abs subterm_prod: coc.



(* Inversion for `mem_sort` for lifting *)
Lemma mem_sort_lift :
  forall t n k s, mem_sort s (lift_rec n t k) -> mem_sort s t
.
Proof.
  simple induction t; simpl in |- *; intros; auto with coc core arith sets.
  generalize H; elim (le_gt_dec k n); intros; auto with coc core arith sets.
  inversion_clear H0.

  inversion_clear H1.
  apply mem_abs_l; apply H with n k; auto with coc core arith sets.

  apply mem_abs_r; apply H0 with n (S k); auto with coc core arith sets.

  inversion_clear H1.
  apply mem_app_l; apply H with n k; auto with coc core arith sets.

  apply mem_app_r; apply H0 with n k; auto with coc core arith sets.

  inversion_clear H1.
  apply mem_prod_l; apply H with n k; auto with coc core arith sets.

  apply mem_prod_r; apply H0 with n (S k); auto with coc core arith sets.

  inversion_clear H0.
  apply mem_nat_succ; apply H with n k; auto with coc core arith sets.

  inversion_clear H3.
  apply mem_nat_destruct_choice; apply H with n k; auto with coc core arith sets.
  apply mem_nat_destruct_on_zero; apply H0 with n k; auto with coc core arith sets.
  apply mem_nat_destruct_on_succ; apply H1 with n k; auto with coc core arith sets.
  apply mem_nat_destruct_num; apply H2 with n k; auto with coc core arith sets.

  inversion_clear H3.
  apply mem_nat_cases_choice; apply H with n k; auto with coc core arith sets.
  apply mem_nat_cases_on_zero; apply H0 with n k; auto with coc core arith sets.
  apply mem_nat_cases_on_succ; apply H1 with n k; auto with coc core arith sets.
  apply mem_nat_cases_num; apply H2 with n k; auto with coc core arith sets.

  inversion_clear H3.
  apply mem_nat_rec_choice; apply H with n k; auto with coc core arith sets.
  apply mem_nat_rec_on_zero; apply H0 with n k; auto with coc core arith sets.
  apply mem_nat_rec_on_succ; apply H1 with n k; auto with coc core arith sets.
  apply mem_nat_rec_num; apply H2 with n k; auto with coc core arith sets.

  inversion_clear H3.
  apply mem_nat_ind_choice; apply H with n k; auto with coc core arith sets.
  apply mem_nat_ind_on_zero; apply H0 with n k; auto with coc core arith sets.
  apply mem_nat_ind_on_succ; apply H1 with n k; auto with coc core arith sets.
  apply mem_nat_ind_num; apply H2 with n k; auto with coc core arith sets.

  inversion_clear H2.
  apply mem_acc_prop_type; apply H with n k; auto with coc core arith sets.
  apply mem_acc_prop_rel; apply H0 with n k; auto with coc core arith sets.
  apply mem_acc_prop_val; apply H1 with n k; auto with coc core arith sets.

  inversion_clear H3.
  apply mem_acc_intro_type; apply H with n k; auto with coc core arith sets.
  apply mem_acc_intro_rel; apply H0 with n k; auto with coc core arith sets.
  apply mem_acc_intro_val; apply H1 with n k; auto with coc core arith sets.
  apply mem_acc_intro_proof; apply H2 with n k; auto with coc core arith sets.

  inversion_clear H5.
  apply mem_acc_rec_type; apply H with n k; auto with coc core arith sets.
  apply mem_acc_rec_rel; apply H0 with n k; auto with coc core arith sets.
  apply mem_acc_rec_choice; apply H1 with n k; auto with coc core arith sets.
  apply mem_acc_rec_f; apply H2 with n k; auto with coc core arith sets.
  apply mem_acc_rec_val; apply H3 with n k; auto with coc core arith sets.
  apply mem_acc_rec_proof; apply H4 with n k; auto with coc core arith sets.

  inversion_clear H5.
  apply mem_acc_ind_type; apply H with n k; auto with coc core arith sets.
  apply mem_acc_ind_rel; apply H0 with n k; auto with coc core arith sets.
  apply mem_acc_ind_choice; apply H1 with n k; auto with coc core arith sets.
  apply mem_acc_ind_f; apply H2 with n k; auto with coc core arith sets.
  apply mem_acc_ind_val; apply H3 with n k; auto with coc core arith sets.
  apply mem_acc_ind_proof; apply H4 with n k; auto with coc core arith sets.

  inversion_clear H1.
  apply mem_le_prop_l; apply H with n k; auto with coc core arith sets.
  apply mem_le_prop_r; apply H0 with n k; auto with coc core arith sets.

  inversion_clear H0.
  apply mem_le_n_n; apply H with n k; auto with coc core arith sets.

  inversion_clear H2.
  apply mem_le_s_l; apply H with n k; auto with coc core arith sets.
  apply mem_le_s_r; apply H0 with n k; auto with coc core arith sets.
  apply mem_le_s_proof; apply H1 with n k; auto with coc core arith sets.

  inversion_clear H5.
  apply mem_le_cases_choice; apply H with n k; auto with coc core arith sets.
  apply mem_le_cases_on_le_n; apply H0 with n k; auto with coc core arith sets.
  apply mem_le_cases_on_le_s; apply H1 with n k; auto with coc core arith sets.
  apply mem_le_cases_l; apply H2 with n k; auto with coc core arith sets.
  apply mem_le_cases_r; apply H3 with n k; auto with coc core arith sets.
  apply mem_le_cases_proof; apply H4 with n k; auto with coc core arith sets.

  inversion_clear H5.
  apply mem_le_ind_choice; apply H with n k; auto with coc core arith sets.
  apply mem_le_ind_on_le_n; apply H0 with n k; auto with coc core arith sets.
  apply mem_le_ind_on_le_s; apply H1 with n k; auto with coc core arith sets.
  apply mem_le_ind_l; apply H2 with n k; auto with coc core arith sets.
  apply mem_le_ind_r; apply H3 with n k; auto with coc core arith sets.
  apply mem_le_ind_proof; apply H4 with n k; auto with coc core arith sets.

  inversion_clear H1.
  apply mem_sumbool_type_left_pred; apply H with n k; auto with coc core arith sets.
  apply mem_sumbool_type_right_pred; apply H0 with n k; auto with coc core arith sets.

  inversion_clear H2.
  apply mem_sumbool_left_left_pred; apply H with n k; auto with coc core arith sets.
  apply mem_sumbool_left_right_pred; apply H0 with n k; auto with coc core arith sets.
  apply mem_sumbool_left_proof; apply H1 with n k; auto with coc core arith sets.

  inversion_clear H2.
  apply mem_sumbool_right_left_pred; apply H with n k; auto with coc core arith sets.
  apply mem_sumbool_right_right_pred; apply H0 with n k; auto with coc core arith sets.
  apply mem_sumbool_right_proof; apply H1 with n k; auto with coc core arith sets.

  inversion_clear H3.
  apply mem_bool_ind_choice; apply H with n k; auto with coc core arith sets.
  apply mem_bool_ind_on_true; apply H0 with n k; auto with coc core arith sets.
  apply mem_bool_ind_on_false; apply H1 with n k; auto with coc core arith sets.
  apply mem_bool_ind_proof; apply H2 with n k; auto with coc core arith sets.

  inversion_clear H3.
  apply mem_bool_rec_choice; apply H with n k; auto with coc core arith sets.
  apply mem_bool_rec_on_true; apply H0 with n k; auto with coc core arith sets.
  apply mem_bool_rec_on_false; apply H1 with n k; auto with coc core arith sets.
  apply mem_bool_rec_proof; apply H2 with n k; auto with coc core arith sets.

  inversion_clear H5.
  apply mem_sumbool_ind_left_pred; apply H with n k; auto with coc core arith sets.
  apply mem_sumbool_ind_right_pred; apply H0 with n k; auto with coc core arith sets.
  apply mem_sumbool_ind_choice; apply H1 with n k; auto with coc core arith sets.
  apply mem_sumbool_ind_on_true; apply H2 with n k; auto with coc core arith sets.
  apply mem_sumbool_ind_on_false; apply H3 with n k; auto with coc core arith sets.
  apply mem_sumbool_ind_bool; apply H4 with n k; auto with coc core arith sets.

  inversion_clear H5.
  apply mem_sumbool_rec_left_pred; apply H with n k; auto with coc core arith sets.
  apply mem_sumbool_rec_right_pred; apply H0 with n k; auto with coc core arith sets.
  apply mem_sumbool_rec_choice; apply H1 with n k; auto with coc core arith sets.
  apply mem_sumbool_rec_on_true; apply H2 with n k; auto with coc core arith sets.
  apply mem_sumbool_rec_on_false; apply H3 with n k; auto with coc core arith sets.
  apply mem_sumbool_rec_bool; apply H4 with n k; auto with coc core arith sets.

  inversion_clear H1.
  apply mem_refine_type; apply H with n k; auto with coc core arith sets.
  apply mem_refine_property; apply H0 with n k; auto with coc core arith sets.

  inversion_clear H3.
  apply mem_refine_constr_type; apply H with n k; auto with coc core arith sets.
  apply mem_refine_constr_property; apply H0 with n k; auto with coc core arith sets.
  apply mem_refine_constr_val; apply H1 with n k; auto with coc core arith sets.
  apply mem_refine_constr_proof; apply H2 with n k; auto with coc core arith sets.

  inversion_clear H0.
  apply mem_refine_proj_val; apply H with n k; auto with coc core arith sets.

  inversion_clear H0.
  apply mem_refine_proj_proof; apply H with n k; auto with coc core arith sets.

  inversion_clear H2.
  apply mem_eq_prop_type; apply H with n k; auto with coc core arith sets.
  apply mem_eq_prop_l; apply H0 with n k; auto with coc core arith sets.
  apply mem_eq_prop_r; apply H1 with n k; auto with coc core arith sets.

  inversion_clear H1.
  apply mem_eq_refl_type; apply H with n k; auto with coc core arith sets.
  apply mem_eq_refl_val; apply H0 with n k; auto with coc core arith sets.

  inversion_clear H5.
  apply mem_eq_ind_type; apply H with n k; auto with coc core arith sets.
  apply mem_eq_ind_l; apply H0 with n k; auto with coc core arith sets.
  apply mem_eq_ind_r; apply H1 with n k; auto with coc core arith sets.
  apply mem_eq_ind_property; apply H2 with n k; auto with coc core arith sets.
  apply mem_eq_ind_impl; apply H3 with n k; auto with coc core arith sets.
  apply mem_eq_ind_proof; apply H4 with n k; auto with coc core arith sets.

  inversion_clear H5.
  apply mem_eq_rec_type; apply H with n k; auto with coc core arith sets.
  apply mem_eq_rec_l; apply H0 with n k; auto with coc core arith sets.
  apply mem_eq_rec_r; apply H1 with n k; auto with coc core arith sets.
  apply mem_eq_rec_property; apply H2 with n k; auto with coc core arith sets.
  apply mem_eq_rec_impl; apply H3 with n k; auto with coc core arith sets.
  apply mem_eq_rec_proof; apply H4 with n k; auto with coc core arith sets.

  inversion_clear H1.
  apply mem_false_ind_proof; apply H with n k; auto with coc core arith sets.
  apply mem_false_ind_property; apply H0 with n k; auto with coc core arith sets.

  inversion_clear H1.
  apply mem_false_rec_proof; apply H with n k; auto with coc core arith sets.
  apply mem_false_rec_property; apply H0 with n k; auto with coc core arith sets.

  inversion_clear H4.
  apply mem_WFrec_type; apply H with n k; auto with coc core arith sets.
  apply mem_WFrec_rel; apply H0 with n k; auto with coc core arith sets.
  apply mem_WFrec_choice; apply H1 with n k; auto with coc core arith sets.
  apply mem_WFrec_f; apply H2 with n k; auto with coc core arith sets.
  apply mem_WFrec_proof; apply H3 with n k; auto with coc core arith sets.

  inversion_clear H2.
  apply mem_bool_prop_choice_on_true; apply H with n k; auto with coc.
  apply mem_bool_prop_choice_on_false; apply H0 with n k; auto with coc.
  apply mem_bool_prop_choice_val; apply H1 with n k; auto with coc.
Qed.

(* Inversion of `mem_sort` for substitution *)
Lemma mem_sort_subst :
  forall (b a : term) n s,
  mem_sort s (subst_rec a b n) -> mem_sort s a \/ mem_sort s b
.
Proof.
  simple induction b; simpl in |- *; intros; auto with coc core arith sets.

  generalize H; elim (lt_eq_lt_dec n0 n); [ intro a0 | intro b0 ].
  elim a0; intros.
  inversion_clear H0.

  left.
  apply mem_sort_lift with n0 0; auto with coc core arith sets.

  intros.
  inversion_clear H0.

  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.

  elim H0 with a (S n) s; auto with coc core arith sets.

  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.

  elim H0 with a n s; auto with coc core arith sets.

  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.

  elim H0 with a (S n) s; intros; auto with coc core arith sets.

  inversion_clear H0.
  elim H with a n s; auto with coc core arith sets.

  inversion_clear H3.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.

  inversion_clear H3.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.

  inversion_clear H3.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.

  inversion_clear H3.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.

  inversion_clear H2.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.

  inversion_clear H3.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.

  inversion_clear H5.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.
  elim H3 with a n s; auto with coc core arith sets.
  elim H4 with a n s; auto with coc core arith sets.

  inversion_clear H5.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.
  elim H3 with a n s; auto with coc core arith sets.
  elim H4 with a n s; auto with coc core arith sets.

  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.

  inversion_clear H0.
  elim H with a n s; auto with coc core arith sets.

  inversion_clear H2.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.

  inversion_clear H5.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.
  elim H3 with a n s; auto with coc core arith sets.
  elim H4 with a n s; auto with coc core arith sets.

  inversion_clear H5.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.
  elim H3 with a n s; auto with coc core arith sets.
  elim H4 with a n s; auto with coc core arith sets.

  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.

  inversion_clear H2.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.

  inversion_clear H2.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.

  inversion_clear H3.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.

  inversion_clear H3.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.

  inversion_clear H5.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.
  elim H3 with a n s; auto with coc core arith sets.
  elim H4 with a n s; auto with coc core arith sets.

  inversion_clear H5.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.
  elim H3 with a n s; auto with coc core arith sets.
  elim H4 with a n s; auto with coc core arith sets.

  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.

  inversion_clear H3.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.

  inversion_clear H0.
  elim H with a n s; auto with coc core arith sets.

  inversion_clear H0.
  elim H with a n s; auto with coc core arith sets.

  inversion_clear H2.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.

  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.

  inversion_clear H5.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.
  elim H3 with a n s; auto with coc core arith sets.
  elim H4 with a n s; auto with coc core arith sets.

  inversion_clear H5.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.
  elim H3 with a n s; auto with coc core arith sets.
  elim H4 with a n s; auto with coc core arith sets.

  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.

  inversion_clear H1.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.

  inversion_clear H4.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
  elim H2 with a n s; auto with coc core arith sets.
  elim H3 with a n s; auto with coc core arith sets.

  inversion_clear H2.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.
Qed.

Hint Resolve mem_sort_lift mem_sort_subst : coc.

(* Reduction doesn't remove the sort from our term *)
Lemma red_sort_mem : forall t s, red t (Srt s) -> mem_sort s t.
Proof.
  intros.
  pattern t in |- *.
  apply red1_red_ind with (Srt s); auto with coc core arith sets.
  do 4 intro.
  elim H0; intros; try (solve [inversion_clear H4; auto with coc core arith sets]); try (solve [inversion_clear H2; auto with coc core arith sets]).
  elim mem_sort_subst with M0 N 0 s; intros; auto with coc core arith sets.

  inversion_clear H2.
  inversion_clear H3; auto with coc core arith sets.
  inversion_clear H3; auto with coc core arith sets.

  inversion_clear H2.
  inversion_clear H3; auto with coc core arith sets.
  inversion_clear H3; auto with coc core arith sets.

  inversion_clear H2.
  inversion_clear H3; auto with coc core arith sets.
  inversion_clear H3; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H2.
  apply mem_sort_lift in H3; auto with coc core arith sets.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H2.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H3.

  inversion_clear H2.
  inversion_clear H3; auto with coc core arith sets.
  inversion_clear H3; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H2.
  apply mem_sort_lift in H3; auto with coc core arith sets.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H2.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H3.

  inversion_clear H2; auto with coc core arith sets.
  inversion_clear H3; auto with coc core arith sets.

  inversion_clear H2.
  inversion_clear H3; auto with coc core arith sets.
  inversion_clear H2; auto with coc core arith sets.
  inversion_clear H3; auto with coc core arith sets.

  inversion_clear H2; auto with coc core arith sets.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  apply mem_sort_lift in H3; auto with coc core arith sets.
  inversion_clear H3.
  inversion_clear H2.
  apply mem_sort_lift in H3; auto with coc core arith sets.
  inversion_clear H3.
  inversion_clear H2.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H2.
  apply mem_sort_lift in H3; auto with coc core arith sets.
  inversion_clear H3.
  inversion_clear H2.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H2.
  apply mem_sort_lift in H3; auto with coc core arith sets.
  inversion_clear H3.
  inversion_clear H2.
  apply mem_sort_lift in H3; auto with coc core arith sets.
  inversion_clear H3.
  inversion_clear H2.
  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H2.
  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H3.
  inversion_clear H2.
  inversion_clear H2.
  inversion_clear H2.
  apply mem_sort_lift in H3; auto with coc core arith sets.
  inversion_clear H3.
Qed.



(* A term which the normal form reduces to is the normal form itself *)
Lemma red_normal : forall u v, red u v -> normal u -> u = v.
Proof.
  simple induction 1; auto with coc core arith sets; intros.
  absurd (red1 u N); auto with coc core arith sets.
  absurd (red1 P N); auto with coc core arith sets.
  elim (H1 H3).
  unfold not in |- *; intro; apply (H3 N); auto with coc core arith sets.
Qed.



(* Reduction preserves strong normalization *)
Lemma sn_red_sn : forall a b : term, sn a -> red a b -> sn b.
Proof.
  unfold sn in |- *.
  simple induction 2; intros; auto with coc core arith sets.
  apply Acc_inv with P; auto with coc core arith sets.
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
  exists (Abs t z); auto with coc core arith sets.

  exists (Prod t z); auto with coc core arith sets.

  inversion_clear H0.
  exists (Abs z n); auto with coc core arith sets.

  exists (App z v); auto with coc core arith sets.

  exists (App u z); auto with coc core arith sets.

  exists (Prod z n); auto with coc core arith sets.

  exists (NatDestruct z a2 a3 a4); auto with coc core arith sets.

  exists (NatDestruct a1 z a3 a4); auto with coc core arith sets.

  exists (NatDestruct a1 a2 z a4); auto with coc core arith sets.

  exists (NatDestruct a1 a2 a3 z); auto with coc core arith sets.

  exists (NatCases z a2 a3 a4); auto with coc core arith sets.

  exists (NatCases a1 z a3 a4); auto with coc core arith sets.

  exists (NatCases a1 a2 z a4); auto with coc core arith sets.
  
  exists (NatCases a1 a2 a3 z); auto with coc core arith sets.

  exists (NatSucc z); auto with coc core arith sets.

  exists (NatRec z a2 a3 a4); auto with coc core arith sets.

  exists (NatRec a1 z a3 a4); auto with coc core arith sets.

  exists (NatRec a1 a2 z a4); auto with coc core arith sets.

  exists (NatRec a1 a2 a3 z); auto with coc core arith sets.

  exists (NatInd z a2 a3 a4); auto with coc core arith sets.

  exists (NatInd a1 z a3 a4); auto with coc core arith sets.

  exists (NatInd a1 a2 z a4); auto with coc core arith sets.
  
  exists (NatInd a1 a2 a3 z); auto with coc core arith sets.

  exists (AccProp z a2 a3); auto with coc core arith sets.

  exists (AccProp a1 z a3); auto with coc core arith sets.

  exists (AccProp a1 a2 z); auto with coc core arith sets.

  exists (AccIntro z a2 a3 a4); auto with coc core arith sets.

  exists (AccIntro a1 z a3 a4); auto with coc core arith sets.

  exists (AccIntro a1 a2 z a4); auto with coc core arith sets.

  exists (AccIntro a1 a2 a3 z); auto with coc core arith sets.

  exists (AccRec z a2 a3 a4 a5 a6); auto with coc core arith sets.

  exists (AccRec a1 z a3 a4 a5 a6); auto with coc core arith sets.

  exists (AccRec a1 a2 z a4 a5 a6); auto with coc core arith sets.

  exists (AccRec a1 a2 a3 z a5 a6); auto with coc core arith sets.

  exists (AccRec a1 a2 a3 a4 z a6); auto with coc core arith sets.

  exists (AccRec a1 a2 a3 a4 a5 z); auto with coc core arith sets.

  exists (AccInd z a2 a3 a4 a5 a6); auto with coc core arith sets.

  exists (AccInd a1 z a3 a4 a5 a6); auto with coc core arith sets.

  exists (AccInd a1 a2 z a4 a5 a6); auto with coc core arith sets.

  exists (AccInd a1 a2 a3 z a5 a6); auto with coc core arith sets.

  exists (AccInd a1 a2 a3 a4 z a6); auto with coc core arith sets.

  exists (AccInd a1 a2 a3 a4 a5 z); auto with coc core arith sets.

  exists (Le z a2); auto with coc core arith sets.

  exists (Le a1 z); auto with coc core arith sets.

  exists (LeN z); auto with coc core arith sets.

  exists (LeS z a2 a3); auto with coc core arith sets.

  exists (LeS a1 z a3); auto with coc core arith sets.

  exists (LeS a1 a2 z); auto with coc core arith sets.

  exists (LeCases z a2 a3 a4 a5 a6); auto with coc core arith sets.

  exists (LeCases a1 z a3 a4 a5 a6); auto with coc core arith sets.

  exists (LeCases a1 a2 z a4 a5 a6); auto with coc core arith sets.

  exists (LeCases a1 a2 a3 z a5 a6); auto with coc core arith sets.

  exists (LeCases a1 a2 a3 a4 z a6); auto with coc core arith sets.

  exists (LeCases a1 a2 a3 a4 a5 z); auto with coc core arith sets.

  exists (LeInd z a2 a3 a4 a5 a6); auto with coc core arith sets.

  exists (LeInd a1 z a3 a4 a5 a6); auto with coc core arith sets.

  exists (LeInd a1 a2 z a4 a5 a6); auto with coc core arith sets.

  exists (LeInd a1 a2 a3 z a5 a6); auto with coc core arith sets.

  exists (LeInd a1 a2 a3 a4 z a6); auto with coc core arith sets.

  exists (LeInd a1 a2 a3 a4 a5 z); auto with coc core arith sets.

  exists (SumBool z a2); auto with coc core arith sets.

  exists (SumBool a1 z); auto with coc core arith sets.

  exists (SumBoolLeft z a2 a3); auto with coc core arith sets.

  exists (SumBoolLeft a1 z a3); auto with coc core arith sets.

  exists (SumBoolLeft a1 a2 z); auto with coc core arith sets.

  exists (SumBoolRight z a2 a3); auto with coc core arith sets.

  exists (SumBoolRight a1 z a3); auto with coc core arith sets.

  exists (SumBoolRight a1 a2 z); auto with coc core arith sets.

  exists (BoolInd z a2 a3 a4); auto with coc core arith sets.

  exists (BoolInd a1 z a3 a4); auto with coc core arith sets.

  exists (BoolInd a1 a2 z a4); auto with coc core arith sets.

  exists (BoolInd a1 a2 a3 z); auto with coc core arith sets.

  exists (BoolRec z a2 a3 a4); auto with coc core arith sets.

  exists (BoolRec a1 z a3 a4); auto with coc core arith sets.

  exists (BoolRec a1 a2 z a4); auto with coc core arith sets.

  exists (BoolRec a1 a2 a3 z); auto with coc core arith sets.

  exists (SumBoolInd z a2 a3 a4 a5 a6); auto with coc core arith sets.

  exists (SumBoolInd a1 z a3 a4 a5 a6); auto with coc core arith sets.

  exists (SumBoolInd a1 a2 z a4 a5 a6); auto with coc core arith sets.

  exists (SumBoolInd a1 a2 a3 z a5 a6); auto with coc core arith sets.

  exists (SumBoolInd a1 a2 a3 a4 z a6); auto with coc core arith sets.

  exists (SumBoolInd a1 a2 a3 a4 a5 z); auto with coc core arith sets.

  exists (SumBoolRec z a2 a3 a4 a5 a6); auto with coc core arith sets.

  exists (SumBoolRec a1 z a3 a4 a5 a6); auto with coc core arith sets.

  exists (SumBoolRec a1 a2 z a4 a5 a6); auto with coc core arith sets.

  exists (SumBoolRec a1 a2 a3 z a5 a6); auto with coc core arith sets.

  exists (SumBoolRec a1 a2 a3 a4 z a6); auto with coc core arith sets.

  exists (SumBoolRec a1 a2 a3 a4 a5 z); auto with coc core arith sets.

  exists (Refine z a2); auto with coc core arith sets.

  exists (Refine a1 z); auto with coc core arith sets.

  exists (RefineConstr z a2 a3 a4); auto with coc core arith sets.

  exists (RefineConstr a1 z a3 a4); auto with coc core arith sets.

  exists (RefineConstr a1 a2 z a4); auto with coc core arith sets.

  exists (RefineConstr a1 a2 a3 z); auto with coc core arith sets.

  exists (RefineProjVal z); auto with coc core arith sets.

  exists (RefineProjProof z); auto with coc core arith sets.

  exists (Eq z a2 a3); auto with coc core arith sets.

  exists (Eq a1 z a3); auto with coc core arith sets.

  exists (Eq a1 a2 z); auto with coc core arith sets.

  exists (EqRefl z a2); auto with coc core arith sets.

  exists (EqRefl a1 z); auto with coc core arith sets.

  exists (EqInd z a2 a3 a4 a5 a6); auto with coc core arith sets.

  exists (EqInd a1 z a3 a4 a5 a6); auto with coc core arith sets.

  exists (EqInd a1 a2 z a4 a5 a6); auto with coc core arith sets.

  exists (EqInd a1 a2 a3 z a5 a6); auto with coc core arith sets.

  exists (EqInd a1 a2 a3 a4 z a6); auto with coc core arith sets.

  exists (EqInd a1 a2 a3 a4 a5 z); auto with coc core arith sets.

  exists (EqRec z a2 a3 a4 a5 a6); auto with coc core arith sets.

  exists (EqRec a1 z a3 a4 a5 a6); auto with coc core arith sets.

  exists (EqRec a1 a2 z a4 a5 a6); auto with coc core arith sets.

  exists (EqRec a1 a2 a3 z a5 a6); auto with coc core arith sets.

  exists (EqRec a1 a2 a3 a4 z a6); auto with coc core arith sets.

  exists (EqRec a1 a2 a3 a4 a5 z); auto with coc core arith sets.

  exists (FalseInd z a2); auto with coc core arith sets.

  exists (FalseInd a1 z); auto with coc core arith sets.

  exists (FalseRec z a2); auto with coc core arith sets.

  exists (FalseRec a1 z); auto with coc core arith sets.

  exists (WFrec z a2 a3 a4 a5); auto with coc core arith sets.

  exists (WFrec a1 z a3 a4 a5); auto with coc core arith sets.

  exists (WFrec a1 a2 z a4 a5); auto with coc core arith sets.

  exists (WFrec a1 a2 a3 z a5); auto with coc core arith sets.

  exists (WFrec a1 a2 a3 a4 z); auto with coc core arith sets.

  exists (BoolPropChoice z a2 a3); auto with coc core arith sets.

  exists (BoolPropChoice a1 z a3); auto with coc core arith sets.

  exists (BoolPropChoice a1 a2 z); auto with coc core arith sets.
Qed.


(* Subterm of a strongly normalizing term is strongly normalizing *)
Lemma subterm_sn :
  forall a : term, sn a -> forall b : term, subterm b a -> sn b.
Proof.
unfold sn in |- *.
  simple induction 1; intros.
  apply Acc_intro; intros.
  elim commut_red1_subterm with x b y; intros; auto with coc core arith sets.
  apply H1 with x0; auto with coc core arith sets.
Qed.


(* product of strongly normalizing terms is strongly normalizing *)
Lemma sn_prod : forall A, sn A -> forall B, sn B -> sn (Prod A B).
Proof.
  unfold sn in |- *.
  simple induction 1.
  simple induction 3; intros.
  apply Acc_intro; intros.
  inversion_clear H5; auto with coc core arith sets.
  apply H1; auto with coc core arith sets.
  apply Acc_intro; auto with coc core arith sets.
Qed.


(* 
  If the substituition is strongly normalizing then the value we 
  were substituting with is strongly normalizing 
*)
Lemma sn_subst : forall T M, sn (subst T M) -> sn M.
Proof.  
  intros.
  cut (forall t, sn t -> forall m : term, t = subst T m -> sn m).
  intros.
  apply H0 with (subst T M); auto with coc core arith sets.

  unfold sn in |- *.
  simple induction 1; intros.
  apply Acc_intro; intros.
  apply H2 with (subst T y); auto with coc core arith sets.
  rewrite H3.
  unfold subst in |- *; auto with coc core arith sets.
Qed.
*)