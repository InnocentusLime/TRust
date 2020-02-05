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
  Here we show the decidiblity of conversion relation on strongly
  normalizing terms. We abuse our defintiion of a strongly normalizing
  term (an accessible element in order `red1`)
*)

Require Import Peano_dec.
Require Import Transitive_Closure.
Require Import Union.
Require Import Termes.
Require Import Conv.

(* we define the order relation on terms *)
Definition ord_norm1 := union _ subterm (transp _ red1).
Definition ord_norm := clos_trans _ ord_norm1.

Hint Unfold ord_norm1 ord_norm: coc.

(* Subterm implies the order *)
Lemma subterm_ord_norm : forall a b : term, subterm a b -> ord_norm a b.
Proof.
  auto 10 with coc sets.
Qed.

Hint Resolve subterm_ord_norm: coc.


(* One-step reduction with multistep implies the order *)
Lemma red_red1_ord_norm :
  forall a b : term, red a b -> forall c : term, red1 b c -> ord_norm c a
.
Proof.
  red in |- *.
  simple induction 1; intros; auto with coc sets.
  apply t_trans with N; auto with coc sets.
Qed.

(* The subterm relation is well founded *)
Lemma wf_subterm : well_founded subterm.
Proof.
  red in |- *.
  simple induction a; intros; apply Acc_intro; intros.
  inversion_clear H; inversion_clear H0.

  inversion_clear H; inversion_clear H0.

  inversion_clear H1; inversion_clear H2; auto with coc sets.

  inversion_clear H1; inversion_clear H2; auto with coc sets.

  inversion_clear H1; inversion_clear H2; auto with coc sets.

  inversion_clear H; inversion_clear H0.

  inversion_clear H; inversion_clear H0.

  inversion_clear H0; inversion_clear H1; auto with coc sets.
  
  inversion_clear H3.
  inversion_clear H4.
  inversion_clear H4.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H3.
  inversion_clear H4.
  inversion_clear H4.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H3.
  inversion_clear H4.
  inversion_clear H4.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H3.
  inversion_clear H4.
  inversion_clear H4.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H3.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H3.
  inversion_clear H4.
  inversion_clear H4.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H5.
  inversion_clear H6.
  inversion_clear H6.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H5.
  inversion_clear H6.
  inversion_clear H6.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H1.
  inversion_clear H2.
  inversion_clear H2.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H1.
  auto with coc sets.

  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H3.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H5.
  inversion_clear H6.
  inversion_clear H6.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H5.
  inversion_clear H6.
  inversion_clear H6.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H.
  inversion_clear H0.
  inversion_clear H0.

  inversion_clear H1.
  inversion_clear H2.
  inversion_clear H2.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H.
  inversion_clear H0.
  inversion_clear H0.

  inversion_clear H.
  inversion_clear H0.
  inversion_clear H0.

  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H3.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H3.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H3.
  inversion_clear H4.
  inversion_clear H4.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H3.
  inversion_clear H4.
  inversion_clear H4.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H5.
  inversion_clear H6.
  inversion_clear H6.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H5.
  inversion_clear H6.
  inversion_clear H6.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H1.
  inversion_clear H2.
  inversion_clear H2.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H3.
  inversion_clear H4.
  inversion_clear H4.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H3.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H3.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H3.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H1.
  inversion_clear H2.
  inversion_clear H2.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H5.
  inversion_clear H6.
  inversion_clear H6.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H5.
  inversion_clear H6.
  inversion_clear H6.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H.
  inversion_clear H0.
  inversion_clear H0.

  inversion_clear H1.
  inversion_clear H2.
  inversion_clear H2.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H1.
  inversion_clear H2.
  inversion_clear H2.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H.
  inversion_clear H0.
  inversion_clear H0.

  inversion_clear H.
  inversion_clear H0.
  inversion_clear H0.

  inversion_clear H4.
  inversion_clear H5.
  inversion_clear H5.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.

  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H3.
  auto with coc sets.
  auto with coc sets.
  auto with coc sets.
Qed.


(* A strongly normalizing term is accessible in `ord_norm1` *)
Lemma wf_ord_norm1 : forall t : term, sn t -> Acc ord_norm1 t.
Proof.
  unfold ord_norm1 in |- *.
  intros.
  apply Acc_union; auto with coc sets.
  exact commut_red1_subterm.

  intros.
  apply wf_subterm.
Qed.


(* A strongly normalizing term is accessible on `ord_norm` *)
Theorem wf_ord_norm : forall t : term, sn t -> Acc ord_norm t.
Proof.
  unfold ord_norm in |- *.
  intros.
  apply Acc_clos_trans.
  apply wf_ord_norm1; auto with coc sets.
Qed.

(* We store some inverison principles to speed up the complilation *)
Derive Inversion_clear preleminv_red_app with (forall u v x, red1 (App u v) x) Sort Prop.
Definition leminv_red_app u v x (P : term -> term -> term -> Prop) := 
  preleminv_red_app u v x (fun u0 v out => u = u0 -> P u0 v out)
.

Derive Inversion_clear preleminv_red_nat_destruct with (forall choice on_zero on_succ num x, red1 (NatDestruct choice on_zero on_succ num) x) Sort Prop.
Definition leminv_red_nat_destruct choice on_zero on_succ num x (P : term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_nat_destruct choice on_zero on_succ num x (fun choice on_zero on_succ num0 out => num = num0 -> P choice on_zero on_succ num0 out)
.

Derive Inversion_clear preleminv_red_nat_cases with (forall choice on_zero on_succ num x, red1 (NatCases choice on_zero on_succ num) x) Sort Prop.
Definition leminv_red_nat_cases choice on_zero on_succ num x (P : term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_nat_cases choice on_zero on_succ num x (fun choice on_zero on_succ num0 out => num = num0 -> P choice on_zero on_succ num0 out)
.

Derive Inversion_clear preleminv_red_nat_rec with (forall choice on_zero on_succ num x, red1 (NatRec choice on_zero on_succ num) x) Sort Prop.
Definition leminv_red_nat_rec choice on_zero on_succ num x (P : term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_nat_rec choice on_zero on_succ num x (fun choice on_zero on_succ num0 out => num = num0 -> P choice on_zero on_succ num0 out)
.

Derive Inversion_clear preleminv_red_nat_ind with (forall choice on_zero on_succ num x, red1 (NatInd choice on_zero on_succ num) x) Sort Prop.
Definition leminv_red_nat_ind choice on_zero on_succ num x (P : term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_nat_ind choice on_zero on_succ num x (fun choice on_zero on_succ num0 out => num = num0 -> P choice on_zero on_succ num0 out)
.

Derive Inversion_clear preleminv_red_acc_rec with (forall type rel choice f val proof x, red1 (AccRec type rel choice f val proof) x) Sort Prop.
Definition leminv_red_acc_rec type rel choice f val proof x (P : term -> term -> term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_acc_rec type rel choice f val proof x (fun type rel choice f val proof0 out => proof = proof0 -> P type rel choice f val proof0 out)
.

Derive Inversion_clear preleminv_red_acc_ind with (forall type rel choice f val proof x, red1 (AccInd type rel choice f val proof) x) Sort Prop.
Definition leminv_red_acc_ind type rel choice f val proof x (P : term -> term -> term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_acc_ind type rel choice f val proof x (fun type rel choice f val proof0 out => proof = proof0 -> P type rel choice f val proof0 out)
.

Derive Inversion_clear preleminv_red_le_cases with (forall choice on_le_n on_le_s l r proof x, red1 (LeCases choice on_le_n on_le_s l r proof) x) Sort Prop.
Definition leminv_red_le_cases choice on_le_n on_le_s l r proof x (P : term -> term -> term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_le_cases choice on_le_n on_le_s l r proof x (fun choice on_le_n on_le_s l r proof0 out => proof = proof0 -> P choice on_le_n on_le_s l r proof0 out)
.

Derive Inversion_clear preleminv_red_le_ind with (forall choice on_le_n on_le_s l r proof x, red1 (LeInd choice on_le_n on_le_s l r proof) x) Sort Prop.
Definition leminv_red_le_ind choice on_le_n on_le_s l r proof x (P : term -> term -> term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_le_ind choice on_le_n on_le_s l r proof x (fun choice on_le_n on_le_s l r proof0 out => proof = proof0 -> P choice on_le_n on_le_s l r proof0 out)
.

Derive Inversion_clear preleminv_red_bool_ind with (forall choice on_true on_false bool x, red1 (BoolInd choice on_true on_false bool) x) Sort Prop.
Definition leminv_red_bool_ind choice on_true on_false bool x (P : term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_bool_ind choice on_true on_false bool x (fun choice on_true on_false bool0 out => bool = bool0 -> P choice on_true on_false bool0 out)
.

Derive Inversion_clear preleminv_red_bool_rec with (forall choice on_true on_false bool x, red1 (BoolRec choice on_true on_false bool) x) Sort Prop.
Definition leminv_red_bool_rec choice on_true on_false bool x (P : term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_bool_rec choice on_true on_false bool x (fun choice on_true on_false bool0 out => bool = bool0 -> P choice on_true on_false bool0 out)
.

Derive Inversion_clear preleminv_red_sumbool_ind with (forall left right choice on_left on_right val x, red1 (SumBoolInd left right choice on_left on_right val) x) Sort Prop.
Definition leminv_red_sumbool_ind left right choice on_left on_right val x (P : term -> term -> term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_sumbool_ind left right choice on_left on_right val x (fun left right choice on_left on_right val0 out => val = val0 -> P left right choice on_left on_right val0 out)
.

Derive Inversion_clear preleminv_red_sumbool_rec with (forall left right choice on_left on_right val x, red1 (SumBoolRec left right choice on_left on_right val) x) Sort Prop.
Definition leminv_red_sumbool_rec left right choice on_left on_right val x (P : term -> term -> term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_sumbool_rec left right choice on_left on_right val x (fun left right choice on_left on_right val0 out => val = val0 -> P left right choice on_left on_right val0 out)
.

Derive Inversion_clear preleminv_red_refine_proj_val with (forall type property ref x, red1 (RefineProjVal type property ref) x) Sort Prop.
Definition leminv_red_refine_proj_val type property ref x (P : term -> term -> term -> term -> Prop) := 
  preleminv_red_refine_proj_val type property ref x (fun type property ref0 out => ref = ref0 -> P type property ref0 out)
.

Derive Inversion_clear preleminv_red_refine_proj_proof with (forall type property ref x, red1 (RefineProjProof type property ref) x) Sort Prop.
Definition leminv_red_refine_proj_proof type property ref x (P : term -> term -> term -> term -> Prop) := 
  preleminv_red_refine_proj_proof type property ref x (fun type property ref0 out => ref = ref0 -> P type property ref0 out)
.

Derive Inversion_clear preleminv_red_eq_ind with (forall type l r property impl proof x, red1 (EqInd type l r property impl proof) x) Sort Prop.
Definition leminv_red_eq_ind type l r property impl proof x (P : term -> term -> term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_eq_ind type l r property impl proof x (fun type l r property impl proof0 out => proof = proof0 -> P type l r property impl proof0 out)
.

Derive Inversion_clear preleminv_red_eq_rec with (forall type l r property impl proof x, red1 (EqRec type l r property impl proof) x) Sort Prop.
Definition leminv_red_eq_rec type l r property impl proof x (P : term -> term -> term -> term -> term -> term -> term -> Prop) := 
  preleminv_red_eq_rec type l r property impl proof x (fun type l r property impl proof0 out => proof = proof0 -> P type l r property impl proof0 out)
.

Derive Inversion_clear preleminv_red_bool_prop_choice with (forall on_true on_false val x, red1 (BoolPropChoice on_true on_false val) x) Sort Prop.
Definition leminv_red_bool_prop_choice on_true on_false val x (P : term -> term -> term -> term -> Prop) := 
  preleminv_red_bool_prop_choice on_true on_false val x (fun on_true on_false val0 out => val = val0 -> P on_true on_false val0 out)
.

(* 
  Finding a normal form is a decidable problem. We build a
  function which is recursive by a well-founded relation
  called `ord_norm`.

  NOTE:
  Damn I had to do a lot of automation!
*)
Definition compute_nf :
  forall t : term, sn t -> {u : term | red t u & normal u}
.
Proof.
  idtac "compute nf (has 17 trees)".
  intros.
  elimtype (Acc ord_norm t).
  clear H t.
  intros [
    s | n | T t | u v | T U | (**) | (**) | x | choice on_zero on_succ num | 
    choice on_zero on_succ num | choice on_zero on_succ num | choice on_zero on_succ num |
    type rel val | type rel val proof | type rel choice f val proof |
    type rel choice f val proof | l r | n | l r proof | choice on_le_n on_le_s l r proof |
    choice on_le_n on_le_s l r proof | (**) | l r | (**) | (**) | left right proof |
    left right proof | choice on_true on_false bool | choice on_true on_false bool | 
    left right choice on_left on_right val | left right choice on_left on_right val |
    type property | type property val proof | type property ref | type property ref | type l r | type val |
    type l r property impl proof | type l r property impl proof | (**) |
    proof property | proof property | (**) | (**) | type rel choice f proof | on_true on_false val
  ] _ norm_rec.
  
  exists (Srt s); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.

  exists (Ref n); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.

  elim norm_rec with T; auto with coc; intros T' redT nT.
  elim norm_rec with t; auto with coc; intros t' redt nt.
  exists (Abs T' t'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim nT with M'; trivial.
  elim nt with M'; trivial.

  idtac "doing tree [1]".
  elim norm_rec with v; auto with coc; intros v' redv nv.
  elim norm_rec with u; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        App
        ltac:(
          match goal with
          | redu : red u ?r |- _ => exact r
          end
        )
        v'
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (App ?r v') _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_app r v' u0 (fun _ _ _ => False)))
      end; intros;
      solve[discriminate H0] ||
      solve[elim nu with N1; trivial] ||
      solve[elim nv with N2; trivial]
    ]
  );
  idtac "did tree [1]".

  elim norm_rec with (subst v' t).
  intros t' redt nt.
  exists t'; trivial.
  apply trans_red_red with (subst v' t); auto with coc.
  apply trans_red with (App (Abs T t) v'); auto with coc.
  apply red_red1_ord_norm with (App (Abs T t) v'); auto with coc.

  elim norm_rec with T; auto with coc; intros T' redT nT;
  elim norm_rec with U; auto with coc; intros U' redU nU;
  exists (Prod T' U'); auto with coc;
  red in |- *; red in |- *; intros.
  inversion_clear H;
  [>
    elim nT with N1; trivial |
    elim nU with N2; trivial
  ].

  exists Nat; auto with coc.
  intros x H.
  inversion H.

  exists NatO; auto with coc.
  intros x H.
  inversion H.

  elim norm_rec with x; auto with coc; intros x0 red_x_x0 n_x0.
  exists (NatSucc x0); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_x0 with x'; trivial.

  idtac "doing tree [2]".
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with on_zero; auto with coc; intros on_zero' red_on_zero n_on_zero.
  elim norm_rec with on_succ; auto with coc; intros on_succ' red_on_succ n_on_succ.
  elim norm_rec with num; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        NatDestruct choice' on_zero' on_succ'
        ltac:(
          match goal with
          | redu : red num ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (NatDestruct _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_nat_destruct choice' on_zero' on_succ' r u (fun _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_choice with choice'0; trivial |
        elim n_on_zero with on_zero'0; trivial |
        elim n_on_succ with on_succ'0; trivial |
        elim nu with num'; trivial |
        discriminate H0 |
        discriminate H0 | ..
      ]
    ]
  ). 
  idtac "did tree [2]".

  exists on_zero'; auto with coc.
  apply trans_red_red with on_zero; auto with coc. 
  apply trans_red_red with (NatDestruct choice on_zero on_succ NatO); auto with coc.
  
  elim norm_rec with (App on_succ' num_x); intros.
  exists x; trivial.
  apply trans_red_red with (NatDestruct choice on_zero on_succ' (NatSucc num_x)); auto with coc.
  apply trans_red_red with (App on_succ' num_x); auto with coc.
  apply red_red1_ord_norm with (NatDestruct choice on_zero on_succ' (NatSucc num_x)); auto with coc.

  idtac "doing tree [3]".
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with on_zero; auto with coc; intros on_zero' red_on_zero n_on_zero.
  elim norm_rec with on_succ; auto with coc; intros on_succ' red_on_succ n_on_succ.
  elim norm_rec with num; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        NatCases choice' on_zero' on_succ'
        ltac:(
          match goal with
          | redu : red num ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (NatCases _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_nat_cases choice' on_zero' on_succ' r u (fun _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_choice with choice'0; trivial |
        elim n_on_zero with on_zero'0; trivial |
        elim n_on_succ with on_succ'0; trivial |
        elim nu with num'; trivial |
        discriminate H0 |
        discriminate H0 | ..
      ]
    ]
  ). 
  idtac "did tree [3]".

  exists on_zero'; auto with coc.
  apply trans_red_red with on_zero; auto with coc. 
  apply trans_red_red with (NatCases choice on_zero on_succ NatO); auto with coc.
  
  elim norm_rec with (App on_succ' num_x); intros.
  exists x; trivial.
  apply trans_red_red with (NatCases choice on_zero on_succ' (NatSucc num_x)); auto with coc.
  apply trans_red_red with (App on_succ' num_x); auto with coc.
  apply red_red1_ord_norm with (NatCases choice on_zero on_succ' (NatSucc num_x)); auto with coc.

  idtac "doing tree [4]".
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with on_zero; auto with coc; intros on_zero' red_on_zero n_on_zero.
  elim norm_rec with on_succ; auto with coc; intros on_succ' red_on_succ n_on_succ.
  elim norm_rec with num; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        NatRec choice' on_zero' on_succ'
        ltac:(
          match goal with
          | redu : red num ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (NatRec _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_nat_rec choice' on_zero' on_succ' r u (fun _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_choice with choice'0; trivial |
        elim n_on_zero with on_zero'0; trivial |
        elim n_on_succ with on_succ'0; trivial |
        elim nu with num'; trivial |
        discriminate H0 |
        discriminate H0 | ..
      ]
    ]
  ). 
  idtac "did tree [4]".

  exists on_zero'; auto with coc.
  apply trans_red_red with on_zero; auto with coc. 
  apply trans_red_red with (NatRec choice on_zero on_succ NatO); auto with coc.

  elim norm_rec with (App (App on_succ' num_x) (NatRec choice on_zero on_succ' num_x)); intros.
  exists x; trivial.
  apply trans_red_red with (NatRec choice on_zero on_succ' (NatSucc num_x)); auto with coc.
  apply trans_red_red with (App (App on_succ' num_x) (NatRec choice on_zero on_succ' num_x)); auto with coc.
  apply red_red1_ord_norm with (NatRec choice on_zero on_succ' (NatSucc num_x)); auto with coc.

  idtac "doing tree [5]".
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with on_zero; auto with coc; intros on_zero' red_on_zero n_on_zero.
  elim norm_rec with on_succ; auto with coc; intros on_succ' red_on_succ n_on_succ.
  elim norm_rec with num; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        NatInd choice' on_zero' on_succ'
        ltac:(
          match goal with
          | redu : red num ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (NatInd _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_nat_ind choice' on_zero' on_succ' r u (fun _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_choice with choice'0; trivial |
        elim n_on_zero with on_zero'0; trivial |
        elim n_on_succ with on_succ'0; trivial |
        elim nu with num'; trivial |
        discriminate H0 |
        discriminate H0 | ..
      ]
    ]
  ). 
  idtac "did tree [5]".

  exists on_zero'; auto with coc.
  apply trans_red_red with on_zero; auto with coc. 
  apply trans_red_red with (NatInd choice on_zero on_succ NatO); auto with coc.

  elim norm_rec with (App (App on_succ' num_x) (NatInd choice on_zero on_succ' num_x)); intros.
  exists x; trivial.
  apply trans_red_red with (NatInd choice on_zero on_succ' (NatSucc num_x)); auto with coc.
  apply trans_red_red with (App (App on_succ' num_x) (NatInd choice on_zero on_succ' num_x)); auto with coc.
  apply red_red1_ord_norm with (NatInd choice on_zero on_succ' (NatSucc num_x)); auto with coc.

  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with rel; auto with coc; intros rel' red_rel n_rel.
  elim norm_rec with val; auto with coc; intros val' red_val n_val.
  exists (AccProp type' rel' val'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_type with type'0; trivial.
  elim n_rel with rel'0; trivial.
  elim n_val with val'0; trivial.
  
  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with rel; auto with coc; intros rel' red_rel n_rel.
  elim norm_rec with val; auto with coc; intros val' red_val n_val.
  elim norm_rec with proof; auto with coc; intros proof' red_proof n_proof.
  exists (AccIntro type' rel' val' proof'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_type with type'0; trivial.
  elim n_rel with rel'0; trivial.
  elim n_val with val'0; trivial.
  elim n_proof with proof'0; trivial.

  idtac "doing tree [6]".
  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with rel; auto with coc; intros rel' red_rel n_rel.
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with f; auto with coc; intros f' red_f n_f.
  elim norm_rec with val; auto with coc; intros val' red_val n_val.
  elim norm_rec with proof; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        AccRec type' rel' choice' f' val'
        ltac:(
          match goal with
          | redu : red proof ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (AccRec _ _ _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_acc_rec type' rel' choice' f' val' r u (fun _ _ _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_type with type'0; trivial |
        elim n_rel with rel'0; trivial |
        elim n_choice with choice'0; trivial |
        elim n_f with f'0; trivial |
        elim n_val with val'0; trivial |
        elim nu with proof'; trivial |
        discriminate H0 ..
      ]
    ]
  ).
  idtac "did tree [6]".

  elim norm_rec with (
    App
    (App f' val')
    (
      Abs type' (
        Abs (App (App (lift 1 rel') (Ref 0)) (lift 1 val')) (
          AccRec
          (lift 2 type')
          (lift 2 rel')
          (lift 2 choice')
          (lift 2 f')
          (Ref 1)
          (App (App (lift 2 x4) (Ref 1)) (Ref 0))
        )
      )
    )
  ); intros.
  exists x; trivial.
  apply trans_red_red with (AccRec type' rel' choice' f' val' (AccIntro x1 x2 x3 x4)); auto with coc.
  eapply trans_red_red; eauto.
  apply one_step_red; apply acc_rec_exec.
  apply red_red1_ord_norm with (AccRec type' rel' choice' f' val' (AccIntro x1 x2 x3 x4)); auto with coc.

  idtac "doing tree [7]".
  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with rel; auto with coc; intros rel' red_rel n_rel.
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with f; auto with coc; intros f' red_f n_f.
  elim norm_rec with val; auto with coc; intros val' red_val n_val.
  elim norm_rec with proof; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        AccInd type' rel' choice' f' val'
        ltac:(
          match goal with
          | redu : red proof ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (AccInd _ _ _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_acc_ind type' rel' choice' f' val' r u (fun _ _ _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_type with type'0; trivial |
        elim n_rel with rel'0; trivial |
        elim n_choice with choice'0; trivial |
        elim n_f with f'0; trivial |
        elim n_val with val'0; trivial |
        elim nu with proof'; trivial |
        discriminate H0 ..
      ]
    ]
  ).
  idtac "did tree [7]".

  elim norm_rec with (
    App
    (App f' val')
    (
      Abs type' (
        Abs (App (App (lift 1 rel') (Ref 0)) (lift 1 val')) (
          AccInd
          (lift 2 type')
          (lift 2 rel')
          (lift 2 choice')
          (lift 2 f')
          (Ref 1)
          (App (App (lift 2 x4) (Ref 1)) (Ref 0))
        )
      )
    )
  ); intros.
  exists x; trivial.
  apply trans_red_red with (AccInd type' rel' choice' f' val' (AccIntro x1 x2 x3 x4)); auto with coc.
  eapply trans_red_red; eauto.
  apply one_step_red; apply acc_ind_exec.
  apply red_red1_ord_norm with (AccInd type' rel' choice' f' val' (AccIntro x1 x2 x3 x4)); auto with coc.

  elim norm_rec with l; auto with coc; intros l' red_l n_l.
  elim norm_rec with r; auto with coc; intros r' red_r n_r.
  exists (Le l' r'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_l with l'0; trivial.
  elim n_r with r'0; trivial.

  elim norm_rec with n; auto with coc; intros n' red_n n_n.
  exists (LeN n'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_n with n'0; trivial.

  elim norm_rec with l; auto with coc; intros l' red_l n_l.
  elim norm_rec with r; auto with coc; intros r' red_r n_r.
  elim norm_rec with proof; auto with coc; intros proof' red_proof n_proof.
  exists (LeS l' r' proof'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_l with l'0; trivial.
  elim n_r with r'0; trivial.
  elim n_proof with proof'0; trivial.

  idtac "doing tree [8]".
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with on_le_n; auto with coc; intros on_le_n' red_on_le_n n_on_le_n.
  elim norm_rec with on_le_s; auto with coc; intros on_le_s' red_on_le_s n_on_le_s.
  elim norm_rec with l; auto with coc; intros l' red_l n_l.
  elim norm_rec with r; auto with coc; intros r' red_r n_r.
  elim norm_rec with proof; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        LeCases choice' on_le_n' on_le_s' l' r'
        ltac:(
          match goal with
          | redu : red proof ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (LeCases _ _ _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_le_cases choice' on_le_n' on_le_s' l' r' r u (fun _ _ _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_choice with choice'0; trivial |
        elim n_on_le_n with on_le_n'0; trivial |
        elim n_on_le_s with on_le_s'0; trivial |
        elim n_l with l'0; trivial |
        elim n_r with r'0; trivial |
        elim nu with proof'; trivial |
        discriminate H0 |
        discriminate H0 | ..
      ]
    ]
  ).
  idtac "did tree [8]".
  exists on_le_n'; trivial.
  apply trans_red_red with (LeCases choice on_le_n' on_le_s l r (LeN x)); auto with coc.

  elim norm_rec with (App (App on_le_s' x2) x3); intros.
  exists x; trivial.
  apply trans_red_red with (LeCases choice on_le_n on_le_s' l r (LeS x1 x2 x3)); auto with coc.
  apply trans_red_red with (App (App on_le_s' x2) x3); auto with coc.
  apply red_red1_ord_norm with (LeCases choice on_le_n on_le_s' l r (LeS x1 x2 x3)); auto with coc.

  idtac "doing tree [9]".
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with on_le_n; auto with coc; intros on_le_n' red_on_le_n n_on_le_n.
  elim norm_rec with on_le_s; auto with coc; intros on_le_s' red_on_le_s n_on_le_s.
  elim norm_rec with l; auto with coc; intros l' red_l n_l.
  elim norm_rec with r; auto with coc; intros r' red_r n_r.
  elim norm_rec with proof; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        LeInd choice' on_le_n' on_le_s' l' r'
        ltac:(
          match goal with
          | redu : red proof ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (LeInd _ _ _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_le_ind choice' on_le_n' on_le_s' l' r' r u (fun _ _ _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_choice with choice'0; trivial |
        elim n_on_le_n with on_le_n'0; trivial |
        elim n_on_le_s with on_le_s'0; trivial |
        elim n_l with l'0; trivial |
        elim n_r with r'0; trivial |
        elim nu with proof'; trivial |
        discriminate H0 |
        discriminate H0 | ..
      ]
    ]
  ).
  idtac "did tree [9]".

  exists on_le_n'; trivial.
  apply trans_red_red with (LeInd choice on_le_n' on_le_s l r (LeN x)); auto with coc.

  elim norm_rec with (App (App (App on_le_s' x2) x3) (LeInd choice' on_le_n' on_le_s' x1 x2 x3)); intros.
  exists x; trivial.
  apply trans_red_red with (LeInd choice' on_le_n' on_le_s' l r (LeS x1 x2 x3)); auto with coc.
  eapply trans_red_red; eauto.
  auto with coc.
  apply red_red1_ord_norm with (LeInd choice' on_le_n' on_le_s' l r (LeS x1 x2 x3)); auto with coc.

  exists Bool; auto with coc.
  intros x H.
  inversion H.

  elim norm_rec with l; auto with coc; intros l' red_l n_l.
  elim norm_rec with r; auto with coc; intros r' red_r n_r.
  exists (SumBool l' r'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_l with l'0; trivial.
  elim n_r with r'0; trivial.

  exists BoolTrue; auto with coc.
  intros x H.
  inversion H.

  exists BoolFalse; auto with coc.
  intros x H.
  inversion H.

  elim norm_rec with left; auto with coc; intros left' red_left n_left.
  elim norm_rec with right; auto with coc; intros right' red_right n_right.
  elim norm_rec with proof; auto with coc; intros proof' red_proof n_proof.
  exists (SumBoolLeft left' right' proof'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_left with left_pred'; trivial.
  elim n_right with right_pred'; trivial.
  elim n_proof with proof'0; trivial.

  elim norm_rec with left; auto with coc; intros left' red_left n_left.
  elim norm_rec with right; auto with coc; intros right' red_right n_right.
  elim norm_rec with proof; auto with coc; intros proof' red_proof n_proof.
  exists (SumBoolRight left' right' proof'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_left with left_pred'; trivial.
  elim n_right with right_pred'; trivial.
  elim n_proof with proof'0; trivial.

  idtac "doing tree [10]".
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with on_true; auto with coc; intros on_true' red_on_true n_on_true.
  elim norm_rec with on_false; auto with coc; intros on_false' red_on_false n_on_false.
  elim norm_rec with bool; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        BoolInd choice' on_true' on_false'
        ltac:(
          match goal with
          | redu : red bool ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (BoolInd _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_bool_ind choice' on_true' on_false' r u (fun _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_choice with choice'0; trivial |
        elim n_on_true with on_true'0; trivial |
        elim n_on_false with on_false'0; trivial |
        elim nu with bool'; trivial |
        discriminate H0 | 
        discriminate H0 | ..
      ]
    ]
  ).
  idtac "did tree [10]". 

  exists on_true'; trivial.
  apply trans_red_red with (BoolInd choice on_true' on_false BoolTrue); auto with coc.

  exists on_false'; trivial.
  apply trans_red_red with (BoolInd choice on_true on_false' BoolFalse); auto with coc.

  idtac "doing tree [11]".
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with on_true; auto with coc; intros on_true' red_on_true n_on_true.
  elim norm_rec with on_false; auto with coc; intros on_false' red_on_false n_on_false.
  elim norm_rec with bool; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        BoolRec choice' on_true' on_false'
        ltac:(
          match goal with
          | redu : red bool ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (BoolRec _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_bool_rec choice' on_true' on_false' r u (fun _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_choice with choice'0; trivial |
        elim n_on_true with on_true'0; trivial |
        elim n_on_false with on_false'0; trivial |
        elim nu with bool'; trivial |
        discriminate H0 | 
        discriminate H0 | ..
      ]
    ]
  ).
  idtac "did tree [11]".

  exists on_true'; trivial.
  apply trans_red_red with (BoolRec choice on_true' on_false BoolTrue); auto with coc.

  exists on_false'; trivial.
  apply trans_red_red with (BoolRec choice on_true on_false' BoolFalse); auto with coc.

  idtac "doing tree [12]".
  elim norm_rec with left; auto with coc; intros left' red_left n_left.
  elim norm_rec with right; auto with coc; intros right' red_right n_right.
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with on_left; auto with coc; intros on_left' red_on_left n_on_left.
  elim norm_rec with on_right; auto with coc; intros on_right' red_on_right n_on_right.
  elim norm_rec with val; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        SumBoolInd left' right' choice' on_left' on_right'
        ltac:(
          match goal with
          | redu : red val ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (SumBoolInd _ _ _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_sumbool_ind left' right' choice' on_left' on_right' r u (fun _ _ _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_left with left_pred'; trivial |
        elim n_right with right_pred'; trivial |
        elim n_choice with choice'0; trivial |
        elim n_on_left with on_left'0; trivial |
        elim n_on_right with on_right'0; trivial |
        elim nu with val'; trivial |
        discriminate H0 |
        discriminate H0 | ..
      ]
    ]
  ).
  idtac "did tree [12]".

  elim norm_rec with (App on_left' x3); auto with core; intros.
  exists x; trivial.
  apply trans_red_red with (SumBoolInd left right choice on_left' on_right (SumBoolLeft x1 x2 x3)); auto with coc.
  eapply trans_red_red; eauto.
  apply one_step_red; apply sumbool_ind_left.
  apply red_red1_ord_norm with (SumBoolInd left right choice on_left' on_right (SumBoolLeft x1 x2 x3)); auto with coc.

  elim norm_rec with (App on_right' x3); auto with core; intros.
  exists x; trivial.
  apply trans_red_red with (SumBoolInd left right choice on_left on_right' (SumBoolRight x1 x2 x3)); auto with coc.
  eapply trans_red_red; eauto.
  apply one_step_red; apply sumbool_ind_right.
  apply red_red1_ord_norm with (SumBoolInd left right choice on_left on_right' (SumBoolRight x1 x2 x3)); auto with coc.

  idtac "doing tree [13]".
  elim norm_rec with left; auto with coc; intros left' red_left n_left.
  elim norm_rec with right; auto with coc; intros right' red_right n_right.
  elim norm_rec with choice; auto with coc; intros choice' red_choice n_choice.
  elim norm_rec with on_left; auto with coc; intros on_left' red_on_left n_on_left.
  elim norm_rec with on_right; auto with coc; intros on_right' red_on_right n_on_right.
  elim norm_rec with val; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        SumBoolRec left' right' choice' on_left' on_right'
        ltac:(
          match goal with
          | redu : red val ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (SumBoolRec _ _ _ _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_sumbool_rec left' right' choice' on_left' on_right' r u (fun _ _ _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_left with left_pred'; trivial |
        elim n_right with right_pred'; trivial |
        elim n_choice with choice'0; trivial |
        elim n_on_left with on_left'0; trivial |
        elim n_on_right with on_right'0; trivial |
        elim nu with val'; trivial |
        discriminate H0 |
        discriminate H0 | ..
      ]
    ]
  ).
  idtac "did tree [13]".

  elim norm_rec with (App on_left' x3); auto with core; intros.
  exists x; trivial.
  apply trans_red_red with (SumBoolRec left right choice on_left' on_right (SumBoolLeft x1 x2 x3)); auto with coc.
  eapply trans_red_red; eauto.
  apply one_step_red; apply sumbool_rec_left.
  apply red_red1_ord_norm with (SumBoolRec left right choice on_left' on_right (SumBoolLeft x1 x2 x3)); auto with coc.

  elim norm_rec with (App on_right' x3); auto with core; intros.
  exists x; trivial.
  apply trans_red_red with (SumBoolRec left right choice on_left on_right' (SumBoolRight x1 x2 x3)); auto with coc.
  eapply trans_red_red; eauto.
  apply one_step_red; apply sumbool_rec_right.
  apply red_red1_ord_norm with (SumBoolRec left right choice on_left on_right' (SumBoolRight x1 x2 x3)); auto with coc.

  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with property; auto with coc; intros property' red_property n_property.
  exists (Refine type' property'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_type with type'0; trivial.
  elim n_property with property'0; trivial.

  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with property; auto with coc; intros property' red_proerty n_property.
  elim norm_rec with val; auto with coc; intros val' red_val n_val.
  elim norm_rec with proof; auto with coc; intros proof' red_proof n_proof.
  exists (RefineConstr type' property' val' proof'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_type with type'0; trivial.
  elim n_property with property'0; trivial.
  elim n_val with val'0; trivial.
  elim n_proof with proof'0; trivial.

  idtac "doing tree [14]".
  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with property; auto with coc; intros property' red_property n_property.
  elim norm_rec with ref; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        RefineProjVal type' property'
        ltac:(
          match goal with
          | redu : red ref ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (RefineProjVal _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_refine_proj_val type' property' r u (fun _ _ _ _ => False)))
      end; intros;
      [>
        elim n_type with type'0; trivial |
        elim n_property with property'0; trivial |
        elim nu with ref'; trivial |
        discriminate H0 | ..
      ]
    ]
  ).
  idtac "did tree [14]".
  exists x3; auto with coc.
  apply trans_red_red with (RefineProjVal type property (RefineConstr x1 x2 x3 x4)); auto with coc.
  red in |- *; red in |- *; intros.
  elim nu with (RefineConstr x1 x2 u x4); auto with coc.

  idtac "doing tree [15]".
  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with property; auto with coc; intros property' red_property n_property.
  elim norm_rec with ref; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        RefineProjProof type' property'
        ltac:(
          match goal with
          | redu : red ref ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (RefineProjProof _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_refine_proj_proof type' property' r u (fun _ _ _ _ => False)))
      end; intros;
      [>
        elim n_type with type'0; trivial |
        elim n_property with property'0; trivial |
        elim nu with ref'; trivial |
        discriminate H0 | ..
      ]
    ]
  ).
  idtac "did tree [15]".
  exists x4; auto with coc.
  apply trans_red_red with (RefineProjProof type property (RefineConstr x1 x2 x3 x4)); auto with coc.
  red in |- *; red in |- *; intros.
  elim nu with (RefineConstr x1 x2 x3 u); auto with coc.

  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with l; auto with coc; intros l' red_l n_l.
  elim norm_rec with r; auto with coc; intros r' red_r n_r.
  exists (Eq type' l' r'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_type with type'0; trivial.
  elim n_l with l'0; trivial.
  elim n_r with r'0; trivial.

  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with val; auto with coc; intros val' red_val n_val.
  exists (EqRefl type' val'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_type with type'0; trivial.
  elim n_val with val'0; trivial.

  idtac "doing tree [16]".
  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with l; auto with coc; intros l' red_l n_l.
  elim norm_rec with r; auto with coc; intros r' red_r n_r.
  elim norm_rec with property; auto with coc; intros property' red_property n_property.
  elim norm_rec with impl; auto with coc; intros impl' red_impl n_impl.
  elim norm_rec with proof; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        EqInd type' l' r' property' impl'
        ltac:(
          match goal with
          | redu : red proof ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (EqInd type' l' r' property' impl' ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_eq_ind type' l' r' property' impl' r u (fun _ _ _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_type with type'0; trivial |
        elim n_l with l'0; trivial |
        elim n_r with r'0; trivial |
        elim n_property with property'0; trivial |
        elim n_impl with impl'0; trivial |
        elim nu with proof'; trivial |
        discriminate H0 | ..
      ]
    ]
  ).
  idtac "did tree [16]".
  exists impl'; trivial.
  apply trans_red_red with (EqInd type l r property impl' (EqRefl x1 x2)); auto with coc.

  idtac "doing tree [17]".
  elim norm_rec with type; auto with coc; intros type' red_type n_type.
  elim norm_rec with l; auto with coc; intros l' red_l n_l.
  elim norm_rec with r; auto with coc; intros r' red_r n_r.
  elim norm_rec with property; auto with coc; intros property' red_property n_property.
  elim norm_rec with impl; auto with coc; intros impl' red_impl n_impl.
  elim norm_rec with proof; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        EqRec type' l' r' property' impl'
        ltac:(
          match goal with
          | redu : red proof ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (EqRec type' l' r' property' impl' ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_eq_rec type' l' r' property' impl' r u (fun _ _ _ _ _ _ _ => False)))
      end; intros;
      [>
        elim n_type with type'0; trivial |
        elim n_l with l'0; trivial |
        elim n_r with r'0; trivial |
        elim n_property with property'0; trivial |
        elim n_impl with impl'0; trivial |
        elim nu with proof'; trivial |
        discriminate H0 | ..
      ]
    ]
  ).
  idtac "did tree [17]".
  exists impl'; trivial.
  apply trans_red_red with (EqRec type l r property impl' (EqRefl x1 x2)); auto with coc.

  exists Falsity; auto with coc.
  intros x H.
  inversion H.

  elim norm_rec with proof; auto with coc; intros proof' red_proof n_proof.
  elim norm_rec with property; auto with coc; intros property' red_property n_property.
  exists (FalseInd proof' property'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_proof with proof'0; trivial.
  elim n_property with property'0; trivial.

  elim norm_rec with proof; auto with coc; intros proof' red_proof n_proof.
  elim norm_rec with property; auto with coc; intros property' red_property n_property.
  exists (FalseRec proof' property'); auto with coc.
  red in |- *; red in |- *; intros.
  inversion_clear H.
  elim n_proof with proof'0; trivial.
  elim n_property with property'0; trivial.

  exists Unit; auto with coc.
  intros x H.
  inversion H.

  exists Nil; auto with coc.
  intros x H.
  inversion H.

  elim norm_rec with (
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
                  (Abs (lift 3 type) (App (App (lift 4 rel) (Ref 0)) (Ref 3)))
                )
                (
                  App 
                  (
                    App (Ref 1) 
                    (RefineProjVal (lift 4 type) (Abs (lift 4 type) (App (App (lift 5 rel) (Ref 0)) (Ref 3))) (Ref 0))
                  ) 
                  (RefineProjProof (lift 4 type) (Abs (lift 4 type) (App (App (lift 5 rel) (Ref 0)) (Ref 3))) (Ref 0)) 
                )
              )
            )  
          )
        )
        (Ref 0)
        (App (lift 1 proof) (Ref 0))
      )
    ); auto with coc.
  intros res red_res n_res.
  exists res; auto with coc.
  eapply trans_red_red; eauto.
  apply one_step_red; apply wf_rec_expand.
  apply red_red1_ord_norm with (WFrec type rel choice f proof); auto with coc.

  idtac "doing tree [18]".
  elim norm_rec with on_true; auto with coc; intros on_true' red_on_true n_on_true.
  elim norm_rec with on_false; auto with coc; intros on_false' red_on_false n_on_false.
  elim norm_rec with val; auto with coc.
  intros [
    s | n | T t | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redu nu;
  try (
    solve [
      exists (
        BoolPropChoice on_true' on_false'
        ltac:(
          match goal with
          | redu : red val ?r |- _ => exact r
          end
        )
      ); auto with coc;
      red in |- *; red in |- *; intros;
      match goal with
      | H : red1 (BoolPropChoice _ _ ?r) _ |- _ => (generalize (eq_refl r); inversion H using (leminv_red_bool_prop_choice on_true' on_false' r u (fun _ _ _ _ => False)))
      end; intros;
      [>
        elim n_on_true with on_true'0; trivial |
        elim n_on_false with on_false'0; trivial |
        elim nu with val'; trivial |
        discriminate H0 | 
        discriminate H0 | ..
      ]
    ]
  ).
  idtac "did tree [18]".

  exists on_true'; trivial.
  apply trans_red_red with (BoolPropChoice on_true' on_false BoolTrue); auto with coc.

  exists on_false'; trivial.
  apply trans_red_red with (BoolPropChoice on_true on_false' BoolFalse); auto with coc.

  idtac "Saving proof".
  apply wf_ord_norm; auto with coc.
Qed.

(* Term equality is decidable *)
Definition eqterm : forall u v : term, {u = v} + {u <> v}.
Proof.
  decide equality.
  decide equality.
  apply eq_nat_dec.
Qed.


(* The main result of this module *)
Definition is_conv :
  forall u v : term, sn u -> sn v -> {conv u v} + {~ conv u v}.
Proof.
  intros u v snu snv.
  elim compute_nf with (1 := snu); intros u' redu nu.
  elim compute_nf with (1 := snv); intros v' redv nv.
  elim eqterm with u' v'; [ intros same_nf | intros diff_nf ].
  left.
  apply trans_conv_conv with u'; auto with coc.
  rewrite same_nf; apply sym_conv; auto with coc.

  right; red in |- *; intro; apply diff_nf.
  elim church_rosser with u' v'; auto with coc; intros.
  rewrite (red_normal u' x); auto with coc.
  rewrite (red_normal v' x); auto with coc.

  apply trans_conv_conv with v; auto with coc.
  apply trans_conv_conv with u; auto with coc.
  apply sym_conv; auto with coc.
Qed.
