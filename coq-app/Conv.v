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

Require Export RelationClasses.

Require Import Termes.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Section Church_Rosser.

  (*
    Drafty definition: if a -> b and a -> c then
    there's d such that b -> d and (c -> d or c = d)
    After some playing with diagrams we notice that this
    definition  is equivalent to commutation of the
    relation with its own inverse.
  *)
  Definition str_confluent (R : term -> term -> Prop) :=
    commut _ R (transp _ R)
  .

  (*
    We show the correctnes of the above reasoning
  *)
  Lemma str_confluent_correct : forall R : relation term,
    str_confluent R ->
    forall x y z, R x y -> R x z ->
    exists2 w, R y w & R z w
  .
  Proof.
    intros R H x y z H0 H1.
    elim (H y x H0 z H1).
    intros; exists x0; auto with core.
  Qed.

  (*
    We are going to prove that parallel one-step
    reduction is strongly confluent. This is a powerful
    enough lemma to prove other results about confluency
  *)
  Lemma str_confluence_par_red1 : str_confluent par_red1.
  Proof.
    red in |- *; red in |- *.
    simple induction 1; intros.

    inversion_clear H4.
    elim H1 with M'0; auto with coc core arith sets; intros.
    elim H3 with N'0; auto with coc core arith sets; intros.
    exists (subst x1 x0); unfold subst in |- *; auto with coc core arith sets.

    inversion_clear H5.
    elim H1 with M'1; auto with coc core arith sets; intros.
    elim H3 with N'0; auto with coc core arith sets; intros.
    exists (subst x1 x0); auto with coc core arith sets; unfold subst in |- *;
    auto with coc core arith sets.

    inversion_clear H0.
    exists (Srt s); auto with coc core arith sets.

    inversion_clear H0.
    exists (Ref n); auto with coc core arith sets.

    inversion_clear H4.
    elim H1 with M'0; auto with coc core arith sets; intros.
    elim H3 with T'0; auto with coc core arith sets; intros.
    exists (Abs x1 x0); auto with coc core arith sets.

    generalize H0 H1.
    clear H0 H1.
    inversion_clear H4.
    intro.
    inversion_clear H4.
    intros.
    elim H4 with (Abs T M'0); auto with coc core arith sets; intros.
    elim H3 with N'0; auto with coc core arith sets; intros.
    apply inv_par_red_abs with T' M'1 x0; intros; auto with coc core arith sets.
    generalize H7 H8.
    rewrite H11.
    clear H7 H8; intros.
    inversion_clear H7.
    inversion_clear H8.
    exists (subst x1 U'); auto with coc core arith sets.
    unfold subst in |- *; auto with coc core arith sets.

    intros.
    elim H5 with M'0; auto with coc core arith sets; intros.
    elim H3 with N'0; auto with coc core arith sets; intros.
    exists (App x0 x1); auto with coc core arith sets.

    intros.
    inversion_clear H4.
    elim H1 with M'0; auto with coc core arith sets; intros.
    elim H3 with N'0; auto with coc core arith sets; intros.
    exists (Prod x0 x1); auto with coc core arith sets.

    (* For some reason Coq decided to troll me and not inverse the `z` properly *)
    inversion H8.
    subst choice0; subst on_zero0; subst on_succ0; subst num0; subst z.
    elim H1 with choice'0; auto with core coc; intros.
    elim H3 with on_zero'0; auto with core coc; intros.
    elim H5 with on_succ'0; auto with core coc; intros.
    elim H7 with num'0; auto with core coc; intros.
    exists (NatDestruct x0 x1 x2 x3); auto with coc core.
    apply nat_destruct_par_red; auto with coc core.
    subst num; subst z; subst on_zero0; subst choice0; subst on_succ0.
    elim H3 with on_zero'0; auto with core coc; intros.
    inversion H6; subst num'.
    exists x0; auto with coc core.
    apply nat_destruct_on_zero_par_red; auto with coc core.
    subst choice0; subst on_zero0; subst on_succ0; subst num; subst z.
    elim H5 with on_succ'0; auto with coc core; intros.
    elim H7 with (NatSucc num'0); auto with coc core; intros.
    inversion H12; subst x2.
    subst x1.
    inversion H6; subst num'.
    subst x1.
    exists (App x0 x'); auto with coc core.
    apply nat_destruct_on_succ_par_red; auto with coc core.
    inversion_clear H11; auto with coc core.
    apply nat_succ_par_red; auto with coc core.

    inversion H2.
    subst choice0; subst on_zero0; subst on_succ0; subst num; subst z.
    inversion H11; subst num'.
    elim H1 with on_zero'0; auto with coc core; intros.
    exists x0; auto with coc core.
    subst choice0; subst on_zero0; subst on_succ0; subst z.
    elim H1 with on_zero'0; auto with coc core; intros.

    inversion H4.
    subst choice0; subst on_zero0; subst on_succ0; subst num0; subst z.
    inversion H13; subst num'0.
    subst x0.
    elim H1 with on_succ'0; auto with coc core; intros.
    elim H3 with x'; auto with coc core; intros.
    exists (App x0 x1); auto with coc core.
    apply app_par_red; auto with coc core.
    subst choice0; subst on_zero0; subst on_succ0; subst num0; subst z.
    elim H1 with on_succ'0; auto with coc core; intros.
    elim H3 with num'0; auto with coc core; intros.
    exists (App x0 x1); auto with coc core.
    apply app_par_red; auto with coc core.

    inversion H8.
    subst choice0; subst on_zero0; subst on_succ0; subst num0; subst z.
    elim H1 with choice'0; auto with core coc; intros.
    elim H3 with on_zero'0; auto with core coc; intros.
    elim H5 with on_succ'0; auto with core coc; intros.
    elim H7 with num'0; auto with core coc; intros.
    exists (NatCases x0 x1 x2 x3); auto with coc core.
    apply nat_cases_par_red; auto with coc core.
    subst num; subst z; subst on_zero0; subst choice0; subst on_succ0.
    elim H3 with on_zero'0; auto with core coc; intros.
    inversion H6; subst num'.
    exists x0; auto with coc core.
    apply nat_cases_on_zero_par_red; auto with coc core.
    subst choice0; subst on_zero0; subst on_succ0; subst num; subst z.
    elim H5 with on_succ'0; auto with coc core; intros.
    elim H7 with (NatSucc num'0); auto with coc core; intros.
    inversion H12; subst x2.
    subst x1.
    inversion H6; subst num'.
    subst x1.
    exists (App x0 x'); auto with coc core.
    apply nat_cases_on_succ_par_red; auto with coc core.
    inversion_clear H11; auto with coc core.
    apply nat_succ_par_red; auto with coc core.

    inversion H2.
    subst choice0; subst on_zero0; subst on_succ0; subst num; subst z.
    inversion H11; subst num'.
    elim H1 with on_zero'0; auto with coc core; intros.
    exists x0; auto with coc core.
    subst choice0; subst on_zero0; subst on_succ0; subst z.
    elim H1 with on_zero'0; auto with coc core; intros.

    inversion H4.
    subst choice0; subst on_zero0; subst on_succ0; subst num0; subst z.
    inversion H13; subst num'0.
    subst x0.
    elim H1 with on_succ'0; auto with coc core; intros.
    elim H3 with x'; auto with coc core; intros.
    exists (App x0 x1); auto with coc core.
    apply app_par_red; auto with coc core.
    subst choice0; subst on_zero0; subst on_succ0; subst num0; subst z.
    elim H1 with on_succ'0; auto with coc core; intros.
    elim H3 with num'0; auto with coc core; intros.
    exists (App x0 x1); auto with coc core.
    apply app_par_red; auto with coc core.

    inversion H2; subst z.
    subst x1.
    elim H1 with x'0; auto with coc core; intros.
    exists (NatSucc x1); auto with coc core.
    apply nat_succ_par_red; auto with coc core.

    inversion H0; subst z; exists Nat; auto with coc core.

    inversion H0; subst z; exists NatO; auto with coc core.

    inversion H8.
    subst z; subst num0; subst on_succ0; subst on_zero0; subst choice0.
    elim H1 with choice'0; auto with coc core; intros.
    elim H3 with on_zero'0; auto with coc core; intros.
    elim H5 with on_succ'0; auto with coc core; intros.
    elim H7 with num'0; auto with coc core; intros.
    exists (NatRec x0 x1 x2 x3); auto with coc core.
    apply nat_rec_par_red; auto with coc core.
    subst z; subst num; subst on_succ0; subst on_zero0; subst choice0.
    elim H3 with on_zero'0; auto with coc core; intros.
    exists x0; auto with coc core.
    inversion H6; subst num'.
    apply nat_rec_on_zero_par_red; auto with coc core.
    subst z; subst num; subst on_succ; subst on_zero; subst choice.
    inversion H6.
    subst num'; rename x' into num'; subst x0.
    elim H1 with choice'0; auto with coc core; intros.
    elim H3 with on_zero'0; auto with coc core; intros.
    elim H5 with on_succ'0; auto with coc core; intros.
    elim H7 with (NatSucc num'0); auto with coc core; intros.
    inversion H21; subst x3.
    subst x4.
    rename x' into x3.
    exists (App (App x2 x3) (NatRec x0 x1 x2 x3)); auto with coc core.
    apply nat_rec_on_succ_par_red; auto with coc core.
    inversion_clear H20; auto with coc core.
    apply nat_succ_par_red; auto with coc core.

    inversion H2.
    subst z; subst num; subst on_zero0; subst on_succ0; subst choice0.
    elim H1 with on_zero'0; auto with coc core; intros.
    exists x0; auto with coc core.
    inversion_clear H11; apply nat_rec_on_zero_par_red; auto with coc core.
    subst z; elim H1 with on_zero'0; auto with coc core; intros.

    inversion H8.
    subst z; subst num0; subst on_succ0; subst on_zero0; subst choice0.
    inversion H17.
    subst x0; subst num'0; rename x' into num'0.
    elim H1 with choice'0; auto with coc core; intros.
    elim H3 with on_zero'0; auto with coc core; intros.
    elim H5 with on_succ'0; auto with coc core; intros.
    elim H7 with num'0; auto with coc core; intros.
    exists (App (App x2 x3) (NatRec x0 x1 x2 x3)); auto with coc core.
    apply app_par_red; auto with coc core.
    subst z; subst num0; subst on_succ0; subst on_zero0; subst choice0.
    elim H1 with choice'0; auto with coc core; intros.
    elim H3 with on_zero'0; auto with coc core; intros.
    elim H5 with on_succ'0; auto with coc core; intros.
    elim H7 with num'0; auto with coc core; intros.
    exists (App (App x2 x3) (NatRec x0 x1 x2 x3)); auto with coc core.
    apply app_par_red; auto with coc core.

    inversion H8.
    subst z; subst num0; subst on_succ0; subst on_zero0; subst choice0.
    elim H1 with choice'0; auto with coc core; intros.
    elim H3 with on_zero'0; auto with coc core; intros.
    elim H5 with on_succ'0; auto with coc core; intros.
    elim H7 with num'0; auto with coc core; intros.
    exists (NatInd x0 x1 x2 x3); auto with coc core.
    apply nat_ind_par_red; auto with coc core.
    subst z; subst num; subst on_succ0; subst on_zero0; subst choice0.
    elim H3 with on_zero'0; auto with coc core; intros.
    exists x0; auto with coc core.
    inversion H6; subst num'.
    apply nat_ind_on_zero_par_red; auto with coc core.
    subst z; subst num; subst on_succ; subst on_zero; subst choice.
    inversion H6.
    subst num'; rename x' into num'; subst x0.
    elim H1 with choice'0; auto with coc core; intros.
    elim H3 with on_zero'0; auto with coc core; intros.
    elim H5 with on_succ'0; auto with coc core; intros.
    elim H7 with (NatSucc num'0); auto with coc core; intros.
    inversion H21; subst x3.
    subst x4.
    rename x' into x3.
    exists (App (App x2 x3) (NatInd x0 x1 x2 x3)); auto with coc core.
    apply nat_ind_on_succ_par_red; auto with coc core.
    inversion_clear H20; auto with coc core.
    apply nat_succ_par_red; auto with coc core.

    inversion H2.
    subst z; subst num; subst on_zero0; subst on_succ0; subst choice0.
    elim H1 with on_zero'0; auto with coc core; intros.
    exists x0; auto with coc core.
    inversion_clear H11; apply nat_ind_on_zero_par_red; auto with coc core.
    subst z; elim H1 with on_zero'0; auto with coc core; intros.

    inversion H8.
    subst z; subst num0; subst on_succ0; subst on_zero0; subst choice0.
    inversion H17.
    subst x0; subst num'0; rename x' into num'0.
    elim H1 with choice'0; auto with coc core; intros.
    elim H3 with on_zero'0; auto with coc core; intros.
    elim H5 with on_succ'0; auto with coc core; intros.
    elim H7 with num'0; auto with coc core; intros.
    exists (App (App x2 x3) (NatInd x0 x1 x2 x3)); auto with coc core.
    apply app_par_red; auto with coc core.
    subst z; subst num0; subst on_succ0; subst on_zero0; subst choice0.
    elim H1 with choice'0; auto with coc core; intros.
    elim H3 with on_zero'0; auto with coc core; intros.
    elim H5 with on_succ'0; auto with coc core; intros.
    elim H7 with num'0; auto with coc core; intros.
    exists (App (App x2 x3) (NatInd x0 x1 x2 x3)); auto with coc core.
    apply app_par_red; auto with coc core.

    inversion_clear H6.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with rel'0; auto with coc core arith sets; intros.
    elim H5 with val'0; auto with coc core arith sets; intros.
    exists (AccProp x0 x1 x2); auto with coc core arith sets.

    inversion_clear H8.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with rel'0; auto with coc core arith sets; intros.
    elim H5 with val'0; auto with coc core arith sets; intros.
    elim H7 with proof'0; auto with coc core arith sets; intros.
    exists (AccIntro x0 x1 x2 x3); auto with coc core arith sets.

    inversion H12.
    subst type0; subst rel0; subst choice0; subst f0; subst val0; subst proof0; subst z.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with rel'0; auto with coc core arith sets; intros.
    elim H5 with choice'0; auto with coc core arith sets; intros.
    elim H7 with f'0; auto with coc core arith sets; intros.
    elim H9 with val'0; auto with coc core arith sets; intros.
    elim H11 with proof'0; auto with coc core arith sets; intros.
    exists (AccRec x0 x1 x2 x3 x4 x5); auto with coc core arith sets.
    subst z; subst proof; subst f0; subst val_a; subst choice0; subst rel_a; subst type_a.
    inversion H10.
    subst type0; subst rel0; subst val0; subst proof0; subst proof'.
    elim H1 with type_a'; intros; auto with coc core arith sets.
    elim H3 with rel_a'; intros; auto with coc core arith sets.
    elim H5 with choice'0; intros; auto with coc core arith sets.
    elim H7 with f'0; intros; auto with coc core arith sets.
    elim H9 with val_a'; intros; auto with coc core arith sets.
    elim H11 with (AccIntro type'0 rel'0 val'0 proof'0); intros; auto with coc core arith sets.
    inversion H33.
    subst proof0; subst val0; subst rel0; subst type0; subst x5.
    inversion_clear H34.
    exists (
      App
      (App x3 x4)
      (
        Abs x0 (
          Abs (App (App (lift 1 x1) (Ref 0)) (lift 1 x4)) (
            AccRec
            (lift 2 x0)
            (lift 2 x1)
            (lift 2 x2)
            (lift 2 x3)
            (Ref 1)
            (App (App (lift 2 proof') (Ref 1)) (Ref 0))
          )
        )
      )
    ); auto 11 with coc core arith sets.
    unfold lift; auto 11 with coc core arith sets.

    inversion H12.
    subst type; subst rel; subst choice0; subst f0; subst val; subst proof0; subst z.
    inversion H25.
    subst type; subst rel; subst val; subst proof0; subst proof'0.
    elim H1 with type'; intros; auto with coc core arith sets.
    elim H3 with rel'; intros; auto with coc core arith sets.
    elim H5 with val'; intros; auto with coc core arith sets.
    elim H7 with choice'0; intros; auto with coc core arith sets.
    elim H9 with f'0; intros; auto with coc core arith sets.
    elim H11 with proof'1; intros; auto with coc core arith sets.
    exists (
      App
      (App x4 x2)
      (
        Abs x0 (
          Abs (App (App (lift 1 x1) (Ref 0)) (lift 1 x2)) (
            AccRec
            (lift 2 x0)
            (lift 2 x1)
            (lift 2 x3)
            (lift 2 x4)
            (Ref 1)
            (App (App (lift 2 x5) (Ref 1)) (Ref 0))
          )
        )
      )
    ); auto 11 with coc core arith sets.
    unfold lift; auto 11 with coc core arith sets.
    subst z; subst proof0; subst val_b0; subst rel_b0; subst type_b0; subst val_a0; subst f0; subst choice0; subst rel_a0; subst type_a0.
    elim H1 with type_a'0; intros; auto with coc core arith sets.
    elim H3 with rel_a'0; intros; auto with coc core arith sets.
    elim H5 with val_a'0; intros; auto with coc core arith sets.
    elim H7 with choice'0; intros; auto with coc core arith sets.
    elim H9 with f'0; intros; auto with coc core arith sets.
    elim H11 with proof'0; intros; auto with coc core arith sets.
    exists (
      App
      (App x4 x2)
      (
        Abs x0 (
          Abs (App (App (lift 1 x1) (Ref 0)) (lift 1 x2)) (
            AccRec
            (lift 2 x0)
            (lift 2 x1)
            (lift 2 x3)
            (lift 2 x4)
            (Ref 1)
            (App (App (lift 2 x5) (Ref 1)) (Ref 0))
          )
        )
      )
    ); auto 11 with coc core arith sets.
    unfold lift; auto 11 with coc core arith sets.
    unfold lift; auto 11 with coc core arith sets.

    inversion H12.
    subst type0; subst rel0; subst choice0; subst f0; subst val0; subst proof0; subst z.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with rel'0; auto with coc core arith sets; intros.
    elim H5 with choice'0; auto with coc core arith sets; intros.
    elim H7 with f'0; auto with coc core arith sets; intros.
    elim H9 with val'0; auto with coc core arith sets; intros.
    elim H11 with proof'0; auto with coc core arith sets; intros.
    exists (AccInd x0 x1 x2 x3 x4 x5); auto with coc core arith sets.
    subst z; subst proof; subst f0; subst val_a; subst choice0; subst rel_a; subst type_a.
    inversion H10.
    subst type0; subst rel0; subst val0; subst proof0; subst proof'.
    elim H1 with type_a'; intros; auto with coc core arith sets.
    elim H3 with rel_a'; intros; auto with coc core arith sets.
    elim H5 with choice'0; intros; auto with coc core arith sets.
    elim H7 with f'0; intros; auto with coc core arith sets.
    elim H9 with val_a'; intros; auto with coc core arith sets.
    elim H11 with (AccIntro type'0 rel'0 val'0 proof'0); intros; auto with coc core arith sets.
    inversion H33.
    subst proof0; subst val0; subst rel0; subst type0; subst x5.
    inversion_clear H34.
    exists (
      App
      (App x3 x4)
      (
        Abs x0 (
          Abs (App (App (lift 1 x1) (Ref 0)) (lift 1 x4)) (
            AccInd
            (lift 2 x0)
            (lift 2 x1)
            (lift 2 x2)
            (lift 2 x3)
            (Ref 1)
            (App (App (lift 2 proof') (Ref 1)) (Ref 0))
          )
        )
      )
    ); auto 11 with coc core arith sets.
    unfold lift; auto 11 with coc core arith sets.

    inversion H12.
    subst type; subst rel; subst choice0; subst f0; subst val; subst proof0; subst z.
    inversion H25.
    subst type; subst rel; subst val; subst proof0; subst proof'0.
    elim H1 with type'; intros; auto with coc core arith sets.
    elim H3 with rel'; intros; auto with coc core arith sets.
    elim H5 with val'; intros; auto with coc core arith sets.
    elim H7 with choice'0; intros; auto with coc core arith sets.
    elim H9 with f'0; intros; auto with coc core arith sets.
    elim H11 with proof'1; intros; auto with coc core arith sets.
    exists (
      App
      (App x4 x2)
      (
        Abs x0 (
          Abs (App (App (lift 1 x1) (Ref 0)) (lift 1 x2)) (
            AccInd
            (lift 2 x0)
            (lift 2 x1)
            (lift 2 x3)
            (lift 2 x4)
            (Ref 1)
            (App (App (lift 2 x5) (Ref 1)) (Ref 0))
          )
        )
      )
    ); auto 11 with coc core arith sets.
    unfold lift; auto 11 with coc core arith sets.
    subst z; subst proof0; subst val_b0; subst rel_b0; subst type_b0; subst val_a0; subst f0; subst choice0; subst rel_a0; subst type_a0.
    elim H1 with type_a'0; intros; auto with coc core arith sets.
    elim H3 with rel_a'0; intros; auto with coc core arith sets.
    elim H5 with val_a'0; intros; auto with coc core arith sets.
    elim H7 with choice'0; intros; auto with coc core arith sets.
    elim H9 with f'0; intros; auto with coc core arith sets.
    elim H11 with proof'0; intros; auto with coc core arith sets.
    exists (
      App
      (App x4 x2)
      (
        Abs x0 (
          Abs (App (App (lift 1 x1) (Ref 0)) (lift 1 x2)) (
            AccInd
            (lift 2 x0)
            (lift 2 x1)
            (lift 2 x3)
            (lift 2 x4)
            (Ref 1)
            (App (App (lift 2 x5) (Ref 1)) (Ref 0))
          )
        )
      )
    ); auto 11 with coc core arith sets.
    unfold lift; auto 11 with coc core arith sets.
    unfold lift; auto 11 with coc core arith sets.

    inversion_clear H4.
    elim H1 with l'0; intros; auto with coc core arith sets.
    elim H3 with r'0; intros; auto with coc core arith sets.
    exists (Le x0 x1); auto with coc core arith sets.

    inversion_clear H2.
    elim H1 with n'0; intros; auto with coc core arith sets.
    exists (LeN x0); auto with coc core arith sets.

    inversion_clear H6.
    elim H1 with l'0; auto with coc core arith sets; intros.
    elim H3 with r'0; auto with coc core arith sets; intros.
    elim H5 with proof'0; auto with coc core arith sets; intros.
    exists (LeS x0 x1 x2); auto with coc core arith sets.

    inversion H12.
    subst choice0; subst on_le_n0; subst on_le_s0; subst l0; subst r0; subst proof0; subst z.
    elim H1 with choice'0; auto with coc core arith sets; intros.
    elim H3 with on_le_n'0; auto with coc core arith sets; intros.
    elim H5 with on_le_s'0; auto with coc core arith sets; intros.
    elim H7 with l'0; auto with coc core arith sets; intros.
    elim H9 with r'0; auto with coc core arith sets; intros.
    elim H11 with proof'0; auto with coc core arith sets; intros.
    exists (LeCases x0 x1 x2 x3 x4 x5); auto with coc core arith sets.
    
    subst z; subst proof; subst r0; subst l0; subst on_le_s0; subst on_le_n0; subst choice0.
    elim H3 with on_le_n'0; auto with coc core arith sets; intros.
    inversion_clear H10.
    exists x0; auto with coc core arith sets.

    subst z; subst proof; subst r_a; subst l_a; subst on_le_s0; subst on_le_n0; subst choice0.
    inversion H10.
    subst proof'; subst proof0; subst r0; subst l0.
    elim H11 with (LeS l'0 r_b' proof'0); auto with coc core arith sets; intros.
    inversion H13.
    subst l0; subst r0; subst proof0; subst x0.
    inversion_clear H14.    
    elim H5 with on_le_s'0; auto with coc core arith sets; intros.
    exists (App (App x0 r'1) proof'); auto with coc core arith sets.

    inversion H2.
    subst choice0; subst z; subst proof; subst r0; subst l0; subst on_le_s0; subst on_le_n0.
    inversion H15.
    subst n0; subst proof'.
    elim H1 with on_le_n'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    subst choice0; subst z; subst n0; subst r0; subst l0; subst on_le_s0; subst on_le_n0.
    elim H1 with on_le_n'0; auto with coc core arith sets; intros.

    inversion H6.
    subst z; subst choice0; subst proof0; subst r_a; subst l_a; subst on_le_s0; subst on_le_n0.
    inversion H19.
    subst proof'0; subst proof0; subst r0; subst l0.
    elim H5 with proof'1; auto with coc core arith sets; intros.
    elim H1 with on_le_s'0; auto with coc core arith sets; intros.
    elim H3 with r'0; auto with coc core arith sets; intros.
    exists (App (App x1 x2) x0); auto with coc core arith sets.
    subst choice0; subst on_le_n0; subst on_le_s0; subst l_a0; subst r_a0; subst l_b0; subst r_b0; subst proof0; subst z.
    elim H1 with on_le_s'0; auto with coc core arith sets; intros.
    elim H3 with r_b'0; auto with coc core arith sets; intros.
    elim H5 with proof'0; auto with coc core arith sets; intros.
    exists (App (App x0 x1) x2); auto with coc core arith sets.

    inversion H12.
    subst choice0; subst on_le_n0; subst on_le_s0; subst l0; subst r0; subst proof; subst z.
    elim H1 with choice'0; auto with coc core arith sets; intros.
    elim H3 with on_le_n'0; auto with coc core arith sets; intros.
    elim H5 with on_le_s'0; auto with coc core arith sets; intros.
    elim H7 with l'0; auto with coc core arith sets; intros.
    elim H9 with r'0; auto with coc core arith sets; intros.
    elim H11 with proof'0; auto with coc core arith sets; intros.
    exists (LeInd x0 x1 x2 x3 x4 x5); auto with coc core arith sets.

    subst choice0; subst on_le_n0; subst on_le_s0; subst l0; subst r0; subst proof; subst z.
    inversion H10.
    subst proof'; subst n0.
    elim H3 with on_le_n'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    subst choice0; subst on_le_n0; subst on_le_s0; subst l_a; subst r_a; subst proof; subst z.
    inversion H10.
    subst l0; subst r0; subst proof0; subst proof'.
    elim H1 with choice'0; auto with coc core arith sets; intros.
    elim H3 with on_le_n'0; auto with coc core arith sets; intros.
    elim H5 with on_le_s'0; auto with coc core arith sets; intros.
    elim H11 with (LeS l_b' r_b' proof'0); auto with coc core arith sets; intros.
    inversion H29.
    subst proof0; subst l0; subst r0; subst x3.
    inversion_clear H28; auto with coc core arith sets.
    exists (App (App (App x2  r'1) proof') (LeInd x0 x1 x2 l'1 r'1 proof')); auto with coc core arith sets.

    inversion H2.
    subst choice0; subst l0; subst r0; subst on_le_n0; subst on_le_s0; subst proof; subst z.
    inversion H15.
    subst n0; subst proof'.
    elim H1 with on_le_n'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    subst choice0; subst on_le_n0; subst on_le_s0; subst l0; subst r0; subst n0; subst z.
    inversion H2.
    subst choice0; subst proof; subst l0; subst r0; subst on_le_n0; subst on_le_s0; subst on_le_n'0.
    inversion H16.
    subst proof'; subst n0.
    elim H1 with on_le_n'1; auto with coc core arith sets; intros.
    subst on_le_n0; subst choice0; subst on_le_s0; subst l0; subst r0; subst n0; subst on_le_n'1.
    elim H1 with on_le_n'0; auto with coc core arith sets; intros.

    inversion H12.
    subst choice0; subst on_le_n0; subst on_le_s0; subst l_a; subst r_a; subst proof0; subst z.
    inversion H25.
    subst l0; subst r0; subst proof0; subst proof'0.
    elim H1 with choice'0; auto with coc core arith sets; intros.
    elim H3 with on_le_n'0; auto with coc core arith sets; intros.
    elim H5 with on_le_s'0; auto with coc core arith sets; intros.
    elim H7 with l'0; auto with coc core arith sets; intros.
    elim H9 with r'0; auto with coc core arith sets; intros.
    elim H11 with proof'1; auto with coc core arith sets; intros.
    exists (App (App (App x2 x4) x5) (LeInd x0 x1 x2 x3 x4 x5)); auto with coc core arith sets.
    subst z; subst proof0; subst l_b0; subst r_b0; subst r_a0; subst l_a0; subst on_le_s0; subst on_le_n0; subst choice0.
    elim H1 with choice'0; auto with coc core arith sets; intros.
    elim H3 with on_le_n'0; auto with coc core arith sets; intros.
    elim H5 with on_le_s'0; auto with coc core arith sets; intros.
    elim H7 with l_b'0; auto with coc core arith sets; intros.
    elim H9 with r_b'0; auto with coc core arith sets; intros.
    elim H11 with proof'0; auto with coc core arith sets; intros.
    exists (App (App (App x2 x4) x5) (LeInd x0 x1 x2 x3 x4 x5)); auto with coc core arith sets.

    inversion_clear H0.
    exists Bool; auto with coc core arith sets.

    inversion_clear H0.
    exists BoolTrue; auto with coc core arith sets.

    inversion_clear H0.
    exists BoolFalse; auto with coc core arith sets.

    inversion_clear H4.
    elim H1 with l'0; auto with coc core arith sets; intros.
    elim H3 with r'0; auto with coc core arith sets; intros.
    exists (SumBool x0 x1); auto with coc core arith sets.

    inversion_clear H6.
    elim H1 with left_pred'0; auto with coc core arith sets; intros.
    elim H3 with right_pred'0; auto with coc core arith sets; intros.
    elim H5 with proof'0; auto with coc core arith sets; intros.
    exists (SumBoolLeft x0 x1 x2); auto with coc core arith sets.

    inversion_clear H6.
    elim H1 with left_pred'0; auto with coc core arith sets; intros.
    elim H3 with right_pred'0; auto with coc core arith sets; intros.
    elim H5 with proof'0; auto with coc core arith sets; intros.
    exists (SumBoolRight x0 x1 x2); auto with coc core arith sets.

    inversion H8.
    subst z; subst bool0; subst on_false0; subst on_true0; subst choice0.
    elim H1 with choice'0; auto with coc core arith sets; intros.
    elim H3 with on_true'0; auto with coc core arith sets; intros.
    elim H5 with on_false'0; auto with coc core arith sets; intros.
    elim H7 with bool'0; auto with coc core arith sets; intros.
    exists (BoolInd x0 x1 x2 x3); auto with coc core arith sets.
    subst z; subst bool; subst on_false0; subst on_true0; subst choice0.
    elim H3 with on_true'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    inversion_clear H6; auto with coc core arith sets.
    subst z; subst bool; subst on_false0; subst on_true0; subst choice0.
    elim H5 with on_false'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    inversion_clear H6; auto with coc core arith sets.

    inversion H2.
    subst choice0; subst on_true0; subst on_false0; subst bool; subst z.
    elim H1 with on_true'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    inversion_clear H11; auto with coc core arith sets.
    subst choice0; subst on_true0; subst on_false0; subst z.
    elim H1 with on_true'0; auto with coc core arith sets; intros.

    inversion H2.
    subst choice0; subst on_true0; subst on_false0; subst bool; subst z.
    elim H1 with on_false'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    inversion_clear H11; auto with coc core arith sets.
    subst choice0; subst on_true0; subst on_false0; subst z.
    elim H1 with on_false'0; auto with coc core arith sets; intros.

    inversion H8.
    subst z; subst bool0; subst on_false0; subst on_true0; subst choice0.
    elim H1 with choice'0; auto with coc core arith sets; intros.
    elim H3 with on_true'0; auto with coc core arith sets; intros.
    elim H5 with on_false'0; auto with coc core arith sets; intros.
    elim H7 with bool'0; auto with coc core arith sets; intros.
    exists (BoolRec x0 x1 x2 x3); auto with coc core arith sets.
    subst z; subst bool; subst on_false0; subst on_true0; subst choice0.
    elim H3 with on_true'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    inversion_clear H6; auto with coc core arith sets.
    subst z; subst bool; subst on_false0; subst on_true0; subst choice0.
    elim H5 with on_false'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    inversion_clear H6; auto with coc core arith sets.

    inversion H2.
    subst choice0; subst on_true0; subst on_false0; subst bool; subst z.
    elim H1 with on_true'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    inversion_clear H11; auto with coc core arith sets.
    subst choice0; subst on_true0; subst on_false0; subst z.
    elim H1 with on_true'0; auto with coc core arith sets; intros.

    inversion H2.
    subst choice0; subst on_true0; subst on_false0; subst bool; subst z.
    elim H1 with on_false'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    inversion_clear H11; auto with coc core arith sets.
    subst choice0; subst on_true0; subst on_false0; subst z.
    elim H1 with on_false'0; auto with coc core arith sets; intros.

    inversion H12.
    subst z; subst val0; subst on_right0; subst on_left0; subst choice0; subst right_pred0; subst left_pred0.
    elim H1 with left_pred'0; auto with coc core arith sets; intros.
    elim H3 with right_pred'0; auto with coc core arith sets; intros.
    elim H5 with choice'0; auto with coc core arith sets; intros.
    elim H7 with on_left'0; auto with coc core arith sets; intros.
    elim H9 with on_right'0; auto with coc core arith sets; intros.
    elim H11 with val'0; auto with coc core arith sets; intros.
    exists (SumBoolInd x0 x1 x2 x3 x4 x5); auto with coc core arith sets.
    subst z; subst val; subst on_right0; subst on_left0; subst choice0; subst right_pred_a; subst left_pred_a.
    elim H7 with on_left'0; auto with coc core arith sets; intros.
    inversion H10.
    subst proof0; subst right_pred0; subst left_pred0; subst val'.
    elim H11 with (SumBoolLeft left_pred'0 right_pred'0 proof'); auto with coc core arith sets; intros.
    inversion H16.
    subst x1; subst proof0; subst right_pred0; subst left_pred0.
    exists (App x0 proof'1); auto with coc core arith sets.
    inversion_clear H15; auto with coc core arith sets.
    subst left_pred_a; subst right_pred_a; subst choice0; subst on_left0; subst on_right0; subst val; subst z.
    inversion H10.
    subst left_pred0; subst right_pred0; subst proof0; subst val'.
    elim H9 with on_right'0; auto with coc core arith sets; intros.
    elim H11 with (SumBoolRight left_pred'0 right_pred'0 proof'); auto with coc core arith sets; intros.
    inversion H17.
    subst left_pred0; subst right_pred0; subst proof0; subst x1.
    inversion_clear H15; exists (App x0 proof'1); auto with coc core arith sets.
    inversion H4.
    subst z; subst val; subst on_right0; subst on_left0; subst choice0; subst right_pred_a; subst left_pred_a.
    inversion H17.
    subst left_pred0; subst right_pred0; subst proof0; subst val'.
    elim H1 with on_left'0; auto with coc core arith sets; intros.
    elim H3 with proof'0; auto with coc core arith sets; intros.
    exists (App x0 x1); auto with coc core arith sets.
    subst left_pred_a0; subst right_pred_a0; subst choice0; subst on_left0; subst left_pred_b0; subst right_pred_b0; subst proof0; subst z; subst on_right0.
    elim H1 with on_left'0; auto with coc core arith sets; intros.
    elim H3 with proof'0; auto with coc core arith sets; intros.
    exists (App x0 x1); auto with coc core arith sets.
    inversion H4.
    subst left_pred_a; subst right_pred_a; subst choice0; subst on_left0; subst on_right0; subst val; subst z.
    inversion H17.
    subst left_pred0; subst right_pred0; subst proof0; subst val'.
    elim H1 with on_right'0; auto with coc core arith sets; intros.
    elim H3 with proof'0; auto with coc core arith sets; intros.
    exists (App x0 x1); auto with coc core arith sets.
    subst left_pred_a0; subst right_pred_a0; subst choice0; subst on_left0; subst on_right0; subst left_pred_b0; subst right_pred_b0; subst proof0; subst z.
    elim H1 with on_right'0; auto with coc core arith sets; intros.
    elim H3 with proof'0; auto with coc core arith sets; intros.
    exists (App x0 x1); auto with coc core arith sets.

    inversion H12.
    subst z; subst val0; subst on_right0; subst on_left0; subst choice0; subst right_pred0; subst left_pred0.
    elim H1 with left_pred'0; auto with coc core arith sets; intros.
    elim H3 with right_pred'0; auto with coc core arith sets; intros.
    elim H5 with choice'0; auto with coc core arith sets; intros.
    elim H7 with on_left'0; auto with coc core arith sets; intros.
    elim H9 with on_right'0; auto with coc core arith sets; intros.
    elim H11 with val'0; auto with coc core arith sets; intros.
    exists (SumBoolRec x0 x1 x2 x3 x4 x5); auto with coc core arith sets.
    subst z; subst val; subst on_right0; subst on_left0; subst choice0; subst right_pred_a; subst left_pred_a.
    elim H7 with on_left'0; auto with coc core arith sets; intros.
    inversion H10.
    subst proof0; subst right_pred0; subst left_pred0; subst val'.
    elim H11 with (SumBoolLeft left_pred'0 right_pred'0 proof'); auto with coc core arith sets; intros.
    inversion H16.
    subst x1; subst proof0; subst right_pred0; subst left_pred0.
    exists (App x0 proof'1); auto with coc core arith sets.
    inversion_clear H15; auto with coc core arith sets.
    subst left_pred_a; subst right_pred_a; subst choice0; subst on_left0; subst on_right0; subst val; subst z.
    inversion H10.
    subst left_pred0; subst right_pred0; subst proof0; subst val'.
    elim H9 with on_right'0; auto with coc core arith sets; intros.
    elim H11 with (SumBoolRight left_pred'0 right_pred'0 proof'); auto with coc core arith sets; intros.
    inversion H17.
    subst left_pred0; subst right_pred0; subst proof0; subst x1.
    inversion_clear H15; exists (App x0 proof'1); auto with coc core arith sets.
    inversion H4.
    subst z; subst val; subst on_right0; subst on_left0; subst choice0; subst right_pred_a; subst left_pred_a.
    inversion H17.
    subst left_pred0; subst right_pred0; subst proof0; subst val'.
    elim H1 with on_left'0; auto with coc core arith sets; intros.
    elim H3 with proof'0; auto with coc core arith sets; intros.
    exists (App x0 x1); auto with coc core arith sets.
    subst left_pred_a0; subst right_pred_a0; subst choice0; subst on_left0; subst left_pred_b0; subst right_pred_b0; subst proof0; subst z; subst on_right0.
    elim H1 with on_left'0; auto with coc core arith sets; intros.
    elim H3 with proof'0; auto with coc core arith sets; intros.
    exists (App x0 x1); auto with coc core arith sets.
    inversion H4.
    subst left_pred_a; subst right_pred_a; subst choice0; subst on_left0; subst on_right0; subst val; subst z.
    inversion H17.
    subst left_pred0; subst right_pred0; subst proof0; subst val'.
    elim H1 with on_right'0; auto with coc core arith sets; intros.
    elim H3 with proof'0; auto with coc core arith sets; intros.
    exists (App x0 x1); auto with coc core arith sets.
    subst left_pred_a0; subst right_pred_a0; subst choice0; subst on_left0; subst on_right0; subst left_pred_b0; subst right_pred_b0; subst proof0; subst z.
    elim H1 with on_right'0; auto with coc core arith sets; intros.
    elim H3 with proof'0; auto with coc core arith sets; intros.
    exists (App x0 x1); auto with coc core arith sets.

    inversion_clear H4.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with property'0; auto with coc core arith sets; intros.
    exists (Refine x0 x1); auto with coc core arith sets.

    inversion_clear H8.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with property'0; auto with coc core arith sets; intros.
    elim H5 with val'0; auto with coc core arith sets; intros.
    elim H7 with proof'0; auto with coc core arith sets; intros.
    exists (RefineConstr x0 x1 x2 x3); auto with coc core arith sets.

    inversion H6.
    subst type0; subst property0; subst ref0; subst z.    
    elim H1 with type'0; auto with coc; intros.
    elim H3 with property'0; auto with coc; intros.
    elim H5 with ref'0; auto with coc; intros.
    exists (RefineProjVal x0 x1 x2); auto with coc core arith sets.
    subst z; subst ref; subst property_a; subst type_a.
    inversion H4.
    subst proof0; subst val0; subst property0; subst type0; subst ref'.
    elim H5 with (RefineConstr type'0 property'0 val' proof'); auto with coc core arith sets; intros.
    inversion H8.
    subst x0; subst proof0; subst val0; subst property0; subst type0.
    exists val'1; auto with coc core arith sets.
    inversion_clear H7; auto with coc core arith sets.

    inversion H6.
    subst type0; subst property0; subst ref0; subst z.    
    elim H1 with type'0; auto with coc; intros.
    elim H3 with property'0; auto with coc; intros.
    elim H5 with ref'0; auto with coc; intros.
    exists (RefineProjProof x0 x1 x2); auto with coc core arith sets.
    subst z; subst ref; subst property_a; subst type_a.
    inversion H4.
    subst proof0; subst val0; subst property0; subst type0; subst ref'.
    elim H5 with (RefineConstr type'0 property'0 val' proof'); auto with coc core arith sets; intros.
    inversion H8.
    subst x0; subst proof0; subst val0; subst property0; subst type0.
    exists proof'1; auto with coc core arith sets.
    inversion_clear H7; auto with coc core arith sets.

    inversion_clear H2.
    inversion_clear H5.
    elim H1 with val'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    elim H1 with z; auto with coc core arith sets.

    inversion_clear H2.
    inversion_clear H5.
    elim H1 with proof'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    elim H1 with z; auto with coc core arith sets.

    inversion_clear H6.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with l'0; auto with coc core arith sets; intros.
    elim H5 with r'0; auto with coc core arith sets; intros.
    exists (Eq x0 x1 x2); auto with coc core arith sets.

    inversion_clear H4.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with val'0; auto with coc core arith sets; intros.
    exists (EqRefl x0 x1); auto with coc core arith sets.

    inversion H12.
    subst type0; subst l0; subst r0; subst property0; subst impl0; subst proof0; subst z.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with l'0; auto with coc core arith sets; intros.
    elim H5 with r'0; auto with coc core arith sets; intros.
    elim H7 with property'0; auto with coc core arith sets; intros.
    elim H9 with impl'0; auto with coc core arith sets; intros.
    elim H11 with proof'0; auto with coc core arith sets; intros.
    exists (EqInd x0 x1 x2 x3 x4 x5); auto with coc core arith sets.
    subst type_a; subst l0; subst r0; subst property0; subst impl0; subst proof; subst z.
    inversion H10.
    subst type0; subst val0; subst proof'.
    elim H9 with impl'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    inversion H2.
    subst type_a; subst l0; subst r0; subst property0; subst impl0; subst proof; subst z.
    inversion H15.
    subst type0; subst val0; subst proof'.
    elim H1 with impl'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    subst l0; subst r0; subst property0; subst impl0; subst type_a0; subst type_b0; subst val0; subst z.
    elim H1 with impl'0; auto with coc core arith sets.

    inversion H12.
    subst type0; subst l0; subst r0; subst property0; subst impl0; subst proof0; subst z.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with l'0; auto with coc core arith sets; intros.
    elim H5 with r'0; auto with coc core arith sets; intros.
    elim H7 with property'0; auto with coc core arith sets; intros.
    elim H9 with impl'0; auto with coc core arith sets; intros.
    elim H11 with proof'0; auto with coc core arith sets; intros.
    exists (EqRec x0 x1 x2 x3 x4 x5); auto with coc core arith sets.
    subst type_a; subst l0; subst r0; subst property0; subst impl0; subst proof; subst z.
    inversion H10.
    subst type0; subst val0; subst proof'.
    elim H9 with impl'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    inversion H2.
    subst type_a; subst l0; subst r0; subst property0; subst impl0; subst proof; subst z.
    inversion H15.
    subst type0; subst val0; subst proof'.
    elim H1 with impl'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    subst l0; subst r0; subst property0; subst impl0; subst type_a0; subst type_b0; subst val0; subst z.
    elim H1 with impl'0; auto with coc core arith sets.

    inversion_clear H0.
    exists Falsity; auto with coc core arith sets.

    inversion_clear H4.
    elim H1 with proof'0; auto with coc core arith sets; intros.
    elim H3 with property'0; auto with coc core arith sets; intros.
    exists (FalseInd x0 x1); auto with coc core arith sets.

    inversion_clear H4.
    elim H1 with proof'0; auto with coc core arith sets; intros.
    elim H3 with property'0; auto with coc core arith sets; intros.
    exists (FalseRec x0 x1); auto with coc core arith sets.

    inversion_clear H0.
    exists Unit; auto with coc core arith sets.

    inversion_clear H0.
    exists Nil; auto with coc core arith sets.

    inversion H10.
    subst type0; subst rel0; subst choice0; subst f0; subst proof0; subst z.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with rel'0; auto with coc core arith sets; intros.
    elim H5 with choice'0; auto with coc core arith sets; intros.
    elim H7 with f'0; auto with coc core arith sets; intros.
    elim H9 with proof'0; auto with coc core arith sets; intros.
    exists (WFrec x0 x1 x2 x3 x4); auto with coc core arith sets.
    subst z; subst proof0; subst f0; subst choice0; subst rel0; subst type0.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with rel'0; auto with coc core arith sets; intros.
    elim H5 with choice'0; auto with coc core arith sets; intros.
    elim H7 with f'0; auto with coc core arith sets; intros.
    elim H9 with proof'0; auto with coc core arith sets; intros.
    exists (
      Abs x0 
      (
        AccRec 
        (lift 1 x0)
        (lift 1 x1)
        (lift 1 x2)
        (
          Abs (lift 1 x0) (
            Abs (
              Prod (lift 2 x0)
              (
                Prod (App (App (lift 3 x1) (Ref 0)) (Ref 1))
                (App (lift 4 x2) (Ref 1))
              )
            ) (
              App (App (lift 3 x3) (Ref 1))
              (
                Abs (
                  Refine
                  (lift 3 x0)
                  (Abs (lift 3 x0) (App (App (lift 4 x1) (Ref 0)) (Ref 3)))
                )
                (
                  App 
                  (
                    App (Ref 1) 
                    (RefineProjVal (lift 4 x0) (Abs (lift 4 x0) (App (App (lift 5 x1) (Ref 0)) (Ref 3))) (Ref 0))
                  ) 
                  (RefineProjProof (lift 4 x0) (Abs (lift 4 x0) (App (App (lift 5 x1) (Ref 0)) (Ref 3))) (Ref 0)) 
                )
              )
            )  
          )
        )
        (Ref 0)
        (App (lift 1 x4) (Ref 0))
      )
    ); auto with coc core arith sets.
    unfold lift; auto 15 with coc core arith sets.

    inversion H10.
    subst type0; subst rel0; subst choice0; subst f0; subst proof0; subst z.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with rel'0; auto with coc core arith sets; intros.
    elim H5 with choice'0; auto with coc core arith sets; intros.
    elim H7 with f'0; auto with coc core arith sets; intros.
    elim H9 with proof'0; auto with coc core arith sets; intros.
    exists (
      Abs x0 
      (
        AccRec 
        (lift 1 x0)
        (lift 1 x1)
        (lift 1 x2)
        (
          Abs (lift 1 x0) (
            Abs (
              Prod (lift 2 x0)
              (
                Prod (App (App (lift 3 x1) (Ref 0)) (Ref 1))
                (App (lift 4 x2) (Ref 1))
              )
            ) (
              App (App (lift 3 x3) (Ref 1))
              (
                Abs (
                  Refine
                  (lift 3 x0)
                  (Abs (lift 3 x0) (App (App (lift 4 x1) (Ref 0)) (Ref 3)))
                )
                (
                  App 
                  (
                    App (Ref 1) 
                    (RefineProjVal (lift 4 x0) (Abs (lift 4 x0) (App (App (lift 5 x1) (Ref 0)) (Ref 3))) (Ref 0))
                  ) 
                  (RefineProjProof (lift 4 x0) (Abs (lift 4 x0) (App (App (lift 5 x1) (Ref 0)) (Ref 3))) (Ref 0)) 
                )
              )
            )  
          )
        )
        (Ref 0)
        (App (lift 1 x4) (Ref 0))
      )
    ); auto with coc core arith sets.
    unfold transp; unfold lift; auto 15 with coc core arith sets.
    subst z; subst proof0; subst f0; subst choice0; subst rel0; subst type0.
    elim H1 with type'0; auto with coc core arith sets; intros.
    elim H3 with rel'0; auto with coc core arith sets; intros.
    elim H5 with choice'0; auto with coc core arith sets; intros.
    elim H7 with f'0; auto with coc core arith sets; intros.
    elim H9 with proof'0; auto with coc core arith sets; intros.
    exists (
      Abs x0 
      (
        AccRec 
        (lift 1 x0)
        (lift 1 x1)
        (lift 1 x2)
        (
          Abs (lift 1 x0) (
            Abs (
              Prod (lift 2 x0)
              (
                Prod (App (App (lift 3 x1) (Ref 0)) (Ref 1))
                (App (lift 4 x2) (Ref 1))
              )
            ) (
              App (App (lift 3 x3) (Ref 1))
              (
                Abs (
                  Refine
                  (lift 3 x0)
                  (Abs (lift 3 x0) (App (App (lift 4 x1) (Ref 0)) (Ref 3)))
                )
                (
                  App 
                  (
                    App (Ref 1) 
                    (RefineProjVal (lift 4 x0) (Abs (lift 4 x0) (App (App (lift 5 x1) (Ref 0)) (Ref 3))) (Ref 0))
                  ) 
                  (RefineProjProof (lift 4 x0) (Abs (lift 4 x0) (App (App (lift 5 x1) (Ref 0)) (Ref 3))) (Ref 0)) 
                )
              )
            )  
          )
        )
        (Ref 0)
        (App (lift 1 x4) (Ref 0))
      )
    ); auto with coc core arith sets.
    unfold transp; unfold lift; auto 15 with coc core arith sets.
    unfold transp; unfold lift; auto 15 with coc core arith sets.

    inversion H6.
    subst on_true0; subst on_false0; subst val0; subst z.
    elim H1 with on_true'0; auto with coc core arith sets; intros.
    elim H3 with on_false'0; auto with coc core arith sets; intros.
    elim H5 with val'0; auto with coc core arith sets; intros.
    exists (BoolPropChoice x0 x1 x2); auto with coc core arith sets.
    subst on_true0; subst on_false0; subst val; subst z.
    elim H1 with on_true'0; auto with coc core arith sets; intros.
    inversion_clear H4.
    exists x0; auto with coc core arith sets.
    subst z; subst val; subst on_false0; subst on_true0.
    elim H3 with on_false'0; auto with coc core arith sets; intros.
    inversion_clear H4.
    exists x0; auto with coc core arith sets.
    inversion_clear H2.
    elim H1 with on_true'0; auto with coc core arith sets; intros.
    inversion_clear H5.
    exists x0; auto with coc core arith sets.
    elim H1 with z; auto with coc core arith sets.
    inversion_clear H2.
    inversion_clear H5.
    elim H1 with on_false'0; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    elim H1 with z; auto with coc core arith sets.
  Qed.

  (*
    Strip lemma is a lemma useful in proving confluence of multistep
    the parallel reduction. It becomes much more obvious
    what it is about when you look at the diagram. 
    We later restate it using commutation with transposition.
  *)
  Lemma strip_lemma : commut _ par_red (transp _ par_red1).
  Proof.
    unfold commut, par_red in |- *; simple induction 1; intros.
    elim str_confluence_par_red1 with z x0 y0; auto with coc core arith sets;
    intros.
    exists x1; auto with coc core arith sets.

    elim H1 with z0; auto with coc core arith sets; intros.
    elim H3 with x1; intros; auto with coc core arith sets.
    exists x2; auto with coc core arith sets.
    apply t_trans with x1; auto with coc core arith sets.
  Qed.


  (*
    Multistep parallel reduction is confluent too.
  *)
  Corollary confluence_par_red : str_confluent par_red.
  Proof.
    red in |- *; red in |- *.
    simple induction 1; intros.
    elim strip_lemma with z x0 y0; intros; auto with coc core arith sets.
    exists x1; auto with coc core arith sets.

    elim H1 with z0; intros; auto with coc core arith sets.
    elim H3 with x1; intros; auto with coc core arith sets.
    exists x2; auto with coc core arith sets.
    red in |- *.
    apply t_trans with x1; auto with coc core arith sets.
  Qed.


  (* Multistep reduction is confluent! *)
  Corollary confluence_red : str_confluent red.
  Proof.
    red in |- *; red in |- *.
    intros.
    elim confluence_par_red with x y z; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
  Qed.


  (* 
    Church Rosser property. The man himself.
    We state that if two terms are convertible then
    they can be reduced to the same value.
  *)
  Theorem church_rosser :
    forall u v, conv u v -> ex2 (fun t => red u t) (fun t => red v t).
  Proof.
    simple induction 1; intros.
    exists u; auto with coc core arith sets.

    elim H1; intros.
    elim confluence_red with x P N; auto with coc core arith sets; intros.
    exists x0; auto with coc core arith sets.
    apply trans_red_red with x; auto with coc core arith sets.

    elim H1; intros.
    exists x; auto with coc core arith sets.
    apply trans_red_red with P; auto with coc core arith sets.
  Qed.



  (*
    If two proucts are convertible then
    their domains are cinvertible too.
  *)
  Lemma inv_conv_prod_l :
    forall a b c d : term, conv (Prod a c) (Prod b d) -> conv a b.
  Proof.
    intros.
    elim church_rosser with (Prod a c) (Prod b d); intros;
    auto with coc core arith sets.
    apply red_prod_prod with a c x; intros; auto with coc core arith sets.
    apply red_prod_prod with b d x; intros; auto with coc core arith sets.
    apply trans_conv_conv with a0; auto with coc core arith sets.
    apply sym_conv.
    generalize H2.
    rewrite H5; intro.
    injection H8.
    simple induction 2; auto with coc core arith sets.
  Qed.

  (*
    If two products are convertible
    then their ranges are convertible too.
  *)
  Lemma inv_conv_prod_r :
   forall a b c d : term, conv (Prod a c) (Prod b d) -> conv c d.
  Proof.
    intros.
    elim church_rosser with (Prod a c) (Prod b d); intros;
    auto with coc core arith sets.
    apply red_prod_prod with a c x; intros; auto with coc core arith sets.
    apply red_prod_prod with b d x; intros; auto with coc core arith sets.
    apply trans_conv_conv with b0; auto with coc core arith sets.
    apply sym_conv.
    generalize H2.
    rewrite H5; intro.
    injection H8.
    simple induction 1; auto with coc core arith sets.
  Qed.


  (*
    We also proof that if two normal forms
    are convertible to each other then they
    are equal.
  *)
  Lemma nf_uniqueness : forall u v, conv u v -> normal u -> normal v -> u = v. 
  Proof.
    intros.
    elim church_rosser with u v; intros; auto with coc core arith sets.
    rewrite (red_normal u x); auto with coc core arith sets.
    elim red_normal with v x; auto with coc core arith sets.
  Qed.


  (* 
    If a sort is converitble to another sort
    then this is the sort itself.
  *)
  Lemma conv_sort : forall s1 s2, conv (Srt s1) (Srt s2) -> s1 = s2.
  Proof.
    intros.
    cut (Srt s1 = Srt s2); intros.
    injection H0; auto with coc core arith sets.

    apply nf_uniqueness; auto with coc core arith sets.
    red in |- *; red in |- *; intros.
    inversion_clear H0.

    red in |- *; red in |- *; intros.
    inversion_clear H0.
  Qed.


  Corollary conv_kind_prop : ~ conv (Srt kind) (Srt prop).
  Proof.
    red in |- *; intro.
    absurd (kind = prop).
    discriminate.

    apply conv_sort; auto with coc core arith sets.
  Qed.


  Corollary conv_sort_prod : forall s t u, ~ conv (Srt s) (Prod t u).
  Proof.
    red in |- *; intros.
    elim church_rosser with (Srt s) (Prod t u); auto with coc core arith sets.
    do 2 intro.
    elim red_normal with (Srt s) x; auto with coc core arith sets.
    intro.
    apply red_prod_prod with t u (Srt s); auto with coc core arith sets; intros.
    discriminate H2.

    red in |- *; red in |- *; intros.
    inversion_clear H1.
  Qed.

End Church_Rosser.
