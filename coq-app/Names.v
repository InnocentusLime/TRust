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
  Here we define the concept of a "name", which is an `ml_string`.
*)

Require Import Arith.
Require Import MyList.
Require Export MlTypes.


(* The type of name *)
Definition name := ml_string.
(* List of names *)
Definition prt_names := list name.

(* Equality of two names is decidable *)
Definition name_dec : forall x y : name, {x = y} + {x <> y}
:= ml_eq_string.

(* Conversion of a `nat` to `name` *)
Definition var_of_nat (n : nat) : name := ml_x_int (int_of_nat n).

(* This conversion is injective *)
Lemma inj_var_of_nat :
  forall m n : nat, var_of_nat m = var_of_nat n -> m = n
.
Proof.
  unfold var_of_nat in |- *.
  intros.
  apply dangerous_int_injection.
  apply ml_x_int_inj; auto with coc core arith datatypes.
Qed.


(* Ordering on lists of names? *)
Inductive ord_insert : list name -> list name -> Prop :=
| oi_intro :
  forall (x : name) (n : nat) (l1 l2 : list name),
  insert _ x n l1 l2 -> ord_insert l1 l2
.


(* This order is well-founded *)
Lemma wf_oi : well_founded ord_insert.
Proof.
  cut (forall (n : nat) (l : list name), length l = n -> Acc ord_insert l).
  red in |- *; intros.
  apply H with (length a); auto with coc core arith datatypes.

  simple induction n.
  simple destruct l; intros.
  apply Acc_intro; intros.
  inversion_clear H0.
  inversion_clear H1.

  discriminate H.

  simple destruct l; simpl in |- *; intros.
  discriminate H0.

  injection H0; intros.
  apply Acc_intro; intros.
  inversion_clear H2.
  apply H.
  cut (S (length y) = length (n1 :: l0)); intros.
  simpl in H2.
  injection H2; auto with coc core arith datatypes.
  elim H1; auto with coc core arith datatypes.

  elim H3; auto with coc core arith datatypes.
  intros.
  simpl in |- *.
  elim H4; auto with coc core arith datatypes.
Qed.


(* This is a certified function which removes a name from a list *)
Definition rmv :
  forall (x : name) (l : prt_names),
  {l1 : prt_names | exists n : nat, insert _ x n l1 l} + {~ In _ x l}
.
Proof.
  refine
  (fix rmv (x : name) (l : prt_names) {struct l} :
      {l1 : prt_names | exists n : nat, insert _ x n l1 l} + {~ In _ x l} :=
      match
        l
        return
          ({l1 : prt_names | exists n : nat, insert _ x n l1 l} + {~ In _ x l})
      with
      | nil => inright _ _
      | y :: l1 =>
          match name_dec x y with
          | left found => inleft _ (exist _ l1 _)
          | right notfound =>
              match rmv x l1 with
              | inleft (exist v rmvd) => inleft _ (exist _ (y :: v) _)
              | inright notin => inright _ _
              end
          end
      end).
  red in |- *; intros.
  inversion H.

  rewrite found.
  exists 0; trivial with coc.

  inversion_clear rmvd.
  exists (S x0); auto with coc core arith datatypes.

  red in |- *; intros; apply notin.
  inversion H; auto with coc core arith datatypes.
  elim notfound; trivial.
Defined.



(* This certified function can find the unused and is also bigger than `n` *)
Definition find_free :
  forall (l : prt_names) (n : nat),
  { m : nat | n <= m & ~ In _ (var_of_nat m) l }
.
Proof.
  intro l.
  apply Acc_rec with (R := ord_insert) (x := l).
  2: apply wf_oi.
  clear l.
  intros l acc_hyp ffv n.
  refine
  match rmv (var_of_nat n) l with
  | inleft (exist l1 rmvd as s) =>
    match ffv l1 _ (S n) with
    | exist2 m m_le m_notin => exist2 _ _ m _ _
    end
  | inright fresh => exist2 _ _ n _ _
  end; auto with arith.
  inversion_clear rmvd.
  eapply oi_intro; eauto.

  red in |- *; intro.
  apply m_notin.
  inversion_clear rmvd.
  generalize H0; clear H0.
  cut (var_of_nat m <> var_of_nat n).
  generalize x l1.
  elim H; unfold var_of_nat in |- *; intros.
  inversion H1; auto with coc.
  elim H0; auto.

  inversion H3; auto with coc.
  constructor; eauto.

  red in |- *; intros.
  apply (le_Sn_n n).
  pattern n at 2 in |- *.
  replace n with m; auto with coc core arith datatypes.
  apply inj_var_of_nat; auto with coc core arith datatypes.
Defined.



(* Then we proof that it is possible to find a free name *)
Definition find_free_var : forall l : prt_names, {x : name | ~ In _ x l}.
Proof.
  intros.
  elim (find_free l 0); intros; auto with coc.
  exists (var_of_nat x); trivial.
Defined.


(* Condition for list to have unique names *)
Definition name_unique l := forall (m n : nat) (x : name), item _ x l m -> item _ x l n -> m = n.


(* A lemma for extending a unique list with a name *)
Lemma fv_ext :
  forall l : prt_names, name_unique l -> 
  forall x : name, ~ In _ x l -> 
  name_unique (x :: l)
.
Proof.
  unfold name_unique in |- *; intros.
  generalize H2.
  inversion_clear H1; intros.
  inversion_clear H1; auto with coc core arith datatypes.
  elim H0.
  elim H3; auto with coc core arith datatypes.

  generalize H3.
  inversion_clear H1; intros.
  elim H0.
  elim H1; auto with coc core arith datatypes.

  elim H with n1 n0 x0; auto with coc core arith datatypes.
Qed.


(* 
  If `x` is an item of list `l` at position `n` and `l` is a 
  unique list then the first item in `l` equal to `x` is at
  position `x`
*)
Lemma name_unique_first :
  forall (x : name) (l : prt_names) (n : nat),
  item _ x l n -> name_unique l -> first_item _ x l n
.
Proof.
  simple induction 1; intros.
  auto with coc core arith datatypes.

  apply fit_tl; auto with coc core arith datatypes.
  apply H1.
  red in |- *; intros.
  cut (S m = S n1); intros.
  injection H5; auto with coc core arith datatypes.

  elim H2 with (S m) (S n1) x0; auto with coc core arith datatypes.

  red in |- *; intros.
  cut (0 = S n0); intros.
  discriminate H4.

  elim H2 with 0 (S n0) x; auto with coc core arith datatypes.
  rewrite H3; auto with coc core arith datatypes.
Qed.
