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
  Here we defining the heart of out system -- the typing of DeBrujin terms.

  TODO: shortned proofs?
*)

Require Import Termes.
Require Import Conv.
Require Export MyList.

Implicit Types i k m n p : nat.
Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Definition env := list term.

Implicit Types e f g : env.

Definition item_lift t e n :=
  ex2 (fun u => t = lift (S n) u) (fun u => item term u (e:list term) n)
.

Section Typage.

  (* Our typing is mutually inductive with definition of a well-formed context *)
  Inductive wf : env -> Prop :=
  | wf_nil : wf nil
  | wf_var : forall e T s, typ e T (Srt s) -> wf (T :: e) (* That is another bruh moment, because you don't lift items when you push them *)
  with typ : env -> term -> term -> Prop :=
  | type_prop : forall e, wf e -> typ e (Srt prop) (Srt kind)
  | type_set : forall e, wf e -> typ e (Srt set) (Srt kind)
  | type_var :
      forall e,
      wf e -> forall (v : nat) t, item_lift t e v -> typ e (Ref v) t (* Instead the items get lifted afterwards... I guess that's more convinient? *)
  | type_abs :
      forall e T s1,
      typ e T (Srt s1) ->
      forall M (U : term) s2,
      typ (T :: e) U (Srt s2) ->
      typ (T :: e) M U -> typ e (Abs T M) (Prod T U)
  | type_app :
      forall e v (V : term),
      typ e v V ->
      forall u (Ur : term),
      typ e u (Prod V Ur) -> typ e (App u v) (subst v Ur)
  | type_prod :
      forall e T s1,
      typ e T (Srt s1) ->
      forall (U : term) s2,
      typ (T :: e) U (Srt s2) -> typ e (Prod T U) (Srt s2)
  | type_conv :
      forall e t (U V : term),
      typ e t U -> conv U V -> forall s, typ e V (Srt s) -> typ e t V
  (* Additional stuff *)
  | type_nat : forall e, wf e -> typ e Nat (Srt set)
  | type_nat_o : forall e, wf e -> typ e NatO Nat
  | type_nat_succ : forall e x, typ e x Nat -> typ e (NatSucc x) Nat
  | type_nat_destruct : 
    forall e x1 x2 x3 x4, 
    typ e x1 (Prod Nat (Srt set)) ->
    typ e x2 (App x1 NatO) ->
    typ e x3 
    (
      Prod Nat 
      (
        App 
        (lift 1 x1) 
        (NatSucc (Ref 0))
      )
    ) ->
    typ e x4 Nat ->
    typ e (NatDestruct x1 x2 x3 x4) (App x1 x4)
  | type_nat_cases : 
    forall e x1 x2 x3 x4, 
    typ e x1 (Prod Nat (Srt prop)) ->
    typ e x2 (App x1 NatO) ->
    typ e x3 
    (
      Prod Nat ( App (lift 1 x1) (NatSucc (Ref 0)))
    ) ->
    typ e x4 Nat ->
    typ e (NatCases x1 x2 x3 x4) (App x1 x4)
  | type_nat_rec :
    forall e x1 x2 x3 x4,
    typ e x1 (Prod Nat (Srt set)) ->
    typ e x2 (App x1 NatO) ->
    typ e x3
    (
      Prod Nat
      (
        Prod
        (App (lift 1 x1) (Ref 0))
        (App (lift 2 x1) (NatSucc (Ref 1)))
      )
    ) -> 
    typ e x4 Nat ->
    typ e (NatRec x1 x2 x3 x4) (App x1 x4)
  | type_nat_ind :
    forall e x1 x2 x3 x4,
    typ e x1 (Prod Nat (Srt prop)) ->
    typ e x2 (App x1 NatO) ->
    typ e x3
    (
      Prod Nat
      (
        Prod
        (App (lift 1 x1) (Ref 0))
        (App (lift 2 x1) (NatSucc (Ref 1)))
      )
    ) -> 
    typ e x4 Nat ->
    typ e (NatInd x1 x2 x3 x4) (App x1 x4)
  | type_acc_prop :
    forall e x1 x2 x3,
    typ e x1 (Srt set) ->
    typ e x2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
    typ e x3 x1 ->
    typ e (AccProp x1 x2 x3) (Srt prop)
  | type_acc_intro :
    forall e x1 x2 x3 x4,
    typ e x1 (Srt set) ->
    typ e x2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
    typ e x3 x1 ->
    typ e x4
    (
      Prod x1
      (
        Prod (App (App (lift 1 x2) (Ref 0)) (lift 1 x3))
        (AccProp (lift 2 x1) (lift 2 x2) (Ref 1))
      )
    ) ->
    typ e (AccIntro x1 x2 x3 x4) (AccProp x1 x2 x3)
  | type_acc_rec :
    forall e x1 x2 x3 x4 x5 x6,
    typ e x1 (Srt set) ->
    typ e x2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
    typ e x3 (Prod x1 (Srt set)) ->
    typ e x4 
    (
      Prod x1 
      (
        Prod
        (
          Prod (lift 1 x1) 
          (
            Prod (App (App (lift 2 x3) (Ref 0)) (Ref 0))
            (App (lift 3 x3) (Ref 1))
          )
        )
        (App (lift 2 x3) (Ref 1))
      )
    ) -> 
    typ e x5 x1 ->
    typ e x6 (AccProp x1 x2 x5) ->
    typ e (AccRec x1 x2 x3 x4 x5 x6) (App x3 x5)
  | type_acc_ind :
    forall e x1 x2 x3 x4 x5 x6,
    typ e x1 (Srt set) ->
    typ e x2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
    typ e x3 (Prod x1 (Srt prop)) ->
    typ e x4 
    (
      Prod x1 
      (
        Prod
        (
          Prod (lift 1 x1) 
          (
            Prod (App (App (lift 2 x3) (Ref 0)) (Ref 0))
            (App (lift 3 x3) (Ref 1))
          )
        )
        (App (lift 2 x3) (Ref 1))
      )
    ) -> 
    typ e x5 x1 ->
    typ e x6 (AccProp x1 x2 x5) ->
    typ e (AccInd x1 x2 x3 x4 x5 x6) (App x3 x5)
  | type_le :
    forall e x1 x2,
    typ e x1 Nat ->
    typ e x2 Nat ->
    typ e (Le x1 x2) (Srt prop)
  | type_le_n :
    forall e x,
    typ e x Nat ->
    typ e (LeN x) (Le x x)
  | type_le_s :
    forall e x1 x2 x3,
    typ e x1 Nat ->
    typ e x2 Nat ->
    typ e x3 (Le x1 x2) ->
    typ e (LeS x1 x2 x3) (Le x1 (NatSucc x2))
  | type_le_cases :
    forall e x1 x2 x3 x4 x5 x6,
    typ e x1 (Prod Nat (Srt prop)) ->
    typ e x2 (App x1 x4) ->
    typ e x3 
    (
      Prod Nat 
      (
        Prod 
        (Le (lift 1 x4) (Ref 0)) 
        (
          App (lift 2 x1) (NatSucc (Ref 1))
        )
      )
    ) ->
    typ e x4 Nat ->
    typ e x5 Nat ->
    typ e x6 (Le x4 x5) ->
    typ e (LeCases x1 x2 x3 x4 x5 x6) (App x1 x5)
  | type_le_ind :
    forall e x1 x2 x3 x4 x5 x6,
    typ e x1 (Prod Nat (Srt prop)) ->
    typ e x2 (App x1 x4) ->
    typ e x3 
    (
      Prod Nat 
      (
        Prod 
        (Le (lift 1 x4) (Ref 0)) 
        (
          Prod
          (App (lift 2 x1) (Ref 1))
          (App (lift 3 x1) (NatSucc (Ref 2)))
        )
      )
    ) ->
    typ e x4 Nat ->
    typ e x5 Nat ->
    typ e x6 (Le x4 x5) ->
    typ e (LeInd x1 x2 x3 x4 x5 x6) (App x1 x5)
  | type_bool : forall e, wf e -> typ e Bool (Srt set)
  | type_sumbool :
    forall e x1 x2,
    typ e x1 (Srt prop) ->
    typ e x2 (Srt prop) ->
    typ e (SumBool x1 x2) (Srt set)
  | type_bool_true : forall e, wf e -> typ e BoolTrue Bool
  | type_bool_false : forall e, wf e -> typ e BoolFalse Bool
  | type_sumbool_left :
    forall e x1 x2 x3,
    typ e x1 (Srt prop) ->
    typ e x2 (Srt prop) ->
    typ e x3 x1 ->
    typ e (SumBoolLeft x1 x2 x3) (SumBool x1 x2)
  | type_sumbool_right :
    forall e x1 x2 x3,
    typ e x1 (Srt prop) ->
    typ e x2 (Srt prop) ->
    typ e x3 x2 ->
    typ e (SumBoolRight x1 x2 x3) (SumBool x1 x2)
  | type_bool_ind :
    forall e x1 x2 x3 x4,
    typ e x1 (Prod Bool (Srt prop)) ->
    typ e x2 (App x1 BoolTrue) ->
    typ e x3 (App x1 BoolFalse) ->
    typ e x4 Bool ->
    typ e (BoolInd x1 x2 x3 x4) (App x1 x4)
  | type_bool_rec :
    forall e x1 x2 x3 x4,
    typ e x1 (Prod Bool (Srt set)) ->
    typ e x2 (App x1 BoolTrue) ->
    typ e x3 (App x1 BoolFalse) ->
    typ e x4 Bool ->
    typ e (BoolRec x1 x2 x3 x4) (App x1 x4)
  | type_sumbool_ind :
    forall e x1 x2 x3 x4 x5 x6,
    typ e x1 (Srt prop) ->
    typ e x2 (Srt prop) ->
    typ e x3 (Prod (SumBool x1 x2) (Srt prop)) ->
    typ e x4 
    (
      Prod x1 
      (
        App (lift 1 x3) 
        (SumBoolLeft (lift 1 x1) (lift 1 x2) (Ref 0))
      )
    ) ->
    typ e x5
    (
      Prod x2
      (
        App (lift 1 x3) 
        (SumBoolRight (lift 1 x1) (lift 1 x2) (Ref 0))
      )
    ) ->
    typ e x6 (SumBool x1 x2) ->
    typ e (SumBoolInd x1 x2 x3 x4 x5 x6) (App x3 x6)
  | type_sumbool_rec :
    forall e x1 x2 x3 x4 x5 x6,
    typ e x1 (Srt prop) ->
    typ e x2 (Srt prop) ->
    typ e x3 (Prod (SumBool x1 x2) (Srt set)) ->
    typ e x4 
    (
      Prod x1 
      (
        App (lift 1 x3) 
        (SumBoolLeft (lift 1 x1) (lift 1 x2) (Ref 0))
      )
    ) ->
    typ e x5
    (
      Prod x2
      (
        App (lift 1 x3) 
        (SumBoolRight (lift 1 x1) (lift 1 x2) (Ref 0))
      )
    ) ->
    typ e x6 (SumBool x1 x2) ->
    typ e (SumBoolRec x1 x2 x3 x4 x5 x6) (App x3 x6)
  | type_refine :
    forall e x1 x2,
    typ e x1 (Srt set) ->
    typ e x2 (Prod x1 (Srt prop)) ->
    typ e (Refine x1 x2) (Srt set)
  | type_refine_constr :
    forall e x1 x2 x3 x4,
    typ e x1 (Srt set) ->
    typ e x2 (Prod x1 (Srt prop)) ->
    typ e x3 x1 ->
    typ e x4 (App x2 x3) ->
    typ e (RefineConstr x1 x2 x3 x4) (Refine x1 x2)
  | type_refine_proj_val :
    forall e x1 x2 x3,
    typ e x1 (Srt set) ->
    typ e x2 (Prod x1 (Srt prop)) ->
    typ e x3 (Refine x1 x2) ->
    typ e (RefineProjVal x1 x2 x3) x1
  | type_refine_proj_proof :
    forall e x1 x2 x3,
    typ e x1 (Srt set) ->
    typ e x2 (Prod x1 (Srt prop)) ->
    typ e x3 (Refine x1 x2) ->
    typ e (RefineProjProof x1 x2 x3) (App x2 (RefineProjVal x1 x2 x3))
  | type_eq :
    forall e x1 x2 x3,
    typ e x1 (Srt set) ->
    typ e x2 x1 ->
    typ e x3 x1 ->
    typ e (Eq x1 x2 x3) (Srt prop)
  | type_eq_refl :
    forall e x1 x2,
    typ e x1 (Srt set) ->
    typ e x2 x1 ->
    typ e (EqRefl x1 x2) (Eq x1 x2 x2)
  | type_eq_ind :
    forall e x1 x2 x3 x4 x5 x6,
    typ e x1 (Srt set) ->
    typ e x2 x1 ->
    typ e x3 x1 ->
    typ e x4 (Prod x1 (Srt prop)) ->
    typ e x5 (App x4 x2) ->
    typ e x6 (Eq x1 x2 x3) ->
    typ e (EqInd x1 x2 x3 x4 x5 x6) (App x4 x3)
  | type_eq_rec :
    forall e x1 x2 x3 x4 x5 x6,
    typ e x1 (Srt set) ->
    typ e x2 x1 ->
    typ e x3 x1 ->
    typ e x4 (Prod x1 (Srt set)) ->
    typ e x5 (App x4 x2) ->
    typ e x6 (Eq x1 x2 x3) ->
    typ e (EqRec x1 x2 x3 x4 x5 x6) (App x4 x3)
  | type_falsity : forall e, wf e -> typ e Falsity (Srt prop)
  | type_false_ind :
    forall e x1 x2,
    typ e x1 Falsity ->
    typ e x2 (Srt prop) ->
    typ e (FalseInd x1 x2) x2
  | type_false_rec :
    forall e x1 x2,
    typ e x1 Falsity ->
    typ e x2 (Srt set) ->
    typ e (FalseRec x1 x2) x2
  | type_unit : forall e, wf e -> typ e Unit (Srt set)
  | type_nil : forall e, wf e -> typ e Nil Unit
  | type_wf_rec :
    forall e x1 x2 x3 x4 x5,
    typ e x1 (Srt set) ->
    typ e x2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
    typ e x3 (Prod x1 (Srt set)) ->
    typ e x4 
    (
      Prod x1
      (
        Prod (
          Refine 
          (lift 1 x1) 
          (
            Abs (lift 1 x1) 
            (App (App (lift 2 x2) (Ref 0)) (Ref 1))
          )
        )
        (App (lift 2 x3) (Ref 1))
      )
    ) ->
    typ e x5 (Prod x1 (AccProp (lift 1 x1) (lift 1 x2) (Ref 0))) ->
    typ e (WFrec x1 x2 x3 x4 x5) (Prod x1 (App (lift 1 x3) (Ref 0)))
  | type_bool_prop_choice :
    forall e x1 x2 x3,
    typ e x1 (Srt prop) ->
    typ e x2 (Srt prop) ->
    typ e x3 Bool ->
    typ e (BoolPropChoice x1 x2 x3) (Srt prop)
  .

  Hint Resolve wf_nil type_prop type_set type_var type_nat type_nat_o type_nat_succ: coc.


  (* Now time for a cool lemma, that both `Set` and `Prop` have type `Kind` *)
  Lemma type_prop_set :
    forall s, is_prop s -> forall e, wf e -> typ e (Srt s) (Srt kind).
  Proof.
    simple destruct 1; intros; rewrite H0.
    apply type_prop; trivial.
    apply type_set; trivial.
  Qed.

  (* The variable `length e` is not used in the term *)
  Lemma typ_free_db : forall e t T, typ e t T -> free_db (length e) t.
  Proof.
    simple induction 1; intros; auto with coc core arith datatypes.
    inversion_clear H1.

    apply db_ref.
    elim H3; simpl in |- *; intros; auto with coc core arith datatypes.
  Qed.


  (* If a term is typable, the environment is well-formed *)
  Lemma typ_wf : forall e t T, typ e t T -> wf e.
  Proof.
    simple induction 1; auto with coc core arith datatypes.
  Qed.


  (* Typing lemma for variales (here the environment gets truncuated) *)
  Lemma wf_sort :
    forall n e f,
    trunc _ (S n) e f ->
    wf e -> forall t, item _ t e n -> exists s : sort, typ f t (Srt s).
  Proof.
    simple induction n.
    do 3 intro.
    inversion_clear H.
    inversion_clear H0.
    intros.
    inversion_clear H0.
    inversion_clear H.
    exists s; auto with coc core arith datatypes.

    do 5 intro.
    inversion_clear H0.
    intros.
    inversion_clear H2.
    inversion_clear H0.
    elim H with e0 f t; intros; auto with coc core arith datatypes.
    exists x0; auto with coc core arith datatypes.

    apply typ_wf with x (Srt s); auto with coc core arith datatypes.
  Qed.


  (* Inversion principle for typing *)
  Definition inv_type (P : Prop) e t T : Prop :=
    match t with
    | Srt prop => conv T (Srt kind) -> P
    | Srt set => conv T (Srt kind) -> P
    | Srt kind => True
    | Ref n => forall x : term, item _ x e n -> conv T (lift (S n) x) -> P
    | Abs A M =>
        forall s1 s2 (U : term),
        typ e A (Srt s1) ->
        typ (A :: e) M U -> typ (A :: e) U (Srt s2) -> conv T (Prod A U) -> P
    | App u v =>
        forall Ur V : term,
        typ e v V -> typ e u (Prod V Ur) -> conv T (subst v Ur) -> P
    | Prod A B =>
        forall s1 s2,
        typ e A (Srt s1) -> typ (A :: e) B (Srt s2) -> conv T (Srt s2) -> P
    (* New stuff *)
    | Nat => conv T (Srt set) -> P
    | NatO => conv T Nat -> P
    | NatSucc x => 
      forall Tx,
      typ e x Tx -> 
      conv Tx Nat ->
      conv T Nat -> P
    | NatDestruct x1 x2 x3 x4 =>
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Nat (Srt set)) ->
      conv Tx2 (App x1 NatO) ->
      conv Tx3 (Prod Nat (App (lift 1 x1) (NatSucc (Ref 0)))) ->
      conv Tx4 Nat ->
      conv T (App x1 x4) ->
      P
    | NatCases x1 x2 x3 x4 =>
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Nat (Srt prop)) ->
      conv Tx2 (App x1 NatO) ->
      conv Tx3 (Prod Nat (App (lift 1 x1) (NatSucc (Ref 0)))) ->
      conv Tx4 Nat ->
      conv T (App x1 x4) ->
      P
    | NatRec x1 x2 x3 x4 =>
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Nat (Srt set)) ->
      conv Tx2 (App x1 NatO) ->
      conv Tx3 (Prod Nat (Prod (App (lift 1 x1) (Ref 0)) (App (lift 2 x1) (NatSucc (Ref 1))))) ->
      conv Tx4 Nat ->
      conv T (App x1 x4) ->
      P
    | NatInd x1 x2 x3 x4 =>
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Nat (Srt prop)) ->
      conv Tx2 (App x1 NatO) ->
      conv Tx3 (Prod Nat (Prod (App (lift 1 x1) (Ref 0)) (App (lift 2 x1) (NatSucc (Ref 1))))) ->
      conv Tx4 Nat ->
      conv T (App x1 x4) ->
      P
    | AccProp x1 x2 x3 =>
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 ->
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
      conv Tx3 x1 ->
      conv T (Srt prop) ->
      P
    | AccIntro x1 x2 x3 x4 =>
      forall Tx1 Tx2 Tx3 Tx4,
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
      conv Tx3 x1 ->
      conv Tx4
      (
        Prod x1
        (
          Prod (App (App (lift 1 x2) (Ref 0)) (lift 1 x3))
          (AccProp (lift 2 x1) (lift 2 x2) (Ref 1))
        )
      ) ->
      conv T (AccProp x1 x2 x3) ->
      P
    | AccRec x1 x2 x3 x4 x5 x6 =>
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 -> typ e x5 Tx5 ->
      typ e x6 Tx6 ->
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
      conv Tx3 (Prod x1 (Srt set)) ->
      conv Tx4 
      (
        Prod x1 
        (
          Prod
          (
            Prod (lift 1 x1) 
            (
              Prod (App (App (lift 2 x3) (Ref 0)) (Ref 0))
              (App (lift 3 x3) (Ref 1))
            )
          )
          (App (lift 2 x3) (Ref 1))
        )
      ) ->
      conv Tx5 x1 ->
      conv Tx6 (AccProp x1 x2 x5) ->
      conv T (App x3 x5) ->
      P
    | AccInd x1 x2 x3 x4 x5 x6 =>
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 -> typ e x5 Tx5 ->
      typ e x6 Tx6 ->
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
      conv Tx3 (Prod x1 (Srt prop)) ->
      conv Tx4 
      (
        Prod x1 
        (
          Prod
          (
            Prod (lift 1 x1)
            (
              Prod (App (App (lift 2 x3) (Ref 0)) (Ref 0))
              (App (lift 3 x3) (Ref 1))
            )
          )
          (App (lift 2 x3) (Ref 1))
        )
      ) -> 
      conv Tx5 x1 ->
      conv Tx6 (AccProp x1 x2 x5) ->
      conv T (App x3 x5) ->
      P
    | Le x1 x2 =>
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 Nat ->
      conv Tx2 Nat ->
      conv T (Srt prop) ->
      P
    | LeN x =>
      forall Tx,
      typ e x Tx ->
      conv Tx Nat ->
      conv T (Le x x) ->
      P
    | LeS x1 x2 x3 =>
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 ->
      conv Tx1 Nat ->
      conv Tx2 Nat ->
      conv Tx3 (Le x1 x2) ->
      conv T (Le x1 (NatSucc x2)) ->
      P
    | LeCases x1 x2 x3 x4 x5 x6 =>
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      typ e x5 Tx5 -> typ e x6 Tx6 ->
      conv Tx1 (Prod Nat (Srt prop)) ->
      conv Tx2 (App x1 x4) ->
      conv Tx3 
      (
        Prod Nat 
        (
          Prod 
          (Le (lift 1 x4) (Ref 0)) 
          (
            App (lift 2 x1) (NatSucc (Ref 1))
          )
        )
      ) ->
      conv Tx4 Nat ->
      conv Tx5 Nat ->
      conv Tx6 (Le x4 x5) ->
      conv T (App x1 x5) ->
      P
    | LeInd x1 x2 x3 x4 x5 x6 =>
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      typ e x5 Tx5 -> typ e x6 Tx6 ->
      typ e x1 (Prod Nat (Srt prop)) ->
      conv Tx2 (App x1 x4) ->
      conv Tx3 
      (
        Prod Nat 
        (
          Prod 
          (Le (lift 1 x4) (Ref 0)) 
          (
            Prod
            (App (lift 2 x1) (Ref 1))
            (App (lift 3 x1) (NatSucc (Ref 2)))
          )
        )
      ) ->
      conv Tx4 Nat ->
      conv Tx5 Nat ->
      conv Tx6 (Le x4 x5) ->
      conv T (App x1 x5) ->
      P
    | Bool => conv T (Srt set) -> P
    | SumBool x1 x2 =>
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv T (Srt set) ->
      P
    | BoolTrue => conv T Bool -> P
    | BoolFalse => conv T Bool -> P
    | SumBoolLeft x1 x2 x3 =>
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 ->
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv Tx3 x1 ->
      conv T (SumBool x1 x2) ->
      P
    | SumBoolRight x1 x2 x3 =>
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 ->
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv Tx3 x2 ->
      conv T (SumBool x1 x2) ->
      P 
    | BoolInd x1 x2 x3 x4 =>
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Bool (Srt prop)) ->
      conv Tx2 (App x1 BoolTrue) ->
      conv Tx3 (App x1 BoolFalse) ->
      conv Tx4 Bool ->
      conv T (App x1 x4) ->
      P
    | BoolRec x1 x2 x3 x4 =>
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Bool (Srt set)) ->
      conv Tx2 (App x1 BoolTrue) ->
      conv Tx3 (App x1 BoolFalse) ->
      conv Tx4 Bool ->
      conv T (App x1 x4) ->
      P
    | SumBoolInd x1 x2 x3 x4 x5 x6 =>
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      typ e x5 Tx5 -> typ e x6 Tx6 ->
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv Tx3 (Prod (SumBool x1 x2) (Srt prop)) ->
      conv Tx4 
      (
        Prod x1 
        (
          App (lift 1 x3) 
          (SumBoolLeft (lift 1 x1) (lift 1 x2) (Ref 0))
        )
      ) ->
      conv Tx5
      (
        Prod x2
        (
          App (lift 1 x3) 
          (SumBoolRight (lift 1 x1) (lift 1 x2) (Ref 0))
        )
      ) ->
      conv Tx6 (SumBool x1 x2) ->
      conv T (App x3 x6) ->
      P 
    | SumBoolRec x1 x2 x3 x4 x5 x6 =>
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      typ e x5 Tx5 -> typ e x6 Tx6 ->
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv Tx3 (Prod (SumBool x1 x2) (Srt set)) ->
      conv Tx4 
      (
        Prod x1 
        (
          App (lift 1 x3) 
          (SumBoolLeft (lift 1 x1) (lift 1 x2) (Ref 0))
        )
      ) ->
      conv Tx5
      (
        Prod x2
        (
          App (lift 1 x3) 
          (SumBoolRight (lift 1 x1) (lift 1 x2) (Ref 0))
        )
      ) ->
      conv Tx6 (SumBool x1 x2) ->
      conv T (App x3 x6) ->
      P 
    | Refine x1 x2 =>
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Srt prop)) ->
      conv T (Srt set) ->
      P
    | RefineConstr x1 x2 x3 x4 =>
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Srt prop)) ->
      conv Tx3 x1 ->
      conv Tx4 (App x2 x3) ->
      conv T (Refine x1 x2) ->
      P
    | RefineProjVal x1 x2 x3 =>
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Srt prop)) ->
      conv Tx3 (Refine x1 x2) ->
      conv T x1 ->
      P
    | RefineProjProof x1 x2 x3 =>
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Srt prop)) ->
      conv Tx3 (Refine x1 x2) ->
      conv T (App x2 (RefineProjVal x1 x2 x3)) ->
      P
    | Eq x1 x2 x3 =>
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 x1 ->
      conv Tx3 x1 ->
      conv T (Srt prop) ->
      P
    | EqRefl x1 x2 =>
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 (Srt set) ->
      conv Tx2 x1 ->
      conv T (Eq x1 x2 x2) ->
      P
    | EqInd x1 x2 x3 x4 x5 x6 =>
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      typ e x4 Tx4 -> typ e x5 Tx5 -> typ e x6 Tx6 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 x1 ->
      conv Tx3 x1 ->
      conv Tx4 (Prod x1 (Srt prop)) ->
      conv Tx5 (App x4 x2) ->
      conv Tx6 (Eq x1 x2 x3) ->
      conv T (App x4 x3) ->
      P
    | EqRec x1 x2 x3 x4 x5 x6 =>
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      typ e x4 Tx4 -> typ e x5 Tx5 -> typ e x6 Tx6 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 x1 ->
      conv Tx3 x1 ->
      conv Tx4 (Prod x1 (Srt set)) ->
      conv Tx5 (App x4 x2) ->
      conv Tx6 (Eq x1 x2 x3) ->
      conv T (App x4 x3) ->
      P
    | Falsity => conv T (Srt prop) -> P
    | FalseInd x1 x2 =>
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 Falsity ->
      conv Tx2 (Srt prop) ->
      conv T x2 ->
      P
    | FalseRec x1 x2 =>
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 Falsity ->
      conv Tx2 (Srt set) ->
      conv T x2 ->
      P
    | Unit => conv T (Srt set) -> P
    | Nil => conv T Unit -> P
    | WFrec x1 x2 x3 x4 x5 =>
      forall Tx1 Tx2 Tx3 Tx4 Tx5,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      typ e x4 Tx4 -> typ e x5 Tx5 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
      conv Tx3 (Prod x1 (Srt set)) ->
      conv Tx4 
      (
        Prod x1
        (
          Prod (
            Refine 
            (lift 1 x1) 
            (
              Abs (lift 1 x1) 
              (App (App (lift 2 x2) (Ref 0)) (Ref 1))
            )
          )
          (App (lift 2 x3) (Ref 1))
        )
      ) ->
      conv Tx5 (Prod x1 (AccProp (lift 1 x1) (lift 1 x2) (Ref 0))) ->
      conv T (Prod x1 (App (lift 1 x3) (Ref 0))) ->
      P
    | BoolPropChoice x1 x2 x3 =>
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv Tx3 Bool ->
      conv T (Srt prop) ->
      P
    end
  .

  (* A lemma used in the next theorem *)
  Lemma inv_type_conv :
    forall (P : Prop) e t (U V : term),
    conv U V -> inv_type P e t U -> inv_type P e t V
  .
  Proof.
    do 6 intro.
    cut (forall x : term, conv V x -> conv U x).
    intro.
    case t; simpl in |- *; intros.
    generalize H1.
    elim s; auto with coc core arith datatypes; intros.

    apply H1 with x; auto with coc core arith datatypes.

    apply H1 with s1 s2 U0; auto with coc core arith datatypes.

    apply H1 with Ur V0; auto with coc core arith datatypes.

    apply H1 with s1 s2; auto with coc core arith datatypes.

    intros.
    apply H1.
    apply trans_conv_conv with V; auto with coc core arith datatypes.

    apply H1.
    apply trans_conv_conv with V; auto with coc core arith datatypes.

    apply H1 with Tx; [> exact H2 | exact H3 | apply trans_conv_conv with V; auto with coc core arith datatypes].

    apply H1 with Tx1 Tx2 Tx3 Tx4; auto with coc core datatypes.

    apply H1 with Tx1 Tx2 Tx3 Tx4; auto with coc core datatypes.

    apply H1 with Tx1 Tx2 Tx3 Tx4; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4; auto with coc.

    apply H1 with Tx1 Tx2 Tx3; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4 Tx5 Tx6; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4 Tx5 Tx6; auto with coc.

    apply H1 with Tx1 Tx2; auto with coc.

    apply H1 with Tx; auto with coc.

    apply H1 with Tx1 Tx2 Tx3; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4 Tx5 Tx6; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4 Tx5 Tx6; auto with coc.

    apply H1.
    apply H0.
    trivial.

    apply H1 with Tx1 Tx2; auto with coc.

    apply H1.
    apply H0.
    trivial.

    apply H1.
    apply H0.
    trivial.

    apply H1 with Tx1 Tx2 Tx3; auto with coc.

    apply H1 with Tx1 Tx2 Tx3; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4 Tx5 Tx6; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4 Tx5 Tx6; auto with coc.

    apply H1 with Tx1 Tx2; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4; auto with coc.

    apply H1 with Tx1 Tx2 Tx3; auto with coc.

    apply H1 with Tx1 Tx2 Tx3; auto with coc.

    apply H1 with Tx1 Tx2 Tx3; auto with coc.

    apply H1 with Tx1 Tx2; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4 Tx5 Tx6; auto with coc.

    apply H1 with Tx1 Tx2 Tx3 Tx4 Tx5 Tx6; auto with coc.

    apply H1.
    apply H0.
    trivial.

    apply H1 with Tx1 Tx2; auto with coc.

    apply H1 with Tx1 Tx2; auto with coc.

    apply H1.
    apply H0.
    trivial.

    apply H1.
    apply H0.
    trivial.

    apply H1 with Tx1 Tx2 Tx3 Tx4 Tx5; auto with coc.

    apply H1 with Tx1 Tx2 Tx3; auto with coc.

    intros.
    apply trans_conv_conv with V; auto with coc core arith datatypes.
  Qed.


  (* The proof of correcntess of our inversion principle *)
  Theorem typ_inversion :
    forall (P : Prop) e t T, typ e t T -> inv_type P e t T -> P
  .
  Proof.
    simple induction 1; simpl in |- *; intros.
    auto with coc core arith datatypes.

    auto with coc core arith datatypes.

    elim H1; intros.
    apply H2 with x; auto with coc core arith datatypes.
    rewrite H3; auto with coc core arith datatypes.

    apply H6 with s1 s2 U; auto with coc core arith datatypes.

    apply H4 with Ur V; auto with coc core arith datatypes.

    apply H4 with s1 s2; auto with coc core arith datatypes.

    apply H1.
    apply inv_type_conv with V; auto with coc core arith datatypes.

    apply H1; auto with coc core datatypes.

    apply H1; auto with coc core datatypes.

    apply H2 with Nat; auto with coc core datatypes.

    apply H8 with (Prod Nat (Srt set)) (App x1 NatO) (Prod Nat (App (lift 1 x1) (NatSucc (Ref 0)))) Nat; auto with coc core datatypes.

    apply H8 with (Prod Nat (Srt prop)) (App x1 NatO) (Prod Nat (App (lift 1 x1) (NatSucc (Ref 0)))) Nat; auto with coc core datatypes.
  
    eapply H8; eauto with coc.

    eapply H8; eauto with coc.

    eapply H6; eauto with coc.

    eapply H8; eauto with coc.

    eapply H12; eauto with coc.

    eapply H12; eauto with coc.

    eapply H4; eauto with coc.

    eapply H2; eauto with coc.

    eapply H6; eauto with coc.

    eapply H12; eauto with coc.

    eapply H12; eauto with coc.

    apply H1; auto with coc.

    eapply H4; eauto with coc.

    apply H1; auto with coc.

    apply H1; auto with coc.

    eapply H6; eauto with coc.

    eapply H6; eauto with coc.

    eapply H8; eauto with coc.

    eapply H8; eauto with coc.

    eapply H12; eauto with coc.

    eapply H12; eauto with coc.

    eapply H4; eauto with coc.

    eapply H8; eauto with coc.

    eapply H6; eauto with coc.

    eapply H6; eauto with coc.

    eapply H6; eauto with coc.

    eapply H4; eauto with coc.

    eapply H12; eauto with coc.

    eapply H12; eauto with coc.

    apply H1; auto with coc.

    eapply H4; eauto with coc.

    eapply H4; eauto with coc.

    apply H1; auto with coc.

    apply H1; auto with coc.

    eapply H10; eauto with coc.

    eapply H6; eauto with coc.
  Qed.
  (* Now we prove some useful corollaries *)


  Corollary inv_typ_kind : forall e t, ~ typ e (Srt kind) t.
  Proof.
    red in |- *; intros.
    apply typ_inversion with e (Srt kind) t; simpl in |- *;
    auto with coc core arith datatypes.
  Qed.

  Corollary inv_typ_prop : forall e T, typ e (Srt prop) T -> conv T (Srt kind).
  Proof.
    intros.
    apply typ_inversion with e (Srt prop) T; simpl in |- *;
    auto with coc core arith datatypes.
  Qed.

  Corollary inv_typ_set : forall e T, typ e (Srt set) T -> conv T (Srt kind).
  Proof.
    intros.
    apply typ_inversion with e (Srt set) T; simpl in |- *;
    auto with coc core arith datatypes.
  Qed.

  Corollary inv_typ_ref :
    forall (P : Prop) e T n,
    typ e (Ref n) T ->
    (forall U : term, item _ U e n -> conv T (lift (S n) U) -> P) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (Ref n) T; simpl in |- *; intros;
    auto with coc core arith datatypes.
    apply H0 with x; auto with coc core arith datatypes.
  Qed.

  Corollary inv_typ_abs :
    forall (P : Prop) e A M (U : term),
    typ e (Abs A M) U ->
    (
      forall s1 s2 T,
      typ e A (Srt s1) ->
      typ (A :: e) M T -> 
      typ (A :: e) T (Srt s2) -> 
      conv (Prod A T) U -> 
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (Abs A M) U; simpl in |- *;
    auto with coc core arith datatypes; intros.
    apply H0 with s1 s2 U0; auto with coc core arith datatypes.
  Qed.

  Corollary inv_typ_app :
    forall (P : Prop) e u v T,
    typ e (App u v) T ->
    (
      forall V Ur : term,
      typ e u (Prod V Ur) -> 
      typ e v V -> 
      conv T (subst v Ur) -> P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (App u v) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
    apply H0 with V Ur; auto with coc core arith datatypes.
  Qed.

  Corollary inv_typ_prod :
    forall (P : Prop) e T (U s : term),
    typ e (Prod T U) s ->
    (
      forall s1 s2,
      typ e T (Srt s1) -> 
      typ (T :: e) U (Srt s2) -> 
      conv (Srt s2) s -> P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (Prod T U) s; simpl in |- *;
    auto with coc core arith datatypes; intros.
    apply H0 with s1 s2; auto with coc core arith datatypes.
  Qed.

  Corollary inv_typ_nat :
    forall (P : Prop) e T,
    typ e Nat T ->
    (
      conv T (Srt set) -> P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e Nat T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_nat_o :
    forall (P : Prop) e T,
    typ e NatO T ->
    (
      conv T Nat -> P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e NatO T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_nat_succ :
    forall (P : Prop) e x T,
    typ e (NatSucc x) T ->
    (
      forall Tx,
      typ e x Tx -> 
      conv Tx Nat ->
      conv T Nat -> P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (NatSucc x) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_nat_destruct :
    forall (P : Prop) e (x1 x2 x3 x4 T : term),
    typ e (NatDestruct x1 x2 x3 x4) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Nat (Srt set)) ->
      conv Tx2 (App x1 NatO) ->
      conv Tx3 (Prod Nat (App (lift 1 x1) (NatSucc (Ref 0)))) ->
      conv Tx4 Nat ->
      conv T (App x1 x4) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (NatDestruct x1 x2 x3 x4) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_nat_cases :
    forall (P : Prop) e (x1 x2 x3 x4 T : term),
    typ e (NatCases x1 x2 x3 x4) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Nat (Srt prop)) ->
      conv Tx2 (App x1 NatO) ->
      conv Tx3 (Prod Nat (App (lift 1 x1) (NatSucc (Ref 0)))) ->
      conv Tx4 Nat ->
      conv T (App x1 x4) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (NatCases x1 x2 x3 x4) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_nat_rec :
    forall (P : Prop) e (x1 x2 x3 x4 T : term),
    typ e (NatRec x1 x2 x3 x4) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Nat (Srt set)) ->
      conv Tx2 (App x1 NatO) ->
      conv Tx3 (Prod Nat (Prod (App (lift 1 x1) (Ref 0)) (App (lift 2 x1) (NatSucc (Ref 1))))) ->
      conv Tx4 Nat ->
      conv T (App x1 x4) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (NatRec x1 x2 x3 x4) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_nat_ind :
    forall (P : Prop) e (x1 x2 x3 x4 T : term),
    typ e (NatInd x1 x2 x3 x4) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Nat (Srt prop)) ->
      conv Tx2 (App x1 NatO) ->
      conv Tx3 (Prod Nat (Prod (App (lift 1 x1) (Ref 0)) (App (lift 2 x1) (NatSucc (Ref 1))))) ->
      conv Tx4 Nat ->
      conv T (App x1 x4) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (NatInd x1 x2 x3 x4) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_acc_prop :
    forall (P : Prop) e (x1 x2 x3 T : term),
    typ e (AccProp x1 x2 x3) T ->
    (
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 ->
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
      conv Tx3 x1 ->
      conv T (Srt prop) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (AccProp x1 x2 x3) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_acc_intro :
    forall (P : Prop) e (x1 x2 x3 x4 T : term),
    typ e (AccIntro x1 x2 x3 x4) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4,
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
      conv Tx3 x1 ->
      conv Tx4
      (
        Prod x1
        (
          Prod (App (App (lift 1 x2) (Ref 0)) (lift 1 x3))
          (AccProp (lift 2 x1) (lift 2 x2) (Ref 1))
        )
      ) ->
      conv T (AccProp x1 x2 x3) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (AccIntro x1 x2 x3 x4) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_acc_rec :
    forall (P : Prop) e (x1 x2 x3 x4 x5 x6 T : term),
    typ e (AccRec x1 x2 x3 x4 x5 x6) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 -> typ e x5 Tx5 ->
      typ e x6 Tx6 ->
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
      conv Tx3 (Prod x1 (Srt set)) ->
      conv Tx4 
      (
        Prod x1 
        (
          Prod
          (
            Prod (lift 1 x1) 
            (
              Prod (App (App (lift 2 x3) (Ref 0)) (Ref 0))
              (App (lift 3 x3) (Ref 1))
            )
          )
          (App (lift 2 x3) (Ref 1))
        )
      ) -> 
      conv Tx5 x1 ->
      conv Tx6 (AccProp x1 x2 x5) ->
      conv T (App x3 x5) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (AccRec x1 x2 x3 x4 x5 x6) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_acc_ind :
    forall (P : Prop) e (x1 x2 x3 x4 x5 x6 T : term),
    typ e (AccInd x1 x2 x3 x4 x5 x6) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 -> typ e x5 Tx5 ->
      typ e x6 Tx6 ->
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
      conv Tx3 (Prod x1 (Srt prop)) ->
      conv Tx4 
      (
        Prod x1 
        (
          Prod
          (
            Prod (lift 1 x1) 
            (
              Prod (App (App (lift 2 x3) (Ref 0)) (Ref 0))
              (App (lift 3 x3) (Ref 1))
            )
          )
          (App (lift 2 x3) (Ref 1))
        )
      ) -> 
      conv Tx5 x1 ->
      conv Tx6 (AccProp x1 x2 x5) ->
      conv T (App x3 x5) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (AccInd x1 x2 x3 x4 x5 x6) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_le :
    forall (P : Prop) e (x1 x2 T : term),
    typ e (Le x1 x2) T ->
    (
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 Nat ->
      conv Tx2 Nat ->
      conv T (Srt prop) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (Le x1 x2) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_le_n :
    forall (P : Prop) e (x T : term),
    typ e (LeN x) T ->
    (
      forall Tx,
      typ e x Tx ->
      conv Tx Nat ->
      conv T (Le x x) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (LeN x) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_le_s :
    forall (P : Prop) e (x1 x2 x3 T : term),
    typ e (LeS x1 x2 x3) T ->
    (
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 ->
      conv Tx1 Nat ->
      conv Tx2 Nat ->
      conv Tx3 (Le x1 x2) ->
      conv T (Le x1 (NatSucc x2)) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (LeS x1 x2 x3) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_le_cases :
    forall (P : Prop) e (x1 x2 x3 x4 x5 x6 T : term),
    typ e (LeCases x1 x2 x3 x4 x5 x6) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      typ e x5 Tx5 -> typ e x6 Tx6 ->
      conv Tx1 (Prod Nat (Srt prop)) ->
      conv Tx2 (App x1 x4) ->
      conv Tx3 
      (
        Prod Nat 
        (
          Prod 
          (Le (lift 1 x4) (Ref 0)) 
          (
            App (lift 2 x1) (NatSucc (Ref 1))
          )
        )
      ) ->
      conv Tx4 Nat ->
      conv Tx5 Nat ->
      conv Tx6 (Le x4 x5) ->
      conv T (App x1 x5) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (LeCases x1 x2 x3 x4 x5 x6) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

   Corollary inv_typ_le_ind :
    forall (P : Prop) e (x1 x2 x3 x4 x5 x6 T : term),
    typ e (LeInd x1 x2 x3 x4 x5 x6) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      typ e x5 Tx5 -> typ e x6 Tx6 ->
      typ e x1 (Prod Nat (Srt prop)) ->
      conv Tx2 (App x1 x4) ->
      conv Tx3 
      (
        Prod Nat 
        (
          Prod 
          (Le (lift 1 x4) (Ref 0)) 
          (
            Prod
            (App (lift 2 x1) (Ref 1))
            (App (lift 3 x1) (NatSucc (Ref 2)))
          )
        )
      ) ->
      conv Tx4 Nat ->
      conv Tx5 Nat ->
      conv Tx6 (Le x4 x5) ->
      conv T (App x1 x5) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (LeInd x1 x2 x3 x4 x5 x6) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_bool :
    forall (P : Prop) e (T : term),
    typ e Bool T ->
    (
      conv T (Srt set) -> 
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e Bool T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_sumbool :
    forall (P : Prop) e (x1 x2 T : term),
    typ e (SumBool x1 x2) T ->
    (
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv T (Srt set) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (SumBool x1 x2) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_bool_true :
    forall (P : Prop) e (T : term),
    typ e BoolTrue T ->
    (
      conv T Bool ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e BoolTrue T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_bool_false :
    forall (P : Prop) e (T : term),
    typ e BoolFalse T ->
    (
      conv T Bool ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e BoolFalse T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_sumbool_left :
    forall (P : Prop) e (x1 x2 x3 T : term),
    typ e (SumBoolLeft x1 x2 x3) T ->
    (
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 ->
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv Tx3 x1 ->
      conv T (SumBool x1 x2) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (SumBoolLeft x1 x2 x3) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_sumbool_right :
    forall (P : Prop) e (x1 x2 x3 T : term),
    typ e (SumBoolRight x1 x2 x3) T ->
    (
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 ->
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv Tx3 x2 ->
      conv T (SumBool x1 x2) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (SumBoolRight x1 x2 x3) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_bool_ind :
    forall (P : Prop) e (x1 x2 x3 x4 T : term),
    typ e (BoolInd x1 x2 x3 x4) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Bool (Srt prop)) ->
      conv Tx2 (App x1 BoolTrue) ->
      conv Tx3 (App x1 BoolFalse) ->
      conv Tx4 Bool ->
      conv T (App x1 x4) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (BoolInd x1 x2 x3 x4) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_bool_rec :
    forall (P : Prop) e (x1 x2 x3 x4 T : term),
    typ e (BoolRec x1 x2 x3 x4) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Prod Bool (Srt set)) ->
      conv Tx2 (App x1 BoolTrue) ->
      conv Tx3 (App x1 BoolFalse) ->
      conv Tx4 Bool ->
      conv T (App x1 x4) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (BoolRec x1 x2 x3 x4) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_sumbool_ind :
    forall (P : Prop) e (x1 x2 x3 x4 x5 x6 T : term),
    typ e (SumBoolInd x1 x2 x3 x4 x5 x6) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      typ e x5 Tx5 -> typ e x6 Tx6 ->
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv Tx3 (Prod (SumBool x1 x2) (Srt prop)) ->
      conv Tx4 
      (
        Prod x1 
        (
          App (lift 1 x3) 
          (SumBoolLeft (lift 1 x1) (lift 1 x2) (Ref 0))
        )
      ) ->
      conv Tx5
      (
        Prod x2
        (
          App (lift 1 x3) 
          (SumBoolRight (lift 1 x1) (lift 1 x2) (Ref 0))
        )
      ) ->
      conv Tx6 (SumBool x1 x2) ->
      conv T (App x3 x6) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (SumBoolInd x1 x2 x3 x4 x5 x6) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_sumbool_rec :
    forall (P : Prop) e (x1 x2 x3 x4 x5 x6 T : term),
    typ e (SumBoolRec x1 x2 x3 x4 x5 x6) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      typ e x5 Tx5 -> typ e x6 Tx6 ->
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv Tx3 (Prod (SumBool x1 x2) (Srt set)) ->
      conv Tx4 
      (
        Prod x1 
        (
          App (lift 1 x3) 
          (SumBoolLeft (lift 1 x1) (lift 1 x2) (Ref 0))
        )
      ) ->
      conv Tx5
      (
        Prod x2
        (
          App (lift 1 x3) 
          (SumBoolRight (lift 1 x1) (lift 1 x2) (Ref 0))
        )
      ) ->
      conv Tx6 (SumBool x1 x2) ->
      conv T (App x3 x6) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (SumBoolRec x1 x2 x3 x4 x5 x6) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_refine :
    forall (P : Prop) e (x1 x2 T : term),
    typ e (Refine x1 x2) T ->
    (
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Srt prop)) ->
      conv T (Srt set) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (Refine x1 x2) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_refine_constr :
    forall (P : Prop) e (x1 x2 x3 x4 T : term),
    typ e (RefineConstr x1 x2 x3 x4) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> typ e x4 Tx4 ->
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Srt prop)) ->
      conv Tx3 x1 ->
      conv Tx4 (App x2 x3) ->
      conv T (Refine x1 x2) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (RefineConstr x1 x2 x3 x4) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_refine_proj_val :
    forall (P : Prop) e (x1 x2 x3 T : term),
    typ e (RefineProjVal x1 x2 x3) T ->
    (
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Srt prop)) ->
      conv Tx3 (Refine x1 x2) ->
      conv T x1 ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (RefineProjVal x1 x2 x3) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_refine_proj_proof :
    forall (P : Prop) e (x1 x2 x3 T : term),
    typ e (RefineProjProof x1 x2 x3) T ->
    (
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Srt prop)) ->
      conv Tx3 (Refine x1 x2) ->
      conv T (App x2 (RefineProjVal x1 x2 x3)) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (RefineProjProof x1 x2 x3) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_eq :
    forall (P : Prop) e (x1 x2 x3 T : term),
    typ e (Eq x1 x2 x3) T ->
    (
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 x1 ->
      conv Tx3 x1 ->
      conv T (Srt prop) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (Eq x1 x2 x3) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_eq_refl :
    forall (P : Prop) e (x1 x2 T : term),
    typ e (EqRefl x1 x2) T ->
    (
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 (Srt set) ->
      conv Tx2 x1 ->
      conv T (Eq x1 x2 x2) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (EqRefl x1 x2) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_eq_ind :
    forall (P : Prop) e (x1 x2 x3 x4 x5 x6 T : term),
    typ e (EqInd x1 x2 x3 x4 x5 x6) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      typ e x4 Tx4 -> typ e x5 Tx5 -> typ e x6 Tx6 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 x1 ->
      conv Tx3 x1 ->
      conv Tx4 (Prod x1 (Srt prop)) ->
      conv Tx5 (App x4 x2) ->
      conv Tx6 (Eq x1 x2 x3) ->
      conv T (App x4 x3) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (EqInd x1 x2 x3 x4 x5 x6) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_eq_rec :
    forall (P : Prop) e (x1 x2 x3 x4 x5 x6 T : term),
    typ e (EqRec x1 x2 x3 x4 x5 x6) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4 Tx5 Tx6,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      typ e x4 Tx4 -> typ e x5 Tx5 -> typ e x6 Tx6 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 x1 ->
      conv Tx3 x1 ->
      conv Tx4 (Prod x1 (Srt set)) ->
      conv Tx5 (App x4 x2) ->
      conv Tx6 (Eq x1 x2 x3) ->
      conv T (App x4 x3) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (EqRec x1 x2 x3 x4 x5 x6) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_falsity :
    forall (P : Prop) e (T : term),
    typ e Falsity T ->
    (
     conv T (Srt prop) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e Falsity T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_false_ind :
    forall (P : Prop) e (x1 x2 T : term),
    typ e (FalseInd x1 x2) T ->
    (
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 Falsity ->
      conv Tx2 (Srt prop) ->
      conv T x2 ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (FalseInd x1 x2) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_false_rec :
    forall (P : Prop) e (x1 x2 T : term),
    typ e (FalseRec x1 x2) T ->
    (
      forall Tx1 Tx2,
      typ e x1 Tx1 -> typ e x2 Tx2 ->
      conv Tx1 Falsity ->
      conv Tx2 (Srt set) ->
      conv T x2 ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (FalseRec x1 x2) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_unit :
    forall (P : Prop) e (T : term),
    typ e Unit T ->
    (
     conv T (Srt set) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e Unit T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_nil :
    forall (P : Prop) e (T : term),
    typ e Nil T ->
    (
     conv T Unit ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e Nil T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_wf_rec :
    forall (P : Prop) e (x1 x2 x3 x4 x5 T : term),
    typ e (WFrec x1 x2 x3 x4 x5) T ->
    (
      forall Tx1 Tx2 Tx3 Tx4 Tx5,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      typ e x4 Tx4 -> typ e x5 Tx5 -> 
      conv Tx1 (Srt set) ->
      conv Tx2 (Prod x1 (Prod (lift 1 x1) (Srt prop))) ->
      conv Tx3 (Prod x1 (Srt set)) ->
      conv Tx4 
      (
        Prod x1
        (
          Prod (
            Refine 
            (lift 1 x1) 
            (
              Abs (lift 1 x1) 
              (App (App (lift 2 x2) (Ref 0)) (Ref 1))
            )
          )
          (App (lift 2 x3) (Ref 1))
        )
      ) ->
      conv Tx5 (Prod x1 (AccProp (lift 1 x1) (lift 1 x2) (Ref 0))) ->
      conv T (Prod x1 (App (lift 1 x3) (Ref 0))) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (WFrec x1 x2 x3 x4 x5) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

  Corollary inv_typ_bool_prop_choice :
    forall (P : Prop) e (x1 x2 x3 T : term),
    typ e (BoolPropChoice x1 x2 x3) T ->
    (
      forall Tx1 Tx2 Tx3,
      typ e x1 Tx1 -> typ e x2 Tx2 -> typ e x3 Tx3 -> 
      conv Tx1 (Srt prop) ->
      conv Tx2 (Srt prop) ->
      conv Tx3 Bool ->
      conv T (Srt prop) ->
      P
    ) -> P
  .
  Proof.
    intros.
    apply typ_inversion with e (BoolPropChoice x1 x2 x3) T; simpl in |- *;
    auto with coc core arith datatypes; intros.
  Qed.

(*)
  (* We now show that a term which contains sort `Kind` is not typable *)
  Lemma typ_mem_kind : forall e t T, mem_sort kind t -> ~ typ e t T.
  Proof.
    red in |- *; intros.
    apply typ_inversion with e t T; auto with coc core arith datatypes.
    generalize e T.
    clear H0.
    elim H; simpl in |- *; auto with coc core arith datatypes; intros.
    apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

    apply typ_inversion with (u :: e0) v (Srt s2);
    auto with coc core arith datatypes.

    apply typ_inversion with e0 u (Srt s1); auto with coc core arith datatypes.

    apply typ_inversion with (u :: e0) v U; auto with coc core arith datatypes.

    apply typ_inversion with e0 u (Prod V Ur); auto with coc core arith datatypes.

    apply typ_inversion with e0 v V; auto with coc core arith datatypes.

    apply typ_inversion with e0 choice Tx1; auto with coc core arith datatypes.
    apply typ_inversion with e0 on_zero Tx2; auto with coc core arith datatypes.
    apply typ_inversion with e0 on_succ Tx3; auto with coc core arith datatypes.
    apply typ_inversion with e0 num Tx4; auto with coc core arith datatypes.

    apply typ_inversion with e0 choice Tx1; auto with coc core arith datatypes.
    apply typ_inversion with e0 on_zero Tx2; auto with coc core arith datatypes.
    apply typ_inversion with e0 on_succ Tx3; auto with coc core arith datatypes.
    apply typ_inversion with e0 num Tx4; auto with coc core arith datatypes.

    apply typ_inversion with e0 x Tx; auto with coc core arith datatypes.

    apply typ_inversion with e0 choice Tx1; auto with coc core arith datatypes.
    apply typ_inversion with e0 on_zero Tx2; auto with coc core arith datatypes.
    apply typ_inversion with e0 on_succ Tx3; auto with coc core arith datatypes.
    apply typ_inversion with e0 num Tx4; auto with coc core arith datatypes.

    apply typ_inversion with e0 choice Tx1; auto with coc core arith datatypes.
    apply typ_inversion with e0 on_zero Tx2; auto with coc core arith datatypes.
    apply typ_inversion with e0 on_succ Tx3; auto with coc core arith datatypes.
    apply typ_inversion with e0 num Tx4; auto with coc core arith datatypes.
  Qed.
*)

(*)
  (* Then we show that any term convertible to `Kind` is not typable *)
  Lemma inv_typ_conv_kind : forall e t T, conv t (Srt kind) -> ~ typ e t T.
  Proof.
    intros.
    apply typ_mem_kind.
    apply red_sort_mem.
    elim church_rosser with t (Srt kind); intros;
    auto with coc core arith datatypes.
    rewrite (red_normal (Srt kind) x); auto with coc core arith datatypes.
    red in |- *; red in |- *; intros.
    inversion_clear H2.
  Qed.
*)


  (*
    The predicate `ins_in_env A n e1 e2` determins if
    `e2` is `e1` with `A` inserted at `n`th position. 
  *)
  Inductive ins_in_env A : nat -> env -> env -> Prop :=
  | ins_O : forall e, ins_in_env A 0 e (A :: e)
  | ins_S :
    forall n e f t,
    ins_in_env A n e f ->
    ins_in_env A (S n) (t :: e) (lift_rec 1 t n :: f)
  .

  Hint Resolve ins_O ins_S: coc.

  (* Lemma about elements to the right of the inserted element *)
  Lemma ins_item_ge :
    forall A n e f,
    ins_in_env A n e f ->
    forall v : nat, 
    n <= v -> forall t, item _ t e v -> item _ t f (S v)
  .
  Proof.
    simple induction 1; auto with coc core arith datatypes.
    simple destruct v; intros.
    inversion_clear H2.

    inversion_clear H3; auto with coc core arith datatypes.
  Qed.

  (* Lemma about elements to the left of the inserted element *)
  Lemma ins_item_lt :
    forall A n e f,
    ins_in_env A n e f ->
    forall v : nat,
    n > v -> forall t, item_lift t e v -> item_lift (lift_rec 1 t n) f v
  .
  Proof.
    simple induction 1.
    intros.
    inversion_clear H0.

    simple destruct v; intros.
    elim H3; intros.
    rewrite H4.
    exists (lift_rec 1 t n0); auto with coc core arith datatypes.
    inversion_clear H5.
    elim permute_lift with t n0; auto with coc core arith datatypes.

    elim H3; intros.
    rewrite H4.
    inversion_clear H5.
    elim H1 with n1 (lift (S n1) x); intros; auto with coc core arith datatypes.
    exists x0; auto with coc core arith datatypes.
    pattern (lift (S (S n1)) x0) at 1 in |- *.
    rewrite simpl_lift; auto with coc core arith datatypes.
    elim H5.
    change
      (lift_rec 1 (lift (S (S n1)) x) (S n0) =
      lift 1 (lift_rec 1 (lift (S n1) x) n0)) in |- *.
    rewrite (permute_lift (lift (S n1) x) n0).
    unfold lift at 2 in |- *.
    pattern (lift (S (S n1)) x) in |- *.
    rewrite simpl_lift; auto with coc core arith datatypes.

    exists x; auto with coc core arith datatypes.
  Qed.


  (* Lemma about weakening the context with var insertion *)
  Lemma typ_weak_weak :
    forall A e t T,
    typ e t T ->
    forall n f,
    ins_in_env A n e f -> wf f 
    -> typ f (lift_rec 1 t n) (lift_rec 1 T n)
   .
  Proof.
    simple induction 1; simpl in |- *; intros; auto with coc core arith datatypes.
    elim (le_gt_dec n v); intros; apply type_var;
    auto with coc core arith datatypes.
    elim H1; intros.
    exists x.
    rewrite H4.
    unfold lift in |- *.
    rewrite simpl_lift_rec; simpl in |- *; auto with coc core arith datatypes.

    apply ins_item_ge with A n e0; auto with coc core arith datatypes.

    apply ins_item_lt with A e0; auto with coc core arith datatypes.

    cut (wf (lift_rec 1 T0 n :: f)).
    intro.
    apply type_abs with s1 s2; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    rewrite distr_lift_subst.
    apply type_app with (lift_rec 1 V n); auto with coc core arith datatypes.

    cut (wf (lift_rec 1 T0 n :: f)).
    intro.
    apply type_prod with s1; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_conv with (lift_rec 1 U n) s; auto with coc core arith datatypes.

    apply type_nat_destruct; auto with coc core datatypes.
    rewrite permute_lift; auto with coc core datatypes.

    apply type_nat_cases; auto with coc core datatypes.
    rewrite permute_lift; auto with coc core datatypes.

    apply type_nat_rec; auto with coc core datatypes.
    generalize (H5 n f H8 H9).
    change (S (S n)) with (2 + n).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.

    apply type_nat_ind; auto with coc core datatypes.
    generalize (H5 n f H8 H9).
    change (S (S n)) with (2 + n).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.

    apply type_acc_prop; auto with coc core datatypes.
    generalize (H3 n f H6 H7).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.

    apply type_acc_intro; auto with coc core datatypes.
    generalize (H3 n f H8 H9).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.
    generalize (H7 n f H8 H9).
    change (S (S n)) with (2 + n).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.

    apply type_acc_rec; auto with coc core datatypes.
    generalize (H3 n f H12 H13).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.
    generalize (H7 n f H12 H13).
    change (S (S (S n))) with (3 + n).
    change (S (S n)) with (2 + n).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.

    apply type_acc_ind; auto with coc core datatypes.
    generalize (H3 n f H12 H13).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.
    generalize (H7 n f H12 H13).
    change (S (S (S n))) with (3 + n).
    change (S (S n)) with (2 + n).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.

    apply type_le; auto with coc core datatypes.

    apply type_le_n; auto with coc core datatypes.

    apply type_le_s; auto with coc core datatypes.

    apply type_le_cases; auto with coc core datatypes.
    generalize (H5 n f H12 H13).
    change (S (S n)) with (2 + n).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.

    apply type_le_ind; auto with coc core datatypes.
    generalize (H5 n f H12 H13).
    change (S (S (S n))) with (3 + n).
    change (S (S n)) with (2 + n).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.

    apply type_bool; auto with coc core datatypes.

    apply type_sumbool; auto with coc core datatypes.

    apply type_bool_true; auto with coc core datatypes.

    apply type_bool_false; auto with coc core datatypes.

    apply type_sumbool_left; auto with coc core datatypes.

    apply type_sumbool_right; auto with coc core datatypes.

    apply type_bool_ind; auto with coc core datatypes.

    apply type_bool_rec; auto with coc core datatypes.

    apply type_sumbool_ind; auto with coc core datatypes.
    generalize (H7 n f H12 H13).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.
    generalize (H9 n f H12 H13).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.

    apply type_sumbool_rec; auto with coc core datatypes.
    generalize (H7 n f H12 H13).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.
    generalize (H9 n f H12 H13).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.

    apply type_refine; auto with coc core datatypes.

    apply type_refine_constr; auto with coc core datatypes.

    apply type_refine_proj_val; auto with coc core datatypes.

    apply type_refine_proj_proof; auto with coc core datatypes.

    apply type_eq; auto with coc core datatypes.

    apply type_eq_refl; auto with coc core datatypes.

    apply type_eq_ind; auto with coc core datatypes.

    apply type_eq_rec; auto with coc core datatypes.

    apply type_falsity; auto with coc core datatypes.

    apply type_false_ind; auto with coc core datatypes.

    apply type_false_rec; auto with coc core datatypes.

    apply type_unit; auto with coc core datatypes.

    apply type_nil; auto with coc core datatypes.

    rewrite <- permute_lift; auto with coc core arith datatypes.
    apply type_wf_rec; auto with coc core datatypes.
    generalize (H3 n f H10 H11).
    rewrite <- permute_lift; auto with coc core arith datatypes.
    generalize (H7 n f H10 H11).
    change (S (S n)) with (2 + n).
    unfold lift; repeat rewrite <- permute_lift_rec; auto with coc core arith datatypes.
    generalize (H9 n f H10 H11).
    repeat rewrite <- permute_lift; auto with coc core arith datatypes.

    apply type_bool_prop_choice; auto with coc core datatypes.
  Qed.


  (* 
    The thinning lemma is basically about appending a var
    to a context on the left to preserve typing. 
  *)
  Theorem thinning :
    forall e t T,
    typ e t T -> forall A, wf (A :: e) -> typ (A :: e) (lift 1 t) (lift 1 T)
  .
  Proof.
    unfold lift in |- *.
    intros.
    inversion_clear H0.
    apply typ_weak_weak with A e; auto with coc core arith datatypes.
    apply wf_var with s; auto with coc core arith datatypes.
  Qed.


  (* Now about appending more than one var *)
  Lemma thinning_n :
    forall n e f,
    trunc _ n e f ->
    forall t T, typ f t T -> wf e -> typ e (lift n t) (lift n T)
  .
  Proof.
    simple induction n.
    intros.
    rewrite lift0.
    rewrite lift0.
    replace e with f; auto with coc core arith datatypes.
    inversion_clear H; auto with coc core arith datatypes.

    do 8 intro.
    inversion_clear H0.
    intro.
    rewrite simpl_lift; auto with coc core arith datatypes.
    pattern (lift (S n0) T) in |- *.
    rewrite simpl_lift; auto with coc core arith datatypes.
    inversion_clear H0.
    change (typ (x :: e0) (lift 1 (lift n0 t)) (lift 1 (lift n0 T))) in |- *.
    apply thinning; auto with coc core arith datatypes.
    apply H with f; auto with coc core arith datatypes.
    apply typ_wf with x (Srt s); auto with coc core arith datatypes.

    apply wf_var with s; auto with coc core arith datatypes.
  Qed.


  (* Theorem about typability of vars in a well-formed context *)
  Lemma wf_sort_lift :
    forall n e t, wf e -> item_lift t e n -> 
    exists s : sort, typ e t (Srt s)
  .
  Proof.
    simple induction n.
    simple destruct e; intros.
    elim H0; intros.
    inversion_clear H2.

    elim H0; intros.
    rewrite H1.
    inversion_clear H2.
    inversion_clear H.
    exists s.
    replace (Srt s) with (lift 1 (Srt s)); auto with coc core arith datatypes.
    apply thinning; auto with coc core arith datatypes.
    apply wf_var with s; auto with coc core arith datatypes.

    intros.
    elim H1; intros.
    rewrite H2.
    generalize H0.
    inversion_clear H3; intros.
    rewrite simpl_lift; auto with coc core arith datatypes.
    cut (wf l); intros.
    elim H with l (lift (S n0) x); intros; auto with coc core arith datatypes.
    inversion_clear H3.
    exists x0.
    change (typ (y :: l) (lift 1 (lift (S n0) x)) (lift 1 (Srt x0))) in |- *.
    apply thinning; auto with coc core arith datatypes.
    apply wf_var with s; auto with coc core arith datatypes.

    exists x; auto with coc core arith datatypes.

    inversion_clear H3.
    apply typ_wf with y (Srt s); auto with coc core arith datatypes.
  Qed.



  (* 
    I have no clue what it does...
    It inserts `T` at `n` and substitutes
    `n` with `t` in all items before `T`.
    (I guess `T` is type of `t`).
    It must have something to do with substitution
    but then I don't understand why on earth we are
    inserting `T`.
  *)
  Inductive sub_in_env t T : nat -> env -> env -> Prop :=
  | sub_O : forall e, sub_in_env t T 0 (T :: e) e
  | sub_S :
    forall e f n u,
    sub_in_env t T n e f ->
    sub_in_env t T (S n) (u :: e) (subst_rec t u n :: f)
  .

  Hint Resolve sub_O sub_S: coc.

  (* Now we describe how values to right of the insrted `T` look *)
  Lemma nth_sub_sup :
    forall t T n e f,
    sub_in_env t T n e f ->
    forall v : nat, n <= v -> forall u, item _ u e (S v) -> item _ u f v
  .
  Proof.
    simple induction 1.
    intros.
    inversion_clear H1; auto with coc core arith datatypes.

    simple destruct v; intros.
    inversion_clear H2.

    inversion_clear H3; auto with coc core arith datatypes.
  Qed.


  (* Here we show what `n`'th item looks like *)
  Lemma nth_sub_eq : forall t T n e f, sub_in_env t T n e f -> item _ T e n.
  Proof.
    simple induction 1; auto with coc core arith datatypes.
  Qed.


  (*
    Now we describe all the items to the right.
  *)
  Lemma nth_sub_inf :
    forall t T n e f,
    sub_in_env t T n e f ->
    forall v : nat,
    n > v -> forall u, item_lift u e v -> item_lift (subst_rec t u n) f v
  .
  Proof.
    simple induction 1.
    intros.
    inversion_clear H0.

    simple destruct v; intros.
    elim H3; intros.
    rewrite H4.
    inversion_clear H5.
    exists (subst_rec t u n0); auto with coc core arith datatypes.
    apply commut_lift_subst; auto with coc core arith datatypes.

    elim H3; intros.
    rewrite H4.
    inversion_clear H5.
    elim H1 with n1 (lift (S n1) x); intros; auto with coc core arith datatypes.
    exists x0; auto with coc core arith datatypes.
    rewrite simpl_lift; auto with coc core arith datatypes.
    pattern (lift (S (S n1)) x0) in |- *.
    rewrite simpl_lift; auto with coc core arith datatypes.
    elim H5.
    change
      (subst_rec t (lift 1 (lift (S n1) x)) (S n0) =
      lift 1 (subst_rec t (lift (S n1) x) n0)) in |- *.
    apply commut_lift_subst; auto with coc core arith datatypes.

    exists x; auto with coc core arith datatypes.
  Qed.


  (*
    The "weakened" substituition lemma. It is
    weakened, because we add a new var to the
    context.
  *)
  (*)
  Lemma typ_sub_weak :
    forall g (d : term) t, typ g d t ->
    forall e u (U : term), typ e u U ->
    forall f n, sub_in_env d t n e f -> 
    wf f -> trunc _ n f g -> 
    typ f (subst_rec d u n) (subst_rec d U n)
  .
  Proof.
    simple induction 2; simpl in |- *; intros; auto with coc core arith datatypes.
    elim (lt_eq_lt_dec n v); [ intro Hlt_eq | intro Hlt ].
    elim H2.
    elim Hlt_eq; clear Hlt_eq.
    case v; [ intro Hlt | intros n0 Hlt ]; intros.
    inversion_clear Hlt.

    simpl in |- *.
    rewrite H6.
    rewrite simpl_subst; auto with coc core arith datatypes.
    apply type_var; auto with coc core arith datatypes.
    exists x; auto with coc core arith datatypes.
    apply nth_sub_sup with d t n e0; auto with coc core arith datatypes.

    intro Heq; intros.
    rewrite H6.
    elim Heq.
    rewrite simpl_subst; auto with coc core arith datatypes.
    replace x with t.
    apply thinning_n with g; auto with coc core arith datatypes.

    apply fun_item with e0 v; auto with coc core arith datatypes.
    apply nth_sub_eq with d f; auto with coc core arith datatypes.
    elim Heq; auto with coc core arith datatypes.

    apply type_var; auto with coc core arith datatypes.
    apply nth_sub_inf with t e0; auto with coc core arith datatypes.

    cut (wf (subst_rec d T n :: f)); intros.
    apply type_abs with s1 s2; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    rewrite distr_subst.
    apply type_app with (subst_rec d V n); auto with coc core arith datatypes.

    cut (wf (subst_rec d T n :: f)); intros.
    apply type_prod with s1; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_conv with (subst_rec d U0 n) s; auto with coc core arith datatypes.

    apply type_nat_destruct; auto with coc core datatypes.
    rewrite <- commut_lift_subst; auto with coc arith datatypes.

    apply type_nat_cases; auto with coc core datatypes.
    rewrite <- commut_lift_subst; auto with coc arith datatypes.
  Qed.

  (*
    The substitution theorem. This special
    case is more useful for us, because 
    it can be used when reasoning about `App`
    reduction.
  *)
  Theorem substitution :
    forall e t u (U : term),
    typ (t :: e) u U ->
    forall d : term, typ e d t -> typ e (subst d u) (subst d U)
  .
  Proof.
    intros.
    unfold subst in |- *.
    apply typ_sub_weak with e t (t :: e); auto with coc core arith datatypes.
    apply typ_wf with d t; auto with coc core arith datatypes.
  Qed.
  *)



  (*
    In this system all types are unique up to
    conversion.
    (
      Note that this theorem is not true in
      Cic (because of Type[i]) or a system with 
      predicate subtyping.
    )
  *)
  Theorem typ_unique :
    forall e t T, typ e t T -> forall U : term, typ e t U -> conv T U
  .
  Proof.
    simple induction 1; intros.
    apply sym_conv.
    apply inv_typ_prop with e0; auto with coc core arith datatypes.

    apply sym_conv.
    apply inv_typ_set with e0; auto with coc core arith datatypes.

    apply inv_typ_ref with e0 U v; auto with coc core arith datatypes; intros.
    elim H1; intros.
    rewrite H5.
    elim fun_item with term U0 x e0 v; auto with coc core arith datatypes.

    apply inv_typ_abs with e0 T0 M U0; auto with coc core arith datatypes; intros.
    apply trans_conv_conv with (Prod T0 T1); auto with coc core arith datatypes.

    apply inv_typ_app with e0 u v U; auto with coc core arith datatypes; intros.
    apply trans_conv_conv with (subst v Ur0); auto with coc core arith datatypes.
    unfold subst in |- *; apply conv_conv_subst;
    auto with coc core arith datatypes.
    apply inv_conv_prod_r with V V0; auto with coc core arith datatypes.

    apply inv_typ_prod with e0 T0 U U0; auto with coc core arith datatypes;
    intros.
    apply trans_conv_conv with (Srt s3); auto with coc core arith datatypes.

    apply trans_conv_conv with U; auto with coc core arith datatypes.

    apply inv_typ_nat with e0 U; auto with coc core datatypes.

    apply inv_typ_nat_o with e0 U; auto with coc core datatypes.

    apply inv_typ_nat_succ with e0 x U; auto with coc core datatypes.

    apply inv_typ_nat_destruct with e0 x1 x2 x3 x4 U; auto with coc core datatypes.

    apply inv_typ_nat_cases with e0 x1 x2 x3 x4 U; auto with coc core datatypes.
  
    apply inv_typ_nat_rec with e0 x1 x2 x3 x4 U; auto with coc core datatypes.

    apply inv_typ_nat_ind with e0 x1 x2 x3 x4 U; auto with coc core datatypes.

    apply inv_typ_acc_prop with e0 x1 x2 x3 U; auto with coc core datatypes.

    apply inv_typ_acc_intro with e0 x1 x2 x3 x4 U; auto with coc core datatypes.

    apply inv_typ_acc_rec with e0 x1 x2 x3 x4 x5 x6 U; auto with coc core datatypes.

    apply inv_typ_acc_ind with e0 x1 x2 x3 x4 x5 x6 U; auto with coc core datatypes.

    apply inv_typ_le with e0 x1 x2 U; auto with coc core datatypes.

    apply inv_typ_le_n with e0 x U; auto with coc core datatypes.

    apply inv_typ_le_s with e0 x1 x2 x3 U; auto with coc core datatypes.

    apply inv_typ_le_cases with e0 x1 x2 x3 x4 x5 x6 U; auto with coc core datatypes.

    apply inv_typ_le_ind with e0 x1 x2 x3 x4 x5 x6 U; auto with coc core datatypes.

    apply inv_typ_bool with e0 U; auto with coc core datatypes.

    apply inv_typ_sumbool with e0 x1 x2 U; auto with coc core datatypes.

    apply inv_typ_bool_true with e0 U; auto with coc core datatypes.

    apply inv_typ_bool_false with e0 U; auto with coc core datatypes.

    apply inv_typ_sumbool_left with e0 x1 x2 x3 U; auto with coc core datatypes.

    apply inv_typ_sumbool_right with e0 x1 x2 x3 U; auto with coc core datatypes.

    apply inv_typ_bool_ind with e0 x1 x2 x3 x4 U; auto with coc core datatypes.

    apply inv_typ_bool_rec with e0 x1 x2 x3 x4 U; auto with coc core datatypes.

    apply inv_typ_sumbool_ind with e0 x1 x2 x3 x4 x5 x6 U; auto with coc core datatypes.

    apply inv_typ_sumbool_rec with e0 x1 x2 x3 x4 x5 x6 U; auto with coc core datatypes.

    apply inv_typ_refine with e0 x1 x2 U; auto with coc core datatypes.

    apply inv_typ_refine_constr with e0 x1 x2 x3 x4 U; auto with coc core datatypes.

    apply inv_typ_refine_proj_val with e0 x1 x2 x3 U; auto with coc core datatypes.

    apply inv_typ_refine_proj_proof with e0 x1 x2 x3 U; auto with coc core datatypes.

    apply inv_typ_eq with e0 x1 x2 x3 U; auto with coc core datatypes.

    apply inv_typ_eq_refl with e0 x1 x2 U; auto with coc core datatypes.

    apply inv_typ_eq_ind with e0 x1 x2 x3 x4 x5 x6 U; auto with coc core datatypes.

    apply inv_typ_eq_rec with e0 x1 x2 x3 x4 x5 x6 U; auto with coc core datatypes.

    apply inv_typ_falsity with e0 U; auto with coc core datatypes.

    apply inv_typ_false_ind with e0 x1 x2 U; auto with coc core datatypes.

    apply inv_typ_false_rec with e0 x1 x2 U; auto with coc core datatypes.

    apply inv_typ_unit with e0 U; auto with coc core datatypes.

    apply inv_typ_nil with e0 U; auto with coc core datatypes.

    apply inv_typ_wf_rec with e0 x1 x2 x3 x4 x5 U; auto with coc core datatypes.

    apply inv_typ_bool_prop_choice with e0 x1 x2 x3 U; auto with coc core datatypes.
Qed.

(*)
  (* Any type of our term either has type which is as sort or that type is `Kind` *)
  Theorem type_case :
    forall e t T,
    typ e t T -> 
    (exists s : sort, typ e T (Srt s)) \/ T = Srt kind
  .
  Proof.
    simple induction 1; intros; auto with coc core arith datatypes.
    left.
    elim wf_sort_lift with v e0 t0; auto with coc core arith datatypes; intros.
    exists x; auto with coc core arith datatypes.

    left.
    exists s2.
    apply type_prod with s1; auto with coc core arith datatypes.

    left.
    elim H3; intros.
    elim H4; intros.
    apply inv_typ_prod with e0 V Ur (Srt x); auto with coc core arith datatypes;
    intros.
    exists s2.
    replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
    apply substitution with V; auto with coc core arith datatypes.

    discriminate H4.

    case s2; auto with coc core arith datatypes.
    left.
    exists kind.
    apply type_prop.
    apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

    left.
    exists kind.
    apply type_set.
    apply typ_wf with T0 (Srt s1); auto with coc core arith datatypes.

    left.
    exists s; auto with coc core arith datatypes.

    left.
    exists kind; auto with coc core datatypes.

    left.
    exists set; auto with coc core datatypes.

    left.
    exists set.
    change (Srt set) with (subst x4 (Srt set)).
    apply (type_app e0 x4 Nat); auto with coc core datatypes.

    left.
    exists prop.
    change (Srt prop) with (subst x4 (Srt prop)).
    apply (type_app e0 x4 Nat); auto with coc core datatypes.
  Qed.


  (* If a term that has type `T` and type `Kind` at the same time, `T = Kind` *)
  Corollary type_kind_not_conv :
    forall e t T, typ e t T -> typ e t (Srt kind) -> T = Srt kind.
  Proof.
    intros.
    elim type_case with e t T; intros; auto with coc core arith datatypes.
    elim H1; intros.
    elim inv_typ_conv_kind with e T (Srt x); auto with coc core arith datatypes.
    apply typ_unique with e t; auto with coc core arith datatypes.
  Qed.


  (* A lemma about free variables in type of a term *)
  Lemma type_free_db : forall e t T, typ e t T -> free_db (length e) T.
  Proof.
    intros.
    elim type_case with e t T; intros; auto with coc core arith datatypes.
    inversion_clear H0.
    apply typ_free_db with (Srt x); auto with coc core arith datatypes.

    rewrite H0; auto with coc core arith datatypes.
  Qed.



  (* One-step reduction of out enivronment *)
  Inductive red1_in_env : env -> env -> Prop :=
  | red1_env_hd : forall e t u, red1 t u -> red1_in_env (t :: e) (u :: e)
  | red1_env_tl :
    forall e f t, red1_in_env e f -> red1_in_env (t :: e) (t :: f)
  .

  Hint Resolve red1_env_hd red1_env_tl: coc.

  (* 
    Lemma about reasoning lifting and reduction of environment. 
    I guess is says that each item either stays in place or
    gets reduced
  *)
  Lemma red_item :
    forall n t e, item_lift t e n ->
    forall f, red1_in_env e f ->
    item_lift t f n \/ (
      (forall g, trunc _ (S n) e g -> trunc _ (S n) f g) /\
      ex2 (fun u => red1 t u) (fun u => item_lift u f n)
    )
  .
  Proof.
    simple induction n.
    do 3 intro.
    elim H.
    do 4 intro.
    rewrite H0.
    inversion_clear H1.
    intros.
    inversion_clear H1.
    right.
    split; intros.
    inversion_clear H1; auto with coc core arith datatypes.

    exists (lift 1 u).
    unfold lift in |- *; auto with coc core arith datatypes.

    exists u; auto with coc core arith datatypes.

    left.
    exists x; auto with coc core arith datatypes.

    do 5 intro.
    elim H0.
    do 4 intro.
    rewrite H1.
    inversion_clear H2.
    intros.
    inversion_clear H2.
    left.
    exists x; auto with coc core arith datatypes.

    elim H with (lift (S n0) x) l f0; auto with coc core arith datatypes; intros.
    left.
    elim H2; intros.
    exists x0; auto with coc core arith datatypes.
    rewrite simpl_lift.
    pattern (lift (S (S n0)) x0) in |- *.
    rewrite simpl_lift.
    elim H5; auto with coc core arith datatypes.

    right.
    elim H2.
    simple induction 2; intros.
    split; intros.
    inversion_clear H9; auto with coc core arith datatypes.

    elim H8; intros.
    exists (lift (S (S n0)) x1).
    rewrite simpl_lift.
    pattern (lift (S (S n0)) x1) in |- *.
    rewrite simpl_lift.
    elim H9; unfold lift at 1 3 in |- *; auto with coc core arith datatypes.

    exists x1; auto with coc core arith datatypes.

    exists x; auto with coc core arith datatypes.
  Qed.



  (* 
    If we reduce the environment, the type stays the same. 
    (
      We feel a bit unsure and for now require the reduced 
      environemnt to be well-formed
    )
  *)
  Lemma typ_red_env :
    forall e t T, typ e t T -> 
    forall f, red1_in_env e f -> 
    wf f -> typ f t T
  .
  Proof.
    simple induction 1; intros.
    auto with coc core arith datatypes.

    auto with coc core arith datatypes.

    elim red_item with v t0 e0 f; auto with coc core arith datatypes; intros.
    inversion_clear H4.
    inversion_clear H6.
    elim H1; intros.
    elim item_trunc with term v e0 x0; intros; auto with coc core arith datatypes.
    elim wf_sort with v e0 x1 x0; auto with coc core arith datatypes.
    intros.
    apply type_conv with x x2; auto with coc core arith datatypes.
    rewrite H6.
    replace (Srt x2) with (lift (S v) (Srt x2));
    auto with coc core arith datatypes.
    apply thinning_n with x1; auto with coc core arith datatypes.

    cut (wf (T0 :: f)); intros.
    apply type_abs with s1 s2; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_app with V; auto with coc core arith datatypes.

    cut (wf (T0 :: f)); intros.
    apply type_prod with s1; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_conv with U s; auto with coc core arith datatypes.

    apply type_nat; auto with coc core datatypes.

    apply type_nat_o; auto with coc core datatypes.

    apply type_nat_succ; auto with coc core datatypes.

    apply type_nat_destruct; auto with coc core datatypes.

    apply type_nat_cases; auto with coc core datatypes.
  Qed.


  (* The preservation for one-step reduction *)
  Lemma subj_red : forall e t T, typ e t T -> forall u, red1 t u -> typ e u T.
  Proof.
    simple induction 1; intros.
    inversion_clear H1.

    inversion_clear H1.

    inversion_clear H2.

    inversion_clear H6.
    cut (wf (M' :: e0)); intros.
    apply type_conv with (Prod M' U) s2; auto with coc core arith datatypes.
    apply type_abs with s1 s2; auto with coc core arith datatypes.
    apply typ_red_env with (T0 :: e0); auto with coc core arith datatypes.

    apply typ_red_env with (T0 :: e0); auto with coc core arith datatypes.

    apply type_prod with s1; auto with coc core arith datatypes.

    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_abs with s1 s2; auto with coc core arith datatypes.

    elim type_case with e0 u (Prod V Ur); intros;
    auto with coc core arith datatypes.
    inversion_clear H5.
    apply inv_typ_prod with e0 V Ur (Srt x); intros;
    auto with coc core arith datatypes.
    generalize H2 H3.
    clear H2 H3.
    inversion_clear H4; intros.
    apply inv_typ_abs with e0 T0 M (Prod V Ur); intros;
    auto with coc core arith datatypes.
    apply type_conv with (subst v T1) s2; auto with coc core arith datatypes.
    apply substitution with T0; auto with coc core arith datatypes.
    apply type_conv with V s0; auto with coc core arith datatypes.
    apply inv_conv_prod_l with Ur T1; auto with coc core arith datatypes.

    unfold subst in |- *.
    apply conv_conv_subst; auto with coc core arith datatypes.
    apply inv_conv_prod_r with T0 V; auto with coc core arith datatypes.

    replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
    apply substitution with V; auto with coc core arith datatypes.

    apply type_app with V; auto with coc core arith datatypes.

    apply type_conv with (subst N2 Ur) s2; auto with coc core arith datatypes.
    apply type_app with V; auto with coc core arith datatypes.

    unfold subst in |- *.
    apply conv_conv_subst; auto with coc core arith datatypes.

    replace (Srt s2) with (subst v (Srt s2)); auto with coc core arith datatypes.
    apply substitution with V; auto with coc core arith datatypes.

    discriminate H5.

    inversion_clear H4.
    apply type_prod with s1; auto with coc core arith datatypes.
    apply typ_red_env with (T0 :: e0); auto with coc core arith datatypes.
    apply wf_var with s1; auto with coc core arith datatypes.

    apply type_prod with s1; auto with coc core arith datatypes.

    apply type_conv with U s; auto with coc core arith datatypes.

    inversion H1.

    inversion H1.

    inversion_clear H2.
    apply type_nat_succ; auto with coc core datatypes.

    inversion H8.
    subst choice; subst on_zero; subst on_succ; subst num; subst u.
    apply type_conv with (App choice' x4) set; auto with coc core datatypes.
    apply type_nat_destruct; auto with coc core datatypes.
    apply type_conv with (App x1 NatO) set; auto with coc core datatypes.
    change (Srt set) with (subst NatO (Srt set)); apply type_app with Nat; auto with coc core datatypes.
    apply type_nat_o; eapply typ_wf; eauto with coc core datatypes.
    apply type_conv with (Prod Nat (App (lift 1 x1) (NatSucc (Ref 0)))) set; auto with coc core datatypes.
    apply trans_conv_red with (Prod Nat (App (lift 1 x1) (NatSucc (Ref 0)))); auto with coc core datatypes.
    apply prod_red_r; apply app_red_l; unfold lift; auto with coc core datatypes.
    apply type_prod with set.
    apply type_nat; eapply typ_wf; eauto with coc core datatypes.
    change (Srt set) with (subst (NatSucc (Ref 0)) (Srt set)).
    apply type_app with Nat.
    apply type_nat_succ; apply type_var.
    apply wf_var with set; apply type_nat; eapply typ_wf; eauto with coc core datatypes.
    exists Nat; auto with coc core datatypes.
    change (Prod Nat (Srt set)) with (lift 1 (Prod Nat (Srt set))).
    apply thinning; auto with coc core datatypes.
    apply wf_var with set; apply type_nat; eapply typ_wf; eauto with coc core datatypes.
    change (Srt set) with (subst x4 (Srt set)).
    apply type_app with Nat; auto with coc core datatypes.
    apply type_nat_destruct; auto with coc core datatypes.
    apply type_nat_destruct; auto with coc core datatypes.
    subst choice; subst on_zero; subst on_succ; subst num; subst u.
    apply type_conv with (App x1 num') set; auto with coc core datatypes.
    apply type_nat_destruct; auto with coc core datatypes.
    change (Srt set) with (subst x4 (Srt set)).
    apply type_app with Nat; auto with coc core datatypes.
    subst choice; subst on_zero; subst on_succ; subst x4; subst u.
    auto with coc core datatypes.
    subst choice; subst on_zero; subst on_succ; subst x4; subst u.
    rewrite <- (lift0 num).
    rewrite <- (subst_ref_eq num 0) at 2.
    change (NatSucc (subst_rec num (Ref 0) 0)) with (subst_rec num (NatSucc (Ref 0)) 0).
    rewrite <- (lift0 x1).
    rewrite <- simpl_subst with num x1 0 0; auto with coc core arith datatypes.
    change (
      App (subst_rec num (lift 1 x1) 0) (subst_rec num (NatSucc (Ref 0)) 0)
    ) with (
      subst num (App (lift 1 x1) (NatSucc (Ref 0)))
    ).
    rewrite lift0.
    apply type_app with Nat; auto with coc core datatypes.
    apply inv_typ_nat_succ with e0 num Nat.
    apply inv_typ_nat_succ with e0 num Nat; auto with coc core datatypes.
    intros.
    apply type_conv with Tx set; auto with coc core datatypes.
    apply type_nat; eapply typ_wf; eauto with coc core datatypes.


    inversion H8.
    subst choice; subst on_zero; subst on_succ; subst num; subst u.
    apply type_conv with (App choice' x4) prop; auto with coc core datatypes.
    apply type_nat_cases; auto with coc core datatypes.
    apply type_conv with (App x1 NatO) prop; auto with coc core datatypes.
    change (Srt prop) with (subst NatO (Srt prop)); apply type_app with Nat; auto with coc core datatypes.
    apply type_nat_o; eapply typ_wf; eauto with coc core datatypes.
    apply type_conv with (Prod Nat (App (lift 1 x1) (NatSucc (Ref 0)))) prop; auto with coc core datatypes.
    apply trans_conv_red with (Prod Nat (App (lift 1 x1) (NatSucc (Ref 0)))); auto with coc core datatypes.
    apply prod_red_r; apply app_red_l; unfold lift; auto with coc core datatypes.
    apply type_prod with set.
    apply type_nat; eapply typ_wf; eauto with coc core datatypes.
    change (Srt prop) with (subst (NatSucc (Ref 0)) (Srt prop)).
    apply type_app with Nat.
    apply type_nat_succ; apply type_var.
    apply wf_var with set; apply type_nat; eapply typ_wf; eauto with coc core datatypes.
    exists Nat; auto with coc core datatypes.
    change (Prod Nat (Srt prop)) with (lift 1 (Prod Nat (Srt prop))).
    apply thinning; auto with coc core datatypes.
    apply wf_var with set; apply type_nat; eapply typ_wf; eauto with coc core datatypes.
    change (Srt prop) with (subst x4 (Srt prop)).
    apply type_app with Nat; auto with coc core datatypes.
    apply type_nat_cases; auto with coc core datatypes.
    apply type_nat_cases; auto with coc core datatypes.
    subst choice; subst on_zero; subst on_succ; subst num; subst u.
    apply type_conv with (App x1 num') prop; auto with coc core datatypes.
    apply type_nat_cases; auto with coc core datatypes.
    change (Srt prop) with (subst x4 (Srt prop)).
    apply type_app with Nat; auto with coc core datatypes.
    subst choice; subst on_zero; subst on_succ; subst x4; subst u.
    auto with coc core datatypes.
    subst choice; subst on_zero; subst on_succ; subst x4; subst u.
    rewrite <- (lift0 num).
    rewrite <- (subst_ref_eq num 0) at 2.
    change (NatSucc (subst_rec num (Ref 0) 0)) with (subst_rec num (NatSucc (Ref 0)) 0).
    rewrite <- (lift0 x1).
    rewrite <- simpl_subst with num x1 0 0; auto with coc core arith datatypes.
    change (
      App (subst_rec num (lift 1 x1) 0) (subst_rec num (NatSucc (Ref 0)) 0)
    ) with (
      subst num (App (lift 1 x1) (NatSucc (Ref 0)))
    ).
    rewrite lift0.
    apply type_app with Nat; auto with coc core datatypes.
    apply inv_typ_nat_succ with e0 num Nat.
    apply inv_typ_nat_succ with e0 num Nat; auto with coc core datatypes.
    intros.
    apply type_conv with Tx set; auto with coc core datatypes.
    apply type_nat; eapply typ_wf; eauto with coc core datatypes.
  Qed.


  (* The preservation theorem for mulitystep reduction *)
  Theorem subject_reduction :
    forall e t u, red t u -> forall T, typ e t T -> typ e u T
  .
  Proof.
    simple induction 1; intros; auto with coc core arith datatypes.
    apply subj_red with P; intros; auto with coc core arith datatypes.
  Qed.


  (* 
    We show that we can freely replace type `T` with type `U` it reduces 
    to without requiring `U` to be typable 
  *)
  Lemma type_reduction :
    forall e t T (U : term), red T U -> typ e t T -> typ e t U
  .
  Proof.
    intros.
    elim type_case with e t T; intros; auto with coc core arith datatypes.
    inversion_clear H1.
    apply type_conv with T x; auto with coc core arith datatypes.
    apply subject_reduction with T; auto with coc core arith datatypes.

    elim red_normal with T U; auto with coc core arith datatypes.
    rewrite H1.
    red in |- *; red in |- *; intros.
    inversion_clear H2.
  Qed.



  (* Types of two convertible terms are convertible *)
  Lemma typ_conv_conv :
    forall e u (U : term) v (V : term),
    typ e u U -> typ e v V -> conv u v -> conv U V
  .
  Proof. 
    intros.
    elim church_rosser with u v; auto with coc core arith datatypes; intros.
    apply typ_unique with e x.
    apply subject_reduction with u; auto with coc core arith datatypes.

    apply subject_reduction with v; auto with coc core arith datatypes.
  Qed.

(*END TYPAGE GOES HERE*)

Hint Resolve ins_O ins_S: coc.
Hint Resolve sub_O sub_S: coc.
Hint Resolve red1_env_hd red1_env_tl: coc.
*)

(*
End Typage.
*)