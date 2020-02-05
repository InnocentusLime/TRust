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

Implicit Types i k m n p : nat.

Section Termes.

  (* The possible sorts we may have *)
  Inductive sort : Set :=
  | kind : sort
  | prop : sort
  | set : sort
  .

  Implicit Type s : sort.

  Definition is_prop s := s = prop \/ s = set.

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
  | Srt : sort -> term
  | Ref : nat -> term
  | Abs : term -> term -> term
  | App : term -> term -> term
  | Prod : term -> term -> term
  (* Natural numbers *)
  | Nat : term
  | NatO : term
  | NatSucc : term -> term
  (* Natural number eliminators *)
  | NatDestruct : term -> term -> term -> term -> term
  | NatCases : term -> term -> term -> term -> term
  (* Natural number recursors *)
  | NatRec : term -> term -> term -> term -> term
  | NatInd : term -> term -> term -> term -> term
  (* Well founded induction *)
  | AccProp : term -> term -> term -> term
  | AccIntro : term -> term -> term -> term -> term
  | AccRec : term -> term -> term -> term -> term -> term -> term
  | AccInd : term -> term -> term -> term -> term -> term -> term
  (* Order for naturals *)
  | Le : term -> term -> term
  | LeN : term -> term
  | LeS : term -> term -> term -> term
  | LeCases : term -> term -> term -> term -> term -> term -> term
  | LeInd : term -> term -> term -> term -> term -> term -> term
  (* Bool and SumBool *)
  | Bool : term
  | SumBool : term -> term -> term
  | BoolTrue : term
  | BoolFalse : term
  | SumBoolLeft : term -> term -> term -> term
  | SumBoolRight : term -> term -> term -> term
  | BoolInd : term -> term -> term -> term -> term
  | BoolRec : term -> term -> term -> term -> term
  | SumBoolInd : term -> term -> term -> term -> term -> term -> term 
  | SumBoolRec : term -> term -> term -> term -> term -> term -> term
  (* Refinment types *)
  | Refine : term -> term -> term
  | RefineConstr : term -> term -> term -> term -> term
  | RefineProjVal : term -> term -> term -> term
  | RefineProjProof : term -> term -> term -> term
  (* Equality *)
  | Eq : term -> term -> term -> term
  | EqRefl : term -> term -> term
  | EqInd : term -> term -> term -> term -> term -> term -> term
  | EqRec : term -> term -> term -> term -> term -> term -> term
  (* Falsity *)
  | Falsity : term
  | FalseInd : term -> term -> term
  | FalseRec : term -> term -> term
  (* Unit *)
  | Unit : term
  | Nil : term
  (* Well-founded recursion notation *)
  | WFrec : term -> term -> term -> term -> term -> term
  (* proposition choice with bool *)
  | BoolPropChoice : term -> term -> term -> term
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
    | Srt s => Srt s
    | Ref i =>
        match le_gt_dec k i with
        | left _ => Ref (n + i)
        | right _ => Ref i
        end
    | Abs T M => Abs (lift_rec n T k) (lift_rec n M (S k))
    | App u v => App (lift_rec n u k) (lift_rec n v k)
    | Prod A B => Prod (lift_rec n A k) (lift_rec n B (S k))
    (* Natural numbers *)
    | Nat => Nat
    | NatO => NatO
    | NatSucc x => NatSucc (lift_rec n x k)
    (* Eliminators *)
    | NatDestruct choice on_zero on_succ num => NatDestruct (lift_rec n choice k) (lift_rec n on_zero k) (lift_rec n on_succ k) (lift_rec n num k)
    | NatCases choice on_zero on_succ num => NatCases (lift_rec n choice k) (lift_rec n on_zero k) (lift_rec n on_succ k) (lift_rec n num k)
    (* Recursors *)
    | NatRec choice on_zero on_succ num => NatRec (lift_rec n choice k) (lift_rec n on_zero k) (lift_rec n on_succ k) (lift_rec n num k)
    | NatInd choice on_zero on_succ num => NatInd (lift_rec n choice k) (lift_rec n on_zero k) (lift_rec n on_succ k) (lift_rec n num k)
    (* Well founded induction *)
    | AccProp type rel x => AccProp (lift_rec n type k) (lift_rec n rel k) (lift_rec n x k)
    | AccIntro type rel x proof => AccIntro (lift_rec n type k) (lift_rec n rel k) (lift_rec n x k) (lift_rec n proof k)
    | AccRec type rel choice f val proof => AccRec (lift_rec n type k) (lift_rec n rel k) (lift_rec n choice k) (lift_rec n f k) (lift_rec n val k) (lift_rec n proof k)
    | AccInd type rel choice f val proof => AccInd (lift_rec n type k) (lift_rec n rel k) (lift_rec n choice k) (lift_rec n f k) (lift_rec n val k) (lift_rec n proof k)
    (* Order for naturals *)
    | Le l r => Le (lift_rec n l k) (lift_rec n r k)
    | LeN x => LeN (lift_rec n x k)
    | LeS l r proof => LeS (lift_rec n l k) (lift_rec n r k) (lift_rec n proof k)
    | LeCases choice on_le_n on_le_s l r proof => LeCases (lift_rec n choice k) (lift_rec n on_le_n k) (lift_rec n on_le_s k) (lift_rec n l k) (lift_rec n r k) (lift_rec n proof k)
    | LeInd choice on_le_n on_le_s l r proof => LeInd (lift_rec n choice k) (lift_rec n on_le_n k) (lift_rec n on_le_s k) (lift_rec n l k) (lift_rec n r k) (lift_rec n proof k)
    (* Bool and SumBool *)
    | Bool => Bool
    | SumBool l r => SumBool (lift_rec n l k) (lift_rec n r k)
    | BoolTrue => BoolTrue
    | BoolFalse => BoolFalse
    | SumBoolLeft left_pred right_pred proof => SumBoolLeft (lift_rec n left_pred k) (lift_rec n right_pred k) (lift_rec n proof k)
    | SumBoolRight left_pred right_pred proof => SumBoolRight (lift_rec n left_pred k) (lift_rec n right_pred k) (lift_rec n proof k)
    | BoolInd choice on_true on_false bool => BoolInd (lift_rec n choice k) (lift_rec n on_true k) (lift_rec n on_false k) (lift_rec n bool k)
    | BoolRec choice on_true on_false bool => BoolRec (lift_rec n choice k) (lift_rec n on_true k) (lift_rec n on_false k) (lift_rec n bool k)
    | SumBoolInd left_pred right_pred choice on_left on_right val => SumBoolInd (lift_rec n left_pred k) (lift_rec n right_pred k) (lift_rec n choice k) (lift_rec n on_left k) (lift_rec n on_right k) (lift_rec n val k)
    | SumBoolRec left_pred right_pred choice on_left on_right val => SumBoolRec (lift_rec n left_pred k) (lift_rec n right_pred k) (lift_rec n choice k) (lift_rec n on_left k) (lift_rec n on_right k) (lift_rec n val k)
    (* Refinment types *)
    | Refine type property => Refine (lift_rec n type k) (lift_rec n property k)
    | RefineConstr type property val proof => RefineConstr (lift_rec n type k) (lift_rec n property k) (lift_rec n val k) (lift_rec n proof k)
    | RefineProjVal type property ref => RefineProjVal (lift_rec n type k) (lift_rec n property k) (lift_rec n ref k)
    | RefineProjProof type property ref => RefineProjProof (lift_rec n type k) (lift_rec n property k) (lift_rec n ref k)
    (* Equality *)
    | Eq type l r => Eq (lift_rec n type k) (lift_rec n l k) (lift_rec n r k)
    | EqRefl type val => EqRefl (lift_rec n type k) (lift_rec n val k)
    | EqInd type l r property impl proof => EqInd (lift_rec n type k) (lift_rec n l k) (lift_rec n r k) (lift_rec n property k) (lift_rec n impl k) (lift_rec n proof k)
    | EqRec type l r property impl proof => EqRec (lift_rec n type k) (lift_rec n l k) (lift_rec n r k) (lift_rec n property k) (lift_rec n impl k) (lift_rec n proof k)
    (* Falsity *)
    | Falsity => Falsity
    | FalseInd proof property => FalseInd (lift_rec n proof k) (lift_rec n property k)
    | FalseRec proof property => FalseRec (lift_rec n proof k) (lift_rec n property k)
    (* Unit *)
    | Unit => Unit
    | Nil => Nil
    (* well-founded recursion scheme *)
    | WFrec type rel choice f proof => WFrec (lift_rec n type k) (lift_rec n rel k) (lift_rec n choice k) (lift_rec n f k) (lift_rec n proof k)
    (* proposition choice with bool *)
    | BoolPropChoice on_true on_false val => BoolPropChoice (lift_rec n on_true k) (lift_rec n on_false k) (lift_rec n val k)
    end
  .

  (* A shortcut *)
  Definition lift n t := lift_rec n t 0.

  (* 
    Substitution. A quit tricky definition, 
    but it does do lifting, just in a tricky
    hacky delayed way
  *)
  Fixpoint subst_rec N M {struct M} : nat -> term :=
    fun k =>
    match M with
    | Srt s => Srt s
    | Ref i =>
        match lt_eq_lt_dec k i with
        | inleft C =>
            match C with
            | left _ => Ref (pred i)
            | right _ => lift k N
            end
        | inright _ => Ref i
        end
    | Abs A B => Abs (subst_rec N A k) (subst_rec N B (S k))
    | App u v => App (subst_rec N u k) (subst_rec N v k)
    | Prod T U => Prod (subst_rec N T k) (subst_rec N U (S k))
    (* Natural numbers *)
    | Nat => Nat
    | NatO => NatO
    | NatSucc x => NatSucc (subst_rec N x k)
    (* Eliminators of natural numbers *)
    | NatDestruct choice on_zero on_succ num => NatDestruct (subst_rec N choice k) (subst_rec N on_zero k) (subst_rec N on_succ k) (subst_rec N num k)
    | NatCases choice on_zero on_succ num => NatCases (subst_rec N choice k) (subst_rec N on_zero k) (subst_rec N on_succ k) (subst_rec N num k)
    (* Recursors on natural numbers *)
    | NatRec choice on_zero on_succ num => NatRec (subst_rec N choice k) (subst_rec N on_zero k) (subst_rec N on_succ k) (subst_rec N num k)
    | NatInd choice on_zero on_succ num => NatInd (subst_rec N choice k) (subst_rec N on_zero k) (subst_rec N on_succ k) (subst_rec N num k)
    (* Well founded induction *)
    | AccProp type rel x => AccProp (subst_rec N type k) (subst_rec N rel k) (subst_rec N x k)
    | AccIntro type rel x proof => AccIntro (subst_rec N type k) (subst_rec N rel k) (subst_rec N x k) (subst_rec N proof k)
    | AccRec type rel choice f val proof => AccRec (subst_rec N type k) (subst_rec N rel k) (subst_rec N choice k) (subst_rec N f k) (subst_rec N val k) (subst_rec N proof k)
    | AccInd type rel choice f val proof => AccInd (subst_rec N type k) (subst_rec N rel k) (subst_rec N choice k) (subst_rec N f k) (subst_rec N val k) (subst_rec N proof k)
    (* Order for naturals *)
    | Le l r => Le (subst_rec N l k) (subst_rec N r k)
    | LeN x => LeN (subst_rec N x k)
    | LeS l r proof => LeS (subst_rec N l k) (subst_rec N r k) (subst_rec N proof k)
    | LeCases choice on_le_n on_le_s l r proof => LeCases (subst_rec N choice k) (subst_rec N on_le_n k) (subst_rec N on_le_s k) (subst_rec N l k) (subst_rec N r k) (subst_rec N proof k)
    | LeInd choice on_le_n on_le_s l r proof => LeInd (subst_rec N choice k) (subst_rec N on_le_n k) (subst_rec N on_le_s k) (subst_rec N l k) (subst_rec N r k) (subst_rec N proof k)
    (* Bool and SumBool *)
    | Bool => Bool
    | SumBool l r => SumBool (subst_rec N l k) (subst_rec N r k)
    | BoolTrue => BoolTrue
    | BoolFalse => BoolFalse
    | SumBoolLeft left_pred right_pred proof => SumBoolLeft (subst_rec N left_pred k) (subst_rec N right_pred k) (subst_rec N proof k)
    | SumBoolRight left_pred right_pred proof => SumBoolRight (subst_rec N left_pred k) (subst_rec N right_pred k) (subst_rec N proof k)
    | BoolInd choice on_true on_false bool => BoolInd (subst_rec N choice k) (subst_rec N on_true k) (subst_rec N on_false k) (subst_rec N bool k)
    | BoolRec choice on_true on_false bool => BoolRec (subst_rec N choice k) (subst_rec N on_true k) (subst_rec N on_false k) (subst_rec N bool k)
    | SumBoolInd left_pred right_pred choice on_left on_right val => SumBoolInd (subst_rec N left_pred k) (subst_rec N right_pred k) (subst_rec N choice k) (subst_rec N on_left k) (subst_rec N on_right k) (subst_rec N val k)
    | SumBoolRec left_pred right_pred choice on_left on_right val => SumBoolRec (subst_rec N left_pred k) (subst_rec N right_pred k) (subst_rec N choice k) (subst_rec N on_left k) (subst_rec N on_right k) (subst_rec N val k)
    (* Refinment types *)
    | Refine type property => Refine (subst_rec N type k) (subst_rec N property k)
    | RefineConstr type property val proof => RefineConstr (subst_rec N type k) (subst_rec N property k) (subst_rec N val k) (subst_rec N proof k)
    | RefineProjVal type property ref => RefineProjVal (subst_rec N type k) (subst_rec N property k) (subst_rec N ref k)
    | RefineProjProof type property ref => RefineProjProof (subst_rec N type k) (subst_rec N property k) (subst_rec N ref k)
    (* Equality *)
    | Eq type l r => Eq (subst_rec N type k) (subst_rec N l k) (subst_rec N r k)
    | EqRefl type val => EqRefl (subst_rec N type k) (subst_rec N val k)
    | EqInd type l r property impl proof => EqInd (subst_rec N type k) (subst_rec N l k) (subst_rec N r k) (subst_rec N property k) (subst_rec N impl k) (subst_rec N proof k)
    | EqRec type l r property impl proof => EqRec (subst_rec N type k) (subst_rec N l k) (subst_rec N r k) (subst_rec N property k) (subst_rec N impl k) (subst_rec N proof k)
    (* Falsity *)
    | Falsity => Falsity
    | FalseInd proof property => FalseInd (subst_rec N proof k) (subst_rec N property k)
    | FalseRec proof property => FalseRec (subst_rec N proof k) (subst_rec N property k)
    (* Unit *)
    | Unit => Unit
    | Nil => Nil
    (* well-founded recursion scheme *)
    | WFrec type rel choice f proof => WFrec (subst_rec N type k) (subst_rec N rel k) (subst_rec N choice k) (subst_rec N f k) (subst_rec N proof k)
    (* proposition choice with bool *)
    | BoolPropChoice on_true on_false val => BoolPropChoice (subst_rec N on_true k) (subst_rec N on_false k) (subst_rec N val k)
    end
  .

  (* Shortcut *)
  Definition subst N M := subst_rec N M 0.

  (* 
    The predicate to check if a variable is not used in a term.

    That predicate has an additional guarantee:
    every variable grater than the one satisfying `free_db` 
    satisfies `free_db` too!
  *)
  Inductive free_db : nat -> term -> Prop :=
  | db_srt : forall n s, free_db n (Srt s)
  | db_ref : forall k n, k > n -> free_db k (Ref n)
  | db_abs :
    forall k A M, free_db k A -> free_db (S k) M -> free_db k (Abs A M)
  | db_app :
    forall k u v, free_db k u -> free_db k v -> free_db k (App u v)
  | db_prod :
    forall k A B, free_db k A -> free_db (S k) B -> free_db k (Prod A B)
  (* Natural numbers *)
  | db_nat : forall n, free_db n Nat
  | db_nat_o : forall n, free_db n NatO
  | db_nat_succ : forall n x, free_db n x -> free_db n (NatSucc x)
  (* Natural number's eliminators *)
  | db_nat_destruct : forall n choice on_zero on_succ num, free_db n choice -> free_db n on_zero -> free_db n on_succ -> free_db n num -> free_db n (NatDestruct choice on_zero on_succ num)
  | db_nat_cases : forall n choice on_zero on_succ num, free_db n choice -> free_db n on_zero -> free_db n on_succ -> free_db n num -> free_db n (NatCases choice on_zero on_succ num)
  (* Recursors for natural numbers *)
  | db_nat_rec : forall n choice on_zero on_succ num, free_db n choice -> free_db n on_zero -> free_db n on_succ -> free_db n num -> free_db n (NatRec choice on_zero on_succ num)
  | db_nat_ind : forall n choice on_zero on_succ num, free_db n choice -> free_db n on_zero -> free_db n on_succ -> free_db n num -> free_db n (NatInd choice on_zero on_succ num)
  (* Well founded induction *)
  | db_acc_prop : forall n type rel x, free_db n type -> free_db n rel -> free_db n x -> free_db n (AccProp type rel x)
  | db_acc_intro : forall n type rel x proof, free_db n type -> free_db n rel -> free_db n x -> free_db n proof -> free_db n (AccIntro type rel x proof)
  | db_acc_rec : forall n type rel choice f val proof, free_db n type -> free_db n rel -> free_db n choice -> free_db n f -> free_db n choice -> free_db n val -> free_db n (AccRec type rel choice f val proof)
  | db_acc_ind : forall n type rel choice f val proof, free_db n type -> free_db n rel -> free_db n choice -> free_db n f -> free_db n choice -> free_db n val -> free_db n (AccInd type rel choice f val proof)
  (* Order for naturals *)
  | db_le : forall n l r, free_db n l -> free_db n r -> free_db n (Le l r)
  | db_le_n : forall n num, free_db n num -> free_db n (LeN num)
  | db_le_s : forall n l r proof, free_db n l -> free_db n r -> free_db n proof -> free_db n (LeS l r proof)
  | db_le_cases : forall n choice on_le_n on_le_s l r proof, free_db n choice -> free_db n on_le_n -> free_db n on_le_s -> free_db n l -> free_db n r -> free_db n proof -> free_db n (LeCases choice on_le_n on_le_s l r proof)
  | db_le_ind : forall n choice on_le_n on_le_s l r proof, free_db n choice -> free_db n on_le_n -> free_db n on_le_s -> free_db n l -> free_db n r -> free_db n proof -> free_db n (LeInd choice on_le_n on_le_s l r proof)
  (* Bool and SumBool *)
  | db_bool : forall n, free_db n Bool
  | db_sum_bool : forall n l r, free_db n l -> free_db n r -> free_db n (SumBool l r)
  | db_bool_true : forall n, free_db n BoolTrue
  | db_bool_false : forall n, free_db n BoolFalse
  | db_sumbool_left : forall n left_pred right_pred proof, free_db n left_pred -> free_db n right_pred -> free_db n proof -> free_db n (SumBoolLeft left_pred right_pred proof)
  | db_sumbool_right : forall n left_pred right_pred proof, free_db n left_pred -> free_db n right_pred -> free_db n proof -> free_db n (SumBoolRight left_pred right_pred proof)
  | db_bool_ind : forall n choice on_true on_false bool, free_db n choice -> free_db n on_true -> free_db n on_false -> free_db n bool -> free_db n (BoolInd choice on_true on_false bool)
  | db_bool_rec : forall n choice on_true on_false bool, free_db n choice -> free_db n on_true -> free_db n on_false -> free_db n bool -> free_db n (BoolRec choice on_true on_false bool)
  | db_sumbool_ind : forall n left_pred right_pred choice on_left on_right val, free_db n left_pred -> free_db n right_pred -> free_db n choice -> free_db n on_left -> free_db n on_right -> free_db n val -> free_db n (SumBoolInd left_pred right_pred choice on_left on_right val)
  | db_sumbool_rec : forall n left_pred right_pred choice on_left on_right val, free_db n left_pred -> free_db n right_pred -> free_db n choice -> free_db n on_left -> free_db n on_right -> free_db n val -> free_db n (SumBoolRec left_pred right_pred choice on_left on_right val)
  (* Refinment types *)
  | db_refine : forall n type property, free_db n type -> free_db n property -> free_db n (Refine type property)
  | db_refine_constr : forall n type property val proof, free_db n type -> free_db n property -> free_db n val -> free_db n proof -> free_db n (RefineConstr type property val proof)
  | db_refine_proj_val : forall n type property ref, free_db n type -> free_db n property -> free_db n ref -> free_db n (RefineProjVal type property ref) 
  | db_refine_proj_proof : forall n type property ref, free_db n type -> free_db n property -> free_db n ref -> free_db n (RefineProjProof type property ref) 
  (* Equality *)
  | db_eq_prop : forall n type l r, free_db n type -> free_db n l -> free_db n r -> free_db n (Eq type l r)
  | db_eq_refl : forall n type val, free_db n type -> free_db n val -> free_db n (EqRefl type val)
  | db_eq_ind : forall n type l r property impl proof, free_db n type -> free_db n l -> free_db n r -> free_db n property -> free_db n impl -> free_db n proof -> free_db n (EqInd type l r property impl proof)
  | db_eq_rec : forall n type l r property impl proof, free_db n type -> free_db n l -> free_db n r -> free_db n property -> free_db n impl -> free_db n proof -> free_db n (EqRec type l r property impl proof)
  (* Falsity *)
  | db_falsity : forall n, free_db n Falsity
  | db_false_ind : forall n proof property, free_db n proof -> free_db n property -> free_db n (FalseInd proof property)
  | db_false_rec : forall n proof property, free_db n proof -> free_db n property -> free_db n (FalseRec proof property)
  (* Unit *)
  | db_unit : forall n, free_db n Unit
  | db_nil : forall n, free_db n Nil
  (* Well-founded recursion notation *)
  | db_WFrec : forall n type rel choice f proof, free_db n type -> free_db n rel -> free_db n choice -> free_db n f -> free_db n proof -> free_db n (WFrec type rel choice f proof)
  (* bool proposition choice *)
  | db_bool_prop_choice : forall n on_true on_false val, free_db n on_true -> free_db n on_false -> free_db n val -> free_db n (BoolPropChoice on_true on_false val)
  .

  (* Check if a term is a subterm under the binding *)
  Inductive subt_bind T M : term -> Prop :=
  | Bsbt_abs : subt_bind T M (Abs T M)
  | Bsbt_prod : subt_bind T M (Prod T M)
  .

  (* Check if a term is a subterm, but not under the binding *)
  Inductive subt_nobind (m : term) : term -> Prop :=
  | Nbsbt_abs : forall n : term, subt_nobind m (Abs m n)
  | Nbsbt_app_l : forall v, subt_nobind m (App m v)
  | Nbsbt_app_r : forall u, subt_nobind m (App u m)
  | Nbsbt_prod : forall n : term, subt_nobind m (Prod m n)
  (* Natural numbers eliminators *)
  | Nbsbt_nat_destruct_choice : forall a2 a3 a4, subt_nobind m (NatDestruct m a2 a3 a4)
  | Nbsbt_nat_destruct_on_zero : forall a1 a3 a4, subt_nobind m (NatDestruct a1 m a3 a4)
  | Nbsbt_nat_destruct_on_succ : forall a1 a2 a4, subt_nobind m (NatDestruct a1 a2 m a4)
  | Nbsbt_nat_destruct_num : forall a1 a2 a3, subt_nobind m (NatDestruct a1 a2 a3 m)
  | Nbsbt_nat_cases_choice : forall a2 a3 a4, subt_nobind m (NatCases m a2 a3 a4)
  | Nbsbt_nat_cases_on_zero : forall a1 a3 a4, subt_nobind m (NatCases a1 m a3 a4)
  | Nbsbt_nat_cases_on_succ : forall a1 a2 a4, subt_nobind m (NatCases a1 a2 m a4)
  | Nbsbt_nat_cases_num : forall a1 a2 a3, subt_nobind m (NatCases a1 a2 a3 m)
  (* Natural number constructors *)
  | Nbsbt_nat_succ : subt_nobind m (NatSucc m)
  (* Natural number recursors *)
  | Nbsbt_nat_rec_choice : forall a2 a3 a4, subt_nobind m (NatRec m a2 a3 a4)
  | Nbsbt_nat_rec_on_zero : forall a1 a3 a4, subt_nobind m (NatRec a1 m a3 a4)
  | Nbsbt_nat_rec_on_succ : forall a1 a2 a4, subt_nobind m (NatRec a1 a2 m a4)
  | Nbsbt_nat_rec_num : forall a1 a2 a3, subt_nobind m (NatRec a1 a2 a3 m)
  | Nbsbt_nat_ind_choice : forall a2 a3 a4, subt_nobind m (NatInd m a2 a3 a4)
  | Nbsbt_nat_ind_on_zero : forall a1 a3 a4, subt_nobind m (NatInd a1 m a3 a4)
  | Nbsbt_nat_ind_on_succ : forall a1 a2 a4, subt_nobind m (NatInd a1 a2 m a4)
  | Nbsbt_nat_ind_num : forall a1 a2 a3, subt_nobind m (NatInd a1 a2 a3 m)
  (* Well founded induction *)
  | Nsbt_acc_prop_type : forall a2 a3, subt_nobind m (AccProp m a2 a3)
  | Nsbt_acc_prop_rel : forall a1 a3, subt_nobind m (AccProp a1 m a3)
  | Nsbt_acc_prop_val : forall a1 a2, subt_nobind m (AccProp a1 a2 m)
  | Nsbt_acc_intro_type : forall a2 a3 a4, subt_nobind m (AccIntro m a2 a3 a4)
  | Nsbt_acc_intro_rel : forall a1 a3 a4, subt_nobind m (AccIntro a1 m a3 a4)
  | Nsbt_acc_intro_val : forall a1 a2 a4, subt_nobind m (AccIntro a1 a2 m a4)
  | Nsbt_acc_intro_proof : forall a1 a2 a3, subt_nobind m (AccIntro a1 a2 a3 m)
  | Nsbt_acc_rec_type : forall a2 a3 a4 a5 a6, subt_nobind m (AccRec m a2 a3 a4 a5 a6)
  | Nsbt_acc_rec_rel : forall a1 a3 a4 a5 a6, subt_nobind m (AccRec a1 m a3 a4 a5 a6)
  | Nsbt_acc_rec_choice : forall a1 a2 a4 a5 a6, subt_nobind m (AccRec a1 a2 m a4 a5 a6)
  | Nsbt_acc_rec_func : forall a1 a2 a3 a5 a6, subt_nobind m (AccRec a1 a2 a3 m a5 a6)
  | Nsbt_acc_rec_val : forall a1 a2 a3 a4 a6, subt_nobind m (AccRec a1 a2 a3 a4 m a6)
  | Nsbt_acc_rec_proof : forall a1 a2 a3 a4 a5, subt_nobind m (AccRec a1 a2 a3 a4 a5 m)
  | Nsbt_acc_ind_type : forall a2 a3 a4 a5 a6, subt_nobind m (AccInd m a2 a3 a4 a5 a6)
  | Nsbt_acc_ind_rel : forall a1 a3 a4 a5 a6, subt_nobind m (AccInd a1 m a3 a4 a5 a6)
  | Nsbt_acc_ind_choice : forall a1 a2 a4 a5 a6, subt_nobind m (AccInd a1 a2 m a4 a5 a6)
  | Nsbt_acc_ind_func : forall a1 a2 a3 a5 a6, subt_nobind m (AccInd a1 a2 a3 m a5 a6)
  | Nsbt_acc_ind_val : forall a1 a2 a3 a4 a6, subt_nobind m (AccInd a1 a2 a3 a4 m a6)
  | Nsbt_acc_ind_proof : forall a1 a2 a3 a4 a5, subt_nobind m (AccInd a1 a2 a3 a4 a5 m)
  (* Order on natural numbers *)
  | Nsbt_le_prop_l : forall a2, subt_nobind m (Le m a2)
  | Nsbt_le_prop_r : forall a1, subt_nobind m (Le a1 m)
  | Nsbt_le_n : subt_nobind m (LeN m)
  | Nsbt_le_s_l : forall a2 a3, subt_nobind m (LeS m a2 a3)
  | Nsbt_le_s_r : forall a1 a3, subt_nobind m (LeS a1 m a3)
  | Nsbt_le_s_proof : forall a1 a2, subt_nobind m (LeS a1 a2 m)
  | Nsbt_le_cases_choice : forall a2 a3 a4 a5 a6, subt_nobind m (LeCases m a2 a3 a4 a5 a6)
  | Nsbt_le_cases_onLN : forall a1 a3 a4 a5 a6, subt_nobind m (LeCases a1 m a3 a4 a5 a6)
  | Nsbt_le_cases_onLS : forall a1 a2 a4 a5 a6, subt_nobind m (LeCases a1 a2 m a4 a5 a6)
  | Nsbt_le_cases_l : forall a1 a2 a3 a5 a6, subt_nobind m (LeCases a1 a2 a3 m a5 a6)
  | Nsbt_le_cases_r : forall a1 a2 a3 a4 a6, subt_nobind m (LeCases a1 a2 a3 a4 m a6)
  | Nsbt_le_cases_proof : forall a1 a2 a3 a4 a5, subt_nobind m (LeCases a1 a2 a3 a4 a5 m)
  | Nsbt_le_ind_choice : forall a2 a3 a4 a5 a6, subt_nobind m (LeInd m a2 a3 a4 a5 a6)
  | Nsbt_le_ind_onLN : forall a1 a3 a4 a5 a6, subt_nobind m (LeInd a1 m a3 a4 a5 a6)
  | Nsbt_le_ind_onLS : forall a1 a2 a4 a5 a6, subt_nobind m (LeInd a1 a2 m a4 a5 a6)
  | Nsbt_le_ind_l : forall a1 a2 a3 a5 a6, subt_nobind m (LeInd a1 a2 a3 m a5 a6)
  | Nsbt_le_ind_r : forall a1 a2 a3 a4 a6, subt_nobind m (LeInd a1 a2 a3 a4 m a6)
  | Nsbt_le_ind_proof : forall a1 a2 a3 a4 a5, subt_nobind m (LeInd a1 a2 a3 a4 a5 m)
  (* Bools *)
  | Nsbt_sumbool_l : forall a2, subt_nobind m (SumBool m a2)
  | Nsbt_sumbool_r : forall a1, subt_nobind m (SumBool a1 m)
  | Nsbt_sumbool_left_l_pred : forall a2 a3, subt_nobind m (SumBoolLeft m a2 a3)
  | Nsbt_sumbool_left_r_pred : forall a1 a3, subt_nobind m (SumBoolLeft a1 m a3)
  | Nsbt_sumbool_left_proof : forall a1 a2, subt_nobind m (SumBoolLeft a1 a2 m)
  | Nsbt_sumbool_right_l_pred : forall a2 a3, subt_nobind m (SumBoolRight m a2 a3)
  | Nsbt_sumbool_right_r_pred : forall a1 a3, subt_nobind m (SumBoolRight a1 m a3)
  | Nsbt_sumbool_right_proof : forall a1 a2, subt_nobind m (SumBoolRight a1 a2 m)
  | Nsbt_bool_ind_choice : forall a2 a3 a4, subt_nobind m (BoolInd m a2 a3 a4)
  | Nsbt_bool_ind_on_true : forall a1 a3 a4, subt_nobind m (BoolInd a1 m a3 a4)
  | Nsbt_bool_ind_on_false : forall a1 a2 a4, subt_nobind m (BoolInd a1 a2 m a4)
  | Nsbt_bool_ind_val : forall a1 a2 a3, subt_nobind m (BoolInd a1 a2 a3 m)
  | Nsbt_bool_rec_choice : forall a2 a3 a4, subt_nobind m (BoolRec m a2 a3 a4)
  | Nsbt_bool_rec_on_true : forall a1 a3 a4, subt_nobind m (BoolRec a1 m a3 a4)
  | Nsbt_bool_rec_on_false : forall a1 a2 a4, subt_nobind m (BoolRec a1 a2 m a4)
  | Nsbt_bool_rec_val : forall a1 a2 a3, subt_nobind m (BoolRec a1 a2 a3 m)
  | Nsbt_sumbool_ind_l_pred : forall a2 a3 a4 a5 a6, subt_nobind m (SumBoolInd m a2 a3 a4 a5 a6)
  | Nsbt_sumbool_ind_r_pred : forall a1 a3 a4 a5 a6, subt_nobind m (SumBoolInd a1 m a3 a4 a5 a6)
  | Nsbt_sumbool_ind_choice : forall a1 a2 a4 a5 a6, subt_nobind m (SumBoolInd a1 a2 m a4 a5 a6)
  | Nsbt_sumbool_ind_on_left : forall a1 a2 a3 a5 a6, subt_nobind m (SumBoolInd a1 a2 a3 m a5 a6)
  | Nsbt_sumbool_ind_on_right : forall a1 a2 a3 a4 a6, subt_nobind m (SumBoolInd a1 a2 a3 a4 m a6)
  | Nsbt_sumbool_ind_val : forall a1 a2 a3 a4 a5, subt_nobind m (SumBoolInd a1 a2 a3 a4 a5 m)
  | Nsbt_sumbool_rec_l_pred : forall a2 a3 a4 a5 a6, subt_nobind m (SumBoolRec m a2 a3 a4 a5 a6)
  | Nsbt_sumbool_rec_r_pred : forall a1 a3 a4 a5 a6, subt_nobind m (SumBoolRec a1 m a3 a4 a5 a6)
  | Nsbt_sumbool_rec_choice : forall a1 a2 a4 a5 a6, subt_nobind m (SumBoolRec a1 a2 m a4 a5 a6)
  | Nsbt_sumbool_rec_on_left : forall a1 a2 a3 a5 a6, subt_nobind m (SumBoolRec a1 a2 a3 m a5 a6)
  | Nsbt_sumbool_rec_on_right : forall a1 a2 a3 a4 a6, subt_nobind m (SumBoolRec a1 a2 a3 a4 m a6)
  | Nsbt_sumbool_rec_val : forall a1 a2 a3 a4 a5, subt_nobind m (SumBoolRec a1 a2 a3 a4 a5 m)
  (* Refinement types *)
  | Nsbt_refine_type : forall a2, subt_nobind m (Refine m a2)
  | Nsbt_refine_property : forall a1, subt_nobind m (Refine a1 m)
  | Nsbt_refine_constr_type : forall a2 a3 a4, subt_nobind m (RefineConstr m a2 a3 a4)
  | Nsbt_refine_constr_pred : forall a1 a3 a4, subt_nobind m (RefineConstr a1 m a3 a4)
  | Nsbt_refine_constr_val : forall a1 a2 a4, subt_nobind m (RefineConstr a1 a2 m a4)
  | Nsbt_refine_constr_proof : forall a1 a2 a3, subt_nobind m (RefineConstr a1 a2 a3 m)
  | Nsbt_refine_proj_val_type : forall a2 a3, subt_nobind m (RefineProjVal m a2 a3)
  | Nsbt_refine_proj_val_property : forall a1 a3, subt_nobind m (RefineProjVal a1 m a3)
  | Nsbt_refine_proj_val_ref : forall a1 a2, subt_nobind m (RefineProjVal a1 a2 m)
  | Nsbt_refine_proj_proof_type : forall a2 a3, subt_nobind m (RefineProjProof m a2 a3)
  | Nsbt_refine_proj_proof_property : forall a1 a3, subt_nobind m (RefineProjProof a1 m a3)
  | Nsbt_refine_proj_proof_ref : forall a1 a2, subt_nobind m (RefineProjProof a1 a2 m)
  (* Equality *)
  | Nsbt_eq_prop_type : forall a2 a3, subt_nobind m (Eq m a2 a3)
  | Nsbt_eq_prop_l : forall a1 a3, subt_nobind m (Eq a1 m a3)
  | Nsbt_eq_prop_r : forall a1 a2, subt_nobind m (Eq a1 a2 m)
  | Nsbt_eq_refl_type : forall a2, subt_nobind m (EqRefl m a2)
  | Nsbt_eq_refl_val : forall a1, subt_nobind m (EqRefl a1 m)
  | Nsbt_eq_ind_type : forall a2 a3 a4 a5 a6, subt_nobind m (EqInd m a2 a3 a4 a5 a6)
  | Nsbt_eq_ind_l : forall a1 a3 a4 a5 a6, subt_nobind m (EqInd a1 m a3 a4 a5 a6)
  | Nsbt_eq_ind_r : forall a1 a2 a4 a5 a6, subt_nobind m (EqInd a1 a2 m a4 a5 a6)
  | Nsbt_eq_ind_property : forall a1 a2 a3 a5 a6, subt_nobind m (EqInd a1 a2 a3 m a5 a6)
  | Nsbt_eq_ind_impl : forall a1 a2 a3 a4 a6, subt_nobind m (EqInd a1 a2 a3 a4 m a6)
  | Nsbt_eq_ind_proof : forall a1 a2 a3 a4 a5, subt_nobind m (EqInd a1 a2 a3 a4 a5 m)
  | Nsbt_eq_rec_type : forall a2 a3 a4 a5 a6, subt_nobind m (EqRec m a2 a3 a4 a5 a6)
  | Nsbt_eq_rec_l : forall a1 a3 a4 a5 a6, subt_nobind m (EqRec a1 m a3 a4 a5 a6)
  | Nsbt_eq_rec_r : forall a1 a2 a4 a5 a6, subt_nobind m (EqRec a1 a2 m a4 a5 a6)
  | Nsbt_eq_rec_property : forall a1 a2 a3 a5 a6, subt_nobind m (EqRec a1 a2 a3 m a5 a6)
  | Nsbt_eq_rec_impl : forall a1 a2 a3 a4 a6, subt_nobind m (EqRec a1 a2 a3 a4 m a6)
  | Nsbt_eq_rec_proof : forall a1 a2 a3 a4 a5, subt_nobind m (EqRec a1 a2 a3 a4 a5 m)
  (* Falsity *)
  | Nsbt_false_ind_proof : forall a2, subt_nobind m (FalseInd m a2)
  | Nsbt_false_ind_prop : forall a1, subt_nobind m (FalseInd a1 m)
  | Nsbt_false_rec_proof : forall a2, subt_nobind m (FalseRec m a2)
  | Nsbt_false_rec_prop : forall a1, subt_nobind m (FalseRec a1 m)
  (* Unit has nothing *)
  (* well-founded recursion *)  
  | Nsbt_wf_rec_type : forall a2 a3 a4 a5, subt_nobind m (WFrec m a2 a3 a4 a5)
  | Nsbt_wf_rec_rel : forall a1 a3 a4 a5, subt_nobind m (WFrec a1 m a3 a4 a5)
  | Nsbt_wf_rec_choice : forall a1 a2 a4 a5, subt_nobind m (WFrec a1 a2 m a4 a5)
  | Nsbt_wf_rec_f : forall a1 a2 a3 a5, subt_nobind m (WFrec a1 a2 a3 m a5)
  | Nsbt_wf_rec_proof : forall a1 a2 a3 a4, subt_nobind m (WFrec a1 a2 a3 a4 m)
  (* bool proposition choice *)
  | Nsbt_bool_prop_choice_on_true : forall a2 a3, subt_nobind m (BoolPropChoice m a2 a3)
  | Nsbt_bool_prop_choice_on_false : forall a1 a3, subt_nobind m (BoolPropChoice a1 m a3)
  | Nsbt_bool_prop_choice_val : forall a1 a2, subt_nobind m (BoolPropChoice a1 a2 m)
  .

  (* Check if a term `m` is a subterm of `n` *)
  Inductive subterm (m n : term) : Prop :=
  | Sbtrm_bind : forall t, subt_bind t m n -> subterm m n
  | Sbtrm_nobind : subt_nobind m n -> subterm m n
  .

  (* TODO: check why this definition is unused. *)
  (*
    Definition mem_sort := fun (s:sort) (t:term) => (clos_refl_trans term subterm (Srt s) t).
  *)

  (* Check if a sort ocuurs in a term *)
  Inductive mem_sort s : term -> Prop :=
  | mem_eq : mem_sort s (Srt s)
  | mem_prod_l : forall u v, mem_sort s u -> mem_sort s (Prod u v)
  | mem_prod_r : forall u v, mem_sort s v -> mem_sort s (Prod u v)
  | mem_abs_l : forall u v, mem_sort s u -> mem_sort s (Abs u v)
  | mem_abs_r : forall u v, mem_sort s v -> mem_sort s (Abs u v)
  | mem_app_l : forall u v, mem_sort s u -> mem_sort s (App u v)
  | mem_app_r : forall u v, mem_sort s v -> mem_sort s (App u v)
  (* Natural number eliminators *)
  | mem_nat_destruct_choice : forall choice on_zero on_succ num, mem_sort s choice -> mem_sort s (NatDestruct choice on_zero on_succ num)
  | mem_nat_destruct_on_zero : forall choice on_zero on_succ num, mem_sort s on_zero -> mem_sort s (NatDestruct choice on_zero on_succ num)
  | mem_nat_destruct_on_succ : forall choice on_zero on_succ num, mem_sort s on_succ -> mem_sort s (NatDestruct choice on_zero on_succ num)
  | mem_nat_destruct_num : forall choice on_zero on_succ num, mem_sort s num -> mem_sort s (NatDestruct choice on_zero on_succ num)
  | mem_nat_cases_choice : forall choice on_zero on_succ num, mem_sort s choice -> mem_sort s (NatCases choice on_zero on_succ num)
  | mem_nat_cases_on_zero : forall choice on_zero on_succ num, mem_sort s on_zero -> mem_sort s (NatCases choice on_zero on_succ num)
  | mem_nat_cases_on_succ : forall choice on_zero on_succ num, mem_sort s on_succ -> mem_sort s (NatCases choice on_zero on_succ num)
  | mem_nat_cases_num : forall choice on_zero on_succ num, mem_sort s num -> mem_sort s (NatCases choice on_zero on_succ num)
  (* Natural numbers constructors *)
  | mem_nat_succ : forall x, mem_sort s x -> mem_sort s (NatSucc x)
  (* Natural number recursors *)
  | mem_nat_rec_choice : forall choice on_zero on_succ num, mem_sort s choice -> mem_sort s (NatRec choice on_zero on_succ num)
  | mem_nat_rec_on_zero : forall choice on_zero on_succ num, mem_sort s on_zero -> mem_sort s (NatRec choice on_zero on_succ num)
  | mem_nat_rec_on_succ : forall choice on_zero on_succ num, mem_sort s on_succ -> mem_sort s (NatRec choice on_zero on_succ num)
  | mem_nat_rec_num : forall choice on_zero on_succ num, mem_sort s num -> mem_sort s (NatRec choice on_zero on_succ num)
  | mem_nat_ind_choice : forall choice on_zero on_succ num, mem_sort s choice -> mem_sort s (NatInd choice on_zero on_succ num)
  | mem_nat_ind_on_zero : forall choice on_zero on_succ num, mem_sort s on_zero -> mem_sort s (NatInd choice on_zero on_succ num)
  | mem_nat_ind_on_succ : forall choice on_zero on_succ num, mem_sort s on_succ -> mem_sort s (NatInd choice on_zero on_succ num)
  | mem_nat_ind_num : forall choice on_zero on_succ num, mem_sort s num -> mem_sort s (NatInd choice on_zero on_succ num)
  (* Well founded induction *)
  | mem_acc_prop_type : forall type rel val, mem_sort s type -> mem_sort s (AccProp type rel val)
  | mem_acc_prop_rel : forall type rel val, mem_sort s rel -> mem_sort s (AccProp type rel val)
  | mem_acc_prop_val : forall type rel val, mem_sort s val -> mem_sort s (AccProp type rel val)
  | mem_acc_intro_type : forall type rel val proof, mem_sort s type -> mem_sort s (AccIntro type rel val proof)
  | mem_acc_intro_rel : forall type rel val proof, mem_sort s rel -> mem_sort s (AccIntro type rel val proof)
  | mem_acc_intro_val : forall type rel val proof, mem_sort s val -> mem_sort s (AccIntro type rel val proof)
  | mem_acc_intro_proof : forall type rel val proof, mem_sort s proof -> mem_sort s (AccIntro type rel val proof)
  | mem_acc_rec_type : forall type rel choice f val proof, mem_sort s type -> mem_sort s (AccRec type rel choice f val proof)
  | mem_acc_rec_rel : forall type rel choice f val proof, mem_sort s rel -> mem_sort s (AccRec type rel choice f val proof)
  | mem_acc_rec_choice : forall type rel choice f val proof, mem_sort s choice -> mem_sort s (AccRec type rel choice f val proof)
  | mem_acc_rec_f : forall type rel choice f val proof, mem_sort s f -> mem_sort s (AccRec type rel choice f val proof)
  | mem_acc_rec_val : forall type rel choice f val proof, mem_sort s val -> mem_sort s (AccRec type rel choice f val proof)
  | mem_acc_rec_proof : forall type rel choice f val proof, mem_sort s proof -> mem_sort s (AccRec type rel choice f val proof)
  | mem_acc_ind_type : forall type rel choice f val proof, mem_sort s type -> mem_sort s (AccInd type rel choice f val proof)
  | mem_acc_ind_rel : forall type rel choice f val proof, mem_sort s rel -> mem_sort s (AccInd type rel choice f val proof)
  | mem_acc_ind_choice : forall type rel choice f val proof, mem_sort s choice -> mem_sort s (AccInd type rel choice f val proof)
  | mem_acc_ind_f : forall type rel choice f val proof, mem_sort s f -> mem_sort s (AccInd type rel choice f val proof)
  | mem_acc_ind_val : forall type rel choice f val proof, mem_sort s val -> mem_sort s (AccInd type rel choice f val proof)
  | mem_acc_ind_proof : forall type rel choice f val proof, mem_sort s proof -> mem_sort s (AccInd type rel choice f val proof)
  (* Order for naturals *)
  | mem_le_prop_l : forall l r, mem_sort s l -> mem_sort s (Le l r)
  | mem_le_prop_r : forall l r, mem_sort s r -> mem_sort s (Le l r)
  | mem_le_n_n : forall n : term, mem_sort s n -> mem_sort s (LeN n)
  | mem_le_s_l : forall l r proof, mem_sort s l -> mem_sort s (LeS l r proof)
  | mem_le_s_r : forall l r proof, mem_sort s r -> mem_sort s (LeS l r proof)
  | mem_le_s_proof : forall l r proof, mem_sort s proof -> mem_sort s (LeS l r proof)
  | mem_le_cases_choice : forall choice on_le_n on_le_s l r proof, mem_sort s choice -> mem_sort s (LeCases choice on_le_n on_le_s l r proof)
  | mem_le_cases_on_le_n : forall choice on_le_n on_le_s l r proof, mem_sort s on_le_n -> mem_sort s (LeCases choice on_le_n on_le_s l r proof)
  | mem_le_cases_on_le_s : forall choice on_le_n on_le_s l r proof, mem_sort s on_le_s -> mem_sort s (LeCases choice on_le_n on_le_s l r proof)
  | mem_le_cases_l : forall choice on_le_n on_le_s l r proof, mem_sort s l -> mem_sort s (LeCases choice on_le_n on_le_s l r proof)
  | mem_le_cases_r : forall choice on_le_n on_le_s l r proof, mem_sort s r -> mem_sort s (LeCases choice on_le_n on_le_s l r proof)
  | mem_le_cases_proof : forall choice on_le_n on_le_s l r proof, mem_sort s proof -> mem_sort s (LeCases choice on_le_n on_le_s l r proof)
  | mem_le_ind_choice : forall choice on_le_n on_le_s l r proof, mem_sort s choice -> mem_sort s (LeInd choice on_le_n on_le_s l r proof)
  | mem_le_ind_on_le_n : forall choice on_le_n on_le_s l r proof, mem_sort s on_le_n -> mem_sort s (LeInd choice on_le_n on_le_s l r proof)
  | mem_le_ind_on_le_s : forall choice on_le_n on_le_s l r proof, mem_sort s on_le_s -> mem_sort s (LeInd choice on_le_n on_le_s l r proof)
  | mem_le_ind_l : forall choice on_le_n on_le_s l r proof, mem_sort s l -> mem_sort s (LeInd choice on_le_n on_le_s l r proof)
  | mem_le_ind_r : forall choice on_le_n on_le_s l r proof, mem_sort s r -> mem_sort s (LeInd choice on_le_n on_le_s l r proof)
  | mem_le_ind_proof : forall choice on_le_n on_le_s l r proof, mem_sort s proof -> mem_sort s (LeInd choice on_le_n on_le_s l r proof)
  (* Bool and SumBool *)
  | mem_sumbool_type_left_pred : forall left_pred right_pred, mem_sort s left_pred -> mem_sort s (SumBool left_pred right_pred)
  | mem_sumbool_type_right_pred : forall left_pred right_pred, mem_sort s right_pred -> mem_sort s (SumBool left_pred right_pred)
  | mem_sumbool_left_left_pred : forall left_pred right_pred proof, mem_sort s left_pred -> mem_sort s (SumBoolLeft left_pred right_pred proof)
  | mem_sumbool_left_right_pred : forall left_pred right_pred proof, mem_sort s right_pred -> mem_sort s (SumBoolLeft left_pred right_pred proof)
  | mem_sumbool_left_proof : forall left_pred right_pred proof, mem_sort s proof -> mem_sort s (SumBoolLeft left_pred right_pred proof)
  | mem_sumbool_right_left_pred : forall left_pred right_pred proof, mem_sort s left_pred -> mem_sort s (SumBoolRight left_pred right_pred proof)
  | mem_sumbool_right_right_pred : forall left_pred right_pred proof, mem_sort s right_pred -> mem_sort s (SumBoolRight left_pred right_pred proof)
  | mem_sumbool_right_proof : forall left_pred right_pred proof, mem_sort s proof -> mem_sort s (SumBoolRight left_pred right_pred proof)
  | mem_bool_ind_choice : forall choice on_true on_false proof, mem_sort s choice -> mem_sort s (BoolInd choice on_true on_false proof)
  | mem_bool_ind_on_true : forall choice on_true on_false proof, mem_sort s on_true -> mem_sort s (BoolInd choice on_true on_false proof)
  | mem_bool_ind_on_false : forall choice on_true on_false proof, mem_sort s on_false -> mem_sort s (BoolInd choice on_true on_false proof)
  | mem_bool_ind_proof : forall choice on_true on_false proof, mem_sort s proof -> mem_sort s (BoolInd choice on_true on_false proof)
  | mem_bool_rec_choice : forall choice on_true on_false proof, mem_sort s choice -> mem_sort s (BoolRec choice on_true on_false proof)
  | mem_bool_rec_on_true : forall choice on_true on_false proof, mem_sort s on_true -> mem_sort s (BoolRec choice on_true on_false proof)
  | mem_bool_rec_on_false : forall choice on_true on_false proof, mem_sort s on_false -> mem_sort s (BoolRec choice on_true on_false proof)
  | mem_bool_rec_proof : forall choice on_true on_false proof, mem_sort s proof -> mem_sort s (BoolRec choice on_true on_false proof)
  | mem_sumbool_ind_left_pred : forall left_pred right_pred choice on_true on_false bool, mem_sort s left_pred -> mem_sort s (SumBoolInd left_pred right_pred choice on_true on_false bool)
  | mem_sumbool_ind_right_pred : forall left_pred right_pred choice on_true on_false bool, mem_sort s right_pred -> mem_sort s (SumBoolInd left_pred right_pred choice on_true on_false bool)
  | mem_sumbool_ind_choice : forall left_pred right_pred choice on_true on_false bool, mem_sort s choice -> mem_sort s (SumBoolInd left_pred right_pred choice on_true on_false bool)
  | mem_sumbool_ind_on_true : forall left_pred right_pred choice on_true on_false bool, mem_sort s on_true -> mem_sort s (SumBoolInd left_pred right_pred choice on_true on_false bool)
  | mem_sumbool_ind_on_false : forall left_pred right_pred choice on_true on_false bool, mem_sort s on_false -> mem_sort s (SumBoolInd left_pred right_pred choice on_true on_false bool)
  | mem_sumbool_ind_bool : forall left_pred right_pred choice on_true on_false bool, mem_sort s bool -> mem_sort s (SumBoolInd left_pred right_pred choice on_true on_false bool)
  | mem_sumbool_rec_left_pred : forall left_pred right_pred choice on_true on_false bool, mem_sort s left_pred -> mem_sort s (SumBoolRec left_pred right_pred choice on_true on_false bool)
  | mem_sumbool_rec_right_pred : forall left_pred right_pred choice on_true on_false bool, mem_sort s right_pred -> mem_sort s (SumBoolRec left_pred right_pred choice on_true on_false bool)
  | mem_sumbool_rec_choice : forall left_pred right_pred choice on_true on_false bool, mem_sort s choice -> mem_sort s (SumBoolRec left_pred right_pred choice on_true on_false bool)
  | mem_sumbool_rec_on_true : forall left_pred right_pred choice on_true on_false bool, mem_sort s on_true -> mem_sort s (SumBoolRec left_pred right_pred choice on_true on_false bool)
  | mem_sumbool_rec_on_false : forall left_pred right_pred choice on_true on_false bool, mem_sort s on_false -> mem_sort s (SumBoolRec left_pred right_pred choice on_true on_false bool)
  | mem_sumbool_rec_bool : forall left_pred right_pred choice on_true on_false bool, mem_sort s bool -> mem_sort s (SumBoolRec left_pred right_pred choice on_true on_false bool)
  (* Refinment types *)
  | mem_refine_type : forall type property, mem_sort s type -> mem_sort s (Refine type property)
  | mem_refine_property : forall type property, mem_sort s property -> mem_sort s (Refine type property)
  | mem_refine_constr_type : forall type property val proof, mem_sort s type -> mem_sort s (RefineConstr type property val proof)
  | mem_refine_constr_property : forall type property val proof, mem_sort s property -> mem_sort s (RefineConstr type property val proof)
  | mem_refine_constr_val : forall type property val proof, mem_sort s val -> mem_sort s (RefineConstr type property val proof)
  | mem_refine_constr_proof : forall type property val proof, mem_sort s proof -> mem_sort s (RefineConstr type property val proof)
  | mem_refine_proj_val_type : forall type property ref, mem_sort s type -> mem_sort s (RefineProjVal type property ref)
  | mem_refine_proj_val_property : forall type property ref, mem_sort s property -> mem_sort s (RefineProjVal type property ref)
  | mem_refine_proj_val_ref : forall type property ref, mem_sort s ref -> mem_sort s (RefineProjVal type property ref)
  | mem_refine_proj_proof_type : forall type property ref, mem_sort s type -> mem_sort s (RefineProjProof type property ref)
  | mem_refine_proj_proof_property : forall type property ref, mem_sort s property -> mem_sort s (RefineProjProof type property ref)
  | mem_refine_proj_proof_ref : forall type property ref, mem_sort s ref -> mem_sort s (RefineProjProof type property ref)
  (* Equality *)
  | mem_eq_prop_type : forall type l r, mem_sort s type -> mem_sort s (Eq type l r)
  | mem_eq_prop_l : forall type l r, mem_sort s l -> mem_sort s (Eq type l r)
  | mem_eq_prop_r : forall type l r, mem_sort s r -> mem_sort s (Eq type l r)
  | mem_eq_refl_type : forall type val, mem_sort s type -> mem_sort s (EqRefl type val)
  | mem_eq_refl_val : forall type val, mem_sort s val -> mem_sort s (EqRefl type val)
  | mem_eq_ind_type : forall type l r property impl proof, mem_sort s type -> mem_sort s (EqInd type l r property impl proof)
  | mem_eq_ind_l : forall type l r property impl proof, mem_sort s l -> mem_sort s (EqInd type l r property impl proof)
  | mem_eq_ind_r : forall type l r property impl proof, mem_sort s r -> mem_sort s (EqInd type l r property impl proof)
  | mem_eq_ind_property : forall type l r property impl proof,mem_sort s property ->  mem_sort s (EqInd type l r property impl proof)
  | mem_eq_ind_impl : forall type l r property impl proof, mem_sort s impl -> mem_sort s (EqInd type l r property impl proof)
  | mem_eq_ind_proof : forall type l r property impl proof, mem_sort s proof -> mem_sort s (EqInd type l r property impl proof)
  | mem_eq_rec_type : forall type l r property impl proof, mem_sort s type -> mem_sort s (EqRec type l r property impl proof)
  | mem_eq_rec_l : forall type l r property impl proof, mem_sort s l -> mem_sort s (EqRec type l r property impl proof)
  | mem_eq_rec_r : forall type l r property impl proof, mem_sort s r -> mem_sort s (EqRec type l r property impl proof)
  | mem_eq_rec_property : forall type l r property impl proof,mem_sort s property ->  mem_sort s (EqRec type l r property impl proof)
  | mem_eq_rec_impl : forall type l r property impl proof, mem_sort s impl -> mem_sort s (EqRec type l r property impl proof)
  | mem_eq_rec_proof : forall type l r property impl proof, mem_sort s proof -> mem_sort s (EqRec type l r property impl proof)
  (* Falsity *)
  | mem_false_ind_proof : forall proof property, mem_sort s proof -> mem_sort s (FalseInd proof property)
  | mem_false_ind_property : forall proof property, mem_sort s property -> mem_sort s (FalseInd proof property)
  | mem_false_rec_proof : forall proof property, mem_sort s proof -> mem_sort s (FalseRec proof property)
  | mem_false_rec_property : forall proof property, mem_sort s property -> mem_sort s (FalseRec proof property)
  (* Unit has nothing! *)
  (* well founded recursion *)
  | mem_WFrec_type : forall type rel choice f proof, mem_sort s type -> mem_sort s (WFrec type rel choice f proof)
  | mem_WFrec_rel : forall type rel choice f proof, mem_sort s rel -> mem_sort s (WFrec type rel choice f proof)
  | mem_WFrec_choice : forall type rel choice f proof, mem_sort s choice -> mem_sort s (WFrec type rel choice f proof)
  | mem_WFrec_f : forall type rel choice f proof, mem_sort s f -> mem_sort s (WFrec type rel choice f proof)
  | mem_WFrec_proof : forall type rel choice f proof, mem_sort s proof -> mem_sort s (WFrec type rel choice f proof)
  (* bool proposition choice *)
  | mem_bool_prop_choice_on_true : forall on_true on_false val, mem_sort s on_true -> mem_sort s (BoolPropChoice on_true on_false val)
  | mem_bool_prop_choice_on_false : forall on_true on_false val, mem_sort s on_false -> mem_sort s (BoolPropChoice on_true on_false val)
  | mem_bool_prop_choice_val : forall on_true on_false val, mem_sort s val -> mem_sort s (BoolPropChoice on_true on_false val)
  .

End Termes.

Implicit Type s : sort.
Implicit Types A B M N T t u v : term.

Hint Resolve db_srt db_ref db_abs db_app db_prod db_nat db_nat_o db_nat_succ db_nat_destruct db_nat_cases db_nat_succ 
  db_nat_rec db_nat_ind
  db_le db_le_n db_le_s db_le_cases db_le_ind db_bool db_sum_bool db_bool_true db_bool_false
  db_sumbool_left db_sumbool_right db_bool_ind db_bool_rec db_sumbool_ind db_sumbool_rec
  db_refine db_refine_constr db_refine_proj_val db_refine_proj_proof db_eq_prop db_eq_refl
  db_eq_ind db_eq_rec db_falsity db_false_ind db_false_rec db_unit db_nil db_acc_prop
  db_acc_intro db_acc_rec db_acc_ind db_WFrec db_bool_prop_choice
  : coc.
Hint Resolve Bsbt_abs Bsbt_prod Nbsbt_abs Nbsbt_app_l Nbsbt_app_r
  Nbsbt_prod Nbsbt_nat_destruct_choice Nbsbt_nat_destruct_on_zero Nbsbt_nat_destruct_on_succ
  Nbsbt_nat_destruct_num Nbsbt_nat_cases_choice Nbsbt_nat_cases_on_zero Nbsbt_nat_cases_on_succ
  Nbsbt_nat_cases_num Nbsbt_nat_succ Nbsbt_nat_rec_choice Nbsbt_nat_rec_on_zero Nbsbt_nat_rec_on_succ
  Nbsbt_nat_rec_num Nbsbt_nat_ind_choice Nbsbt_nat_ind_on_zero Nbsbt_nat_ind_on_succ
  Nbsbt_nat_ind_num Nsbt_acc_prop_type Nsbt_acc_prop_rel Nsbt_acc_prop_val Nsbt_acc_intro_type
  Nsbt_acc_intro_rel Nsbt_acc_intro_val Nsbt_acc_intro_proof Nsbt_acc_rec_type Nsbt_acc_rec_rel
  Nsbt_acc_rec_choice Nsbt_acc_rec_func Nsbt_acc_rec_proof Nsbt_acc_ind_type Nsbt_acc_ind_rel
  Nsbt_acc_ind_choice Nsbt_acc_ind_func Nsbt_acc_ind_proof Nsbt_le_prop_l Nsbt_le_prop_r
  Nsbt_le_n Nsbt_le_s_l Nsbt_le_s_r Nsbt_le_s_proof Nsbt_le_cases_choice Nsbt_le_cases_onLN
  Nsbt_le_cases_onLS Nsbt_le_cases_l Nsbt_le_cases_r Nsbt_le_cases_proof Nsbt_le_ind_choice
  Nsbt_le_ind_onLN Nsbt_le_ind_onLS Nsbt_le_ind_l Nsbt_le_ind_r Nsbt_le_ind_proof Nsbt_sumbool_l 
  Nsbt_sumbool_r Nsbt_sumbool_left_l_pred Nsbt_sumbool_left_r_pred Nsbt_sumbool_left_proof
  Nsbt_sumbool_right_l_pred Nsbt_sumbool_right_r_pred Nsbt_sumbool_right_proof Nsbt_bool_ind_choice
  Nsbt_bool_ind_on_true Nsbt_bool_ind_on_false Nsbt_bool_ind_val Nsbt_bool_rec_choice Nsbt_bool_rec_on_true
  Nsbt_bool_rec_on_false Nsbt_bool_rec_val Nsbt_sumbool_ind_l_pred Nsbt_sumbool_ind_r_pred
  Nsbt_sumbool_ind_choice Nsbt_sumbool_ind_on_left Nsbt_sumbool_ind_on_right Nsbt_sumbool_ind_val
  Nsbt_sumbool_rec_l_pred Nsbt_sumbool_rec_r_pred Nsbt_sumbool_rec_choice Nsbt_sumbool_rec_on_left
  Nsbt_sumbool_rec_on_right Nsbt_sumbool_rec_val Nsbt_refine_type Nsbt_refine_property
  Nsbt_refine_constr_pred Nsbt_refine_constr_val Nsbt_refine_constr_proof 
  Nsbt_eq_prop_type Nsbt_eq_prop_l Nsbt_eq_prop_r Nsbt_eq_refl_type
  Nsbt_eq_refl_val Nsbt_eq_ind_type Nsbt_eq_ind_l Nsbt_eq_ind_r Nsbt_eq_ind_property
  Nsbt_eq_ind_impl Nsbt_eq_ind_proof Nsbt_eq_rec_type Nsbt_eq_rec_l Nsbt_eq_rec_r Nsbt_eq_rec_property
  Nsbt_eq_rec_impl Nsbt_eq_rec_proof Nsbt_false_ind_proof Nsbt_false_ind_prop Nsbt_false_rec_proof
  Nsbt_false_rec_prop Nsbt_acc_rec_val Nsbt_acc_ind_val Nsbt_refine_constr_type Nsbt_wf_rec_type
  Nsbt_wf_rec_rel Nsbt_wf_rec_choice Nsbt_wf_rec_f Nsbt_wf_rec_proof Nsbt_bool_prop_choice_on_true
  Nsbt_bool_prop_choice_on_false Nsbt_bool_prop_choice_val Nsbt_refine_proj_val_type Nsbt_refine_proj_val_property
  Nsbt_refine_proj_val_ref Nsbt_refine_proj_proof_type Nsbt_refine_proj_proof_property Nsbt_refine_proj_proof_ref
  : coc.
Hint Resolve Sbtrm_nobind: coc.

(*
  Hints Unfold  mem_sort : coc.
*)
Hint Resolve mem_eq mem_prod_l mem_prod_r mem_abs_l mem_abs_r mem_app_l mem_app_r mem_nat_destruct_choice 
  mem_nat_destruct_on_zero  mem_nat_destruct_on_succ mem_nat_destruct_num mem_nat_cases_choice
  mem_nat_cases_on_zero mem_nat_cases_on_succ mem_nat_cases_num mem_nat_succ mem_nat_rec_choice 
  mem_nat_rec_on_zero  mem_nat_rec_on_succ mem_nat_rec_num mem_nat_ind_choice mem_nat_ind_on_zero 
  mem_nat_ind_on_succ mem_nat_ind_num mem_acc_prop_type mem_acc_prop_rel mem_acc_prop_val mem_acc_intro_type
  mem_acc_intro_rel mem_acc_intro_val mem_acc_intro_proof mem_acc_rec_type mem_acc_rec_rel mem_acc_rec_choice
  mem_acc_rec_f mem_acc_rec_proof mem_acc_ind_type mem_acc_ind_rel mem_acc_ind_choice mem_acc_ind_f 
  mem_acc_ind_proof mem_le_prop_l mem_le_prop_r mem_le_n_n mem_le_s_l mem_le_s_r mem_le_s_proof mem_le_cases_choice
  mem_le_cases_on_le_n mem_le_cases_on_le_s mem_le_cases_l mem_le_cases_r mem_le_cases_proof mem_le_ind_choice
  mem_le_ind_on_le_n mem_le_ind_on_le_s mem_le_ind_l mem_le_ind_r mem_le_ind_proof mem_sumbool_type_left_pred
  mem_sumbool_type_right_pred mem_sumbool_left_left_pred mem_sumbool_left_right_pred mem_sumbool_left_proof
  mem_sumbool_right_left_pred mem_sumbool_right_right_pred mem_sumbool_right_proof mem_bool_ind_choice 
  mem_bool_ind_on_true mem_bool_ind_on_false mem_bool_ind_proof mem_bool_rec_choice mem_bool_rec_on_true
  mem_bool_rec_on_false mem_bool_rec_proof mem_sumbool_ind_choice mem_sumbool_ind_on_true mem_sumbool_ind_on_false
  mem_sumbool_ind_bool mem_sumbool_rec_choice mem_sumbool_rec_on_true mem_sumbool_rec_on_false mem_sumbool_rec_bool
  mem_refine_type mem_refine_property mem_refine_constr_type mem_refine_constr_property mem_refine_constr_val
  mem_refine_constr_proof mem_eq_prop_type mem_eq_prop_l mem_eq_prop_r
  mem_eq_refl_type mem_eq_refl_val mem_eq_ind_type mem_eq_ind_l mem_eq_ind_r mem_eq_ind_property mem_eq_ind_impl
  mem_eq_ind_proof mem_eq_rec_type mem_eq_rec_l mem_eq_rec_r mem_eq_rec_property mem_eq_rec_impl mem_eq_rec_proof
  mem_false_ind_proof mem_false_ind_property mem_false_rec_proof mem_false_rec_property mem_acc_rec_val mem_acc_ind_val
  mem_sumbool_ind_left_pred mem_sumbool_ind_right_pred mem_sumbool_rec_left_pred mem_sumbool_rec_right_pred
  mem_WFrec_type mem_WFrec_rel mem_WFrec_choice mem_WFrec_f mem_WFrec_proof mem_bool_prop_choice_on_true
  mem_bool_prop_choice_on_false mem_bool_prop_choice_val mem_refine_proj_val_type mem_refine_proj_val_property
  mem_refine_proj_val_ref mem_refine_proj_proof_type mem_refine_proj_proof_property mem_refine_proj_proof_ref
  : coc.


Section Beta_Reduction.

  (* The one-step reduction *)
  Inductive red1 : term -> term -> Prop :=
  | beta : forall M N T, red1 (App (Abs T M) N) (subst N M)
  | abs_red_l :
    forall M M', red1 M M' -> forall N, red1 (Abs M N) (Abs M' N)
  | abs_red_r :
    forall M M', red1 M M' -> forall N, red1 (Abs N M) (Abs N M')
  | app_red_l :
    forall M1 N1, red1 M1 N1 -> forall M2, red1 (App M1 M2) (App N1 M2)
  | app_red_r :
    forall M2 N2, red1 M2 N2 -> forall M1, red1 (App M1 M2) (App M1 N2)
  | prod_red_l :
    forall M1 N1, red1 M1 N1 -> forall M2, red1 (Prod M1 M2) (Prod N1 M2)
  | prod_red_r :
    forall M2 N2, red1 M2 N2 -> forall M1, red1 (Prod M1 M2) (Prod M1 N2)
  (* Natrual numebers eliminators *)
  | nat_destruct_choice :
    forall choice on_zero on_succ num choice', red1 choice choice' -> red1 (NatDestruct choice on_zero on_succ num) (NatDestruct choice' on_zero on_succ num)
  | nat_destruct_on_zero :
    forall choice on_zero on_succ num on_zero', red1 on_zero on_zero' -> red1 (NatDestruct choice on_zero on_succ num) (NatDestruct choice on_zero' on_succ num)
  | nat_destruct_on_succ :
    forall choice on_zero on_succ num on_succ', red1 on_succ on_succ' -> red1 (NatDestruct choice on_zero on_succ num) (NatDestruct choice on_zero on_succ' num)
  | nat_destruct_num :
    forall choice on_zero on_succ num num', red1 num num' -> red1 (NatDestruct choice on_zero on_succ num) (NatDestruct choice on_zero on_succ num')
  | nat_destruct_choose_zero :
    forall choice on_zero on_succ, red1 (NatDestruct choice on_zero on_succ NatO) on_zero
  | nat_destruct_choose_succ :
    forall choice on_zero on_succ num, red1 (NatDestruct choice on_zero on_succ (NatSucc num)) (App on_succ num)
  | nat_cases_choice :
    forall choice on_zero on_succ num choice', red1 choice choice' -> red1 (NatCases choice on_zero on_succ num) (NatCases choice' on_zero on_succ num)
  | nat_cases_on_zero :
    forall choice on_zero on_succ num on_zero', red1 on_zero on_zero' -> red1 (NatCases choice on_zero on_succ num) (NatCases choice on_zero' on_succ num)
  | nat_cases_on_succ :
    forall choice on_zero on_succ num on_succ', red1 on_succ on_succ' -> red1 (NatCases choice on_zero on_succ num) (NatCases choice on_zero on_succ' num)
  | nat_cases_num :
    forall choice on_zero on_succ num num', red1 num num' -> red1 (NatCases choice on_zero on_succ num) (NatCases choice on_zero on_succ num')
  | nat_cases_choose_zero :
    forall choice on_zero on_succ, red1 (NatCases choice on_zero on_succ NatO) on_zero
  | nat_cases_choose_succ :
    forall choice on_zero on_succ num, red1 (NatCases choice on_zero on_succ (NatSucc num)) (App on_succ num)
  (* nat succ *)
  | nat_succ_red :
    forall x x', red1 x x' -> red1 (NatSucc x) (NatSucc x')
  (* Natural numbers recursors *)
  | nat_rec_choice :
    forall choice on_zero on_succ num choice', red1 choice choice' -> red1 (NatRec choice on_zero on_succ num) (NatRec choice' on_zero on_succ num)
  | nat_rec_on_zero :
    forall choice on_zero on_succ num on_zero', red1 on_zero on_zero' -> red1 (NatRec choice on_zero on_succ num) (NatRec choice on_zero' on_succ num)
  | nat_rec_on_succ :
    forall choice on_zero on_succ num on_succ', red1 on_succ on_succ' -> red1 (NatRec choice on_zero on_succ num) (NatRec choice on_zero on_succ' num)
  | nat_rec_num :
    forall choice on_zero on_succ num num', red1 num num' -> red1 (NatRec choice on_zero on_succ num) (NatRec choice on_zero on_succ num')
  | nat_rec_choose_zero :
    forall choice on_zero on_succ, red1 (NatRec choice on_zero on_succ NatO) on_zero
  | nat_rec_choose_succ :
    forall choice on_zero on_succ num, red1 (NatRec choice on_zero on_succ (NatSucc num)) (App (App on_succ num) (NatRec choice on_zero on_succ num))
  | nat_ind_choice :
    forall choice on_zero on_succ num choice', red1 choice choice' -> red1 (NatInd choice on_zero on_succ num) (NatInd choice' on_zero on_succ num)
  | nat_ind_on_zero :
    forall choice on_zero on_succ num on_zero', red1 on_zero on_zero' -> red1 (NatInd choice on_zero on_succ num) (NatInd choice on_zero' on_succ num)
  | nat_ind_on_succ :
    forall choice on_zero on_succ num on_succ', red1 on_succ on_succ' -> red1 (NatInd choice on_zero on_succ num) (NatInd choice on_zero on_succ' num)
  | nat_ind_num :
    forall choice on_zero on_succ num num', red1 num num' -> red1 (NatInd choice on_zero on_succ num) (NatInd choice on_zero on_succ num')
  | nat_ind_choose_zero :
    forall choice on_zero on_succ, red1 (NatInd choice on_zero on_succ NatO) on_zero
  | nat_ind_choose_succ :
    forall choice on_zero on_succ num, red1 (NatInd choice on_zero on_succ (NatSucc num)) (App (App on_succ num) (NatInd choice on_zero on_succ num))
  (* Well founded induction *)
  | acc_prop_type :
    forall type type' rel val, red1 type type' -> red1 (AccProp type rel val) (AccProp type' rel val)
  | acc_prop_rel :
    forall type rel rel' val, red1 rel rel' -> red1 (AccProp type rel val) (AccProp type rel' val)
  | acc_prop_val :
    forall type rel val val', red1 val val' -> red1 (AccProp type rel val) (AccProp type rel val')
  | acc_intro_type :
    forall type type' rel val proof, red1 type type' -> red1 (AccIntro type rel val proof) (AccIntro type' rel val proof)
  | acc_intro_rel :
    forall type rel rel' val proof, red1 rel rel' -> red1 (AccIntro type rel val proof) (AccIntro type rel' val proof)
  | acc_intro_val :
    forall type rel val val' proof, red1 val val' -> red1 (AccIntro type rel val proof) (AccIntro type rel val' proof)
  | acc_intro_proof :
    forall type rel val proof proof', red1 proof proof' -> red1 (AccIntro type rel val proof) (AccIntro type rel val proof')
  | acc_rec_type :
    forall type type' rel choice f val proof, red1 type type' -> red1 (AccRec type rel choice f val proof) (AccRec type' rel choice f val proof)
  | acc_rec_rel :
    forall type rel rel' choice f val proof, red1 rel rel' -> red1 (AccRec type rel choice f val proof) (AccRec type rel' choice f val proof)
  | acc_rec_choice :
    forall type rel choice choice' f val proof, red1 choice choice' -> red1 (AccRec type rel choice f val proof) (AccRec type rel choice' f val proof)
  | acc_rec_f :
    forall type rel choice f f' val proof, red1 f f' -> red1 (AccRec type rel choice f val proof) (AccRec type rel choice f' val proof)
  | acc_rec_val :
    forall type rel choice f val val' proof, red1 val val' -> red1 (AccRec type rel choice f val proof) (AccRec type rel choice f val' proof) 
  | acc_rec_proof :
    forall type rel choice f val proof proof', red1 proof proof' -> red1 (AccRec type rel choice f val proof) (AccRec type rel choice f val proof')
  | acc_rec_exec :
    forall type_a type_b rel_a rel_b val_a val_b choice f proof,
    red1 
    (AccRec type_a rel_a choice f val_a (AccIntro type_b rel_b val_b proof)) 
    (
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
    )
  | acc_ind_type :
    forall type type' rel choice f val proof, red1 type type' -> red1 (AccInd type rel choice f val proof) (AccInd type' rel choice f val proof)
  | acc_ind_rel :
    forall type rel rel' choice f val proof, red1 rel rel' -> red1 (AccInd type rel choice f val proof) (AccInd type rel' choice f val proof)
  | acc_ind_choice :
    forall type rel choice choice' f val proof, red1 choice choice' -> red1 (AccInd type rel choice f val proof) (AccInd type rel choice' f val proof)
  | acc_ind_f :
    forall type rel choice f f' val proof, red1 f f' -> red1 (AccInd type rel choice f val proof) (AccInd type rel choice f' val proof)
  | acc_ind_val :
    forall type rel choice f val val' proof, red1 val val' -> red1 (AccInd type rel choice f val proof) (AccInd type rel choice f val' proof) 
  | acc_ind_proof :
    forall type rel choice f val proof proof', red1 proof proof' -> red1 (AccInd type rel choice f val proof) (AccInd type rel choice f val proof')
  | acc_ind_exec :
    forall type_a type_b rel_a rel_b val_a val_b choice f proof,
    red1 
    (AccInd type_a rel_a choice f val_a (AccIntro type_b rel_b val_b proof)) 
    (
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
    )
  (* Order for naturals *)
  | le_prop_l :
    forall l l' r, red1 l l' -> red1 (Le l r) (Le l' r) 
  | le_prop_r :
    forall l r r', red1 r r' -> red1 (Le l r) (Le l r') 
  | le_n :
    forall n n' : term, red1 n n' -> red1 (LeN n) (LeN n')
  | le_s_l :
    forall l l' r proof, red1 l l' -> red1 (LeS l r proof) (LeS l' r proof)
  | le_s_r :
    forall l r r' proof, red1 r r' -> red1 (LeS l r proof) (LeS l r' proof)
  | le_s_proof :
    forall l r proof proof', red1 proof proof' -> red1 (LeS l r proof) (LeS l r proof')
  | le_cases_choice :
    forall choice choice' on_le_n on_le_s l r proof, red1 choice choice' -> red1 (LeCases choice on_le_n on_le_s l r proof) (LeCases choice' on_le_n on_le_s l r proof)
  | le_cases_on_le_n :
    forall choice on_le_n on_le_n' on_le_s l r proof, red1 on_le_n on_le_n' -> red1 (LeCases choice on_le_n on_le_s l r proof) (LeCases choice on_le_n' on_le_s l r proof)
  | le_cases_on_le_s :
    forall choice on_le_n on_le_s on_le_s' l r proof, red1 on_le_s on_le_s' -> red1 (LeCases choice on_le_n on_le_s l r proof) (LeCases choice on_le_n on_le_s' l r proof)
  | le_cases_l :
    forall choice on_le_n on_le_s l l' r proof, red1 l l' -> red1 (LeCases choice on_le_n on_le_s l r proof) (LeCases choice on_le_n on_le_s l' r proof)
  | le_cases_r :
    forall choice on_le_n on_le_s l r r' proof, red1 r r' -> red1 (LeCases choice on_le_n on_le_s l r proof) (LeCases choice on_le_n on_le_s l r' proof)
  | le_cases_proof :
    forall choice on_le_n on_le_s l r proof proof', red1 proof proof' -> red1 (LeCases choice on_le_n on_le_s l r proof) (LeCases choice on_le_n on_le_s l r proof')
  | le_cases_exec_1 :
    forall choice on_le_n on_le_s l r n : term,
    red1 (LeCases choice on_le_n on_le_s l r (LeN n)) on_le_n
  | le_cases_exec_2 :
    forall choice on_le_n on_le_s l_a r_a l_b r_b proof,
    red1 (LeCases choice on_le_n on_le_s l_a r_a (LeS l_b r_b proof)) (App (App on_le_s r_b) proof) 
  | le_ind_choice :
    forall choice choice' on_le_n on_le_s l r proof, red1 choice choice' -> red1 (LeInd choice on_le_n on_le_s l r proof) (LeInd choice' on_le_n on_le_s l r proof)
  | le_ind_on_le_n :
    forall choice on_le_n on_le_n' on_le_s l r proof, red1 on_le_n on_le_n' -> red1 (LeInd choice on_le_n on_le_s l r proof) (LeInd choice on_le_n' on_le_s l r proof)
  | le_ind_on_le_s :
    forall choice on_le_n on_le_s on_le_s' l r proof, red1 on_le_s on_le_s' -> red1 (LeInd choice on_le_n on_le_s l r proof) (LeInd choice on_le_n on_le_s' l r proof)
  | le_ind_l :
    forall choice on_le_n on_le_s l l' r proof, red1 l l' -> red1 (LeInd choice on_le_n on_le_s l r proof) (LeInd choice on_le_n on_le_s l' r proof)
  | le_ind_r :
    forall choice on_le_n on_le_s l r r' proof, red1 r r' -> red1 (LeInd choice on_le_n on_le_s l r proof) (LeInd choice on_le_n on_le_s l r' proof)
  | le_ind_proof :
    forall choice on_le_n on_le_s l r proof proof', red1 proof proof' -> red1 (LeInd choice on_le_n on_le_s l r proof) (LeInd choice on_le_n on_le_s l r proof')
  | le_ind_exec_1 :
    forall choice on_le_n on_le_s l r n : term,
    red1 (LeInd choice on_le_n on_le_s l r (LeN n)) on_le_n
  | le_ind_exec_2 :
    forall choice on_le_n on_le_s l_a r_a l_b r_b proof,
    red1 (LeInd choice on_le_n on_le_s l_a r_a (LeS l_b r_b proof)) (App (App (App on_le_s r_b) proof) (LeInd choice on_le_n on_le_s l_b r_b proof))
  (* Bool and SumBool *)
  | sumbool_type_left :
    forall l l' r, red1 l l' -> red1 (SumBool l r) (SumBool l' r)
  | sumbool_type_right :
    forall l r r', red1 r r' -> red1 (SumBool l r) (SumBool l r')
  | sumbool_left_left_pred :
    forall left_pred left_pred' right_pred proof, red1 left_pred left_pred' -> red1 (SumBoolLeft left_pred right_pred proof) (SumBoolLeft left_pred' right_pred proof)
  | sumbool_left_right_pred :
    forall left_pred right_pred right_pred' proof, red1 right_pred right_pred' -> red1 (SumBoolLeft left_pred right_pred proof) (SumBoolLeft left_pred right_pred' proof)
  | sumbool_left_proof :
    forall left_pred right_pred proof proof', red1 proof proof'  -> red1 (SumBoolLeft left_pred right_pred proof) (SumBoolLeft left_pred right_pred proof')
  | sumbool_right_left_pred :
    forall left_pred left_pred' right_pred proof, red1 left_pred left_pred' -> red1 (SumBoolRight left_pred right_pred proof) (SumBoolRight left_pred' right_pred proof)
  | sumbool_right_right_pred :
    forall left_pred right_pred right_pred' proof, red1 right_pred right_pred' -> red1 (SumBoolRight left_pred right_pred proof) (SumBoolRight left_pred right_pred' proof)
  | sumbool_right_proof :
    forall left_pred right_pred proof proof', red1 proof proof' -> red1 (SumBoolRight left_pred right_pred proof) (SumBoolRight left_pred right_pred proof')
  | bool_ind_choice : 
    forall choice choice' on_true on_false bool, red1 choice choice' -> red1 (BoolInd choice on_true on_false bool) (BoolInd choice' on_true on_false bool)
  | bool_ind_on_true : 
    forall choice on_true on_true' on_false bool, red1 on_true on_true' -> red1 (BoolInd choice on_true on_false bool) (BoolInd choice on_true' on_false bool)
  | bool_ind_on_false : 
    forall choice on_true on_false on_false' bool, red1 on_false on_false' -> red1 (BoolInd choice on_true on_false bool) (BoolInd choice on_true on_false' bool)
  | bool_ind_bool : 
    forall choice on_true on_false bool bool', red1 bool bool' -> red1 (BoolInd choice on_true on_false bool) (BoolInd choice on_true on_false bool')
  | bool_ind_true :
    forall choice on_true on_false, red1 (BoolInd choice on_true on_false BoolTrue) on_true
  | bool_ind_false :
    forall choice on_true on_false, red1 (BoolInd choice on_true on_false BoolFalse) on_false
  | bool_rec_choice : 
    forall choice choice' on_true on_false bool, red1 choice choice' -> red1 (BoolRec choice on_true on_false bool) (BoolRec choice' on_true on_false bool)
  | bool_rec_on_true : 
    forall choice on_true on_true' on_false bool, red1 on_true on_true' -> red1 (BoolRec choice on_true on_false bool) (BoolRec choice on_true' on_false bool)
  | bool_rec_on_false : 
    forall choice on_true on_false on_false' bool, red1 on_false on_false' -> red1 (BoolRec choice on_true on_false bool) (BoolRec choice on_true on_false' bool)
  | bool_rec_bool : 
    forall choice on_true on_false bool bool', red1 bool bool' -> red1 (BoolRec choice on_true on_false bool) (BoolRec choice on_true on_false bool')
  | bool_rec_true :
    forall choice on_true on_false, red1 (BoolRec choice on_true on_false BoolTrue) on_true
  | bool_rec_false :
    forall choice on_true on_false, red1 (BoolRec choice on_true on_false BoolFalse) on_false
  | sumbool_ind_left_pred :
    forall left_pred left_pred' right_pred choice on_left on_right val, red1 left_pred left_pred' -> red1 (SumBoolInd left_pred right_pred choice on_left on_right val) (SumBoolInd left_pred' right_pred choice on_left on_right val)
  | sumbool_ind_right_pred :
    forall left_pred right_pred right_pred' choice on_left on_right val, red1 right_pred right_pred' -> red1 (SumBoolInd left_pred right_pred choice on_left on_right val) (SumBoolInd left_pred right_pred' choice on_left on_right val)
  | sumbool_ind_choice :
    forall left_pred right_pred choice choice' on_left on_right val, red1 choice choice' -> red1 (SumBoolInd left_pred right_pred choice on_left on_right val) (SumBoolInd left_pred right_pred choice' on_left on_right val)
  | sumbool_ind_on_left :
    forall left_pred right_pred choice on_left on_left' on_right val, red1 on_left on_left' -> red1 (SumBoolInd left_pred right_pred choice on_left on_right val) (SumBoolInd left_pred right_pred choice on_left' on_right val)
  | sumbool_ind_on_right :
    forall left_pred right_pred choice on_left on_right on_right' val, red1 on_right on_right' -> red1 (SumBoolInd left_pred right_pred choice on_left on_right val) (SumBoolInd left_pred right_pred choice on_left on_right' val)
  | sumbool_ind_val :
    forall left_pred right_pred choice on_left on_right val val', red1 val val' -> red1 (SumBoolInd left_pred right_pred choice on_left on_right val) (SumBoolInd left_pred right_pred choice on_left on_right val')
  | sumbool_ind_left :
    forall left_pred_a right_pred_a choice on_left on_right left_pred_b right_pred_b proof, red1 (SumBoolInd left_pred_a right_pred_a choice on_left on_right (SumBoolLeft left_pred_b right_pred_b proof)) (App on_left proof)
  | sumbool_ind_right :
    forall left_pred_a right_pred_a choice on_left on_right left_pred_b right_pred_b proof, red1 (SumBoolInd left_pred_a right_pred_a choice on_left on_right (SumBoolRight left_pred_b right_pred_b proof)) (App on_right proof)
  | sumbool_rec_left_pred :
    forall left_pred left_pred' right_pred choice on_left on_right val, red1 left_pred left_pred' -> red1 (SumBoolRec left_pred right_pred choice on_left on_right val) (SumBoolRec left_pred' right_pred choice on_left on_right val)
  | sumbool_rec_right_pred :
    forall left_pred right_pred right_pred' choice on_left on_right val, red1 right_pred right_pred' -> red1 (SumBoolRec left_pred right_pred choice on_left on_right val) (SumBoolRec left_pred right_pred' choice on_left on_right val)
  | sumbool_rec_choice :
    forall left_pred right_pred choice choice' on_left on_right val, red1 choice choice' -> red1 (SumBoolRec left_pred right_pred choice on_left on_right val) (SumBoolRec left_pred right_pred choice' on_left on_right val)
  | sumbool_rec_on_left :
    forall left_pred right_pred choice on_left on_left' on_right val, red1 on_left on_left' -> red1 (SumBoolRec left_pred right_pred choice on_left on_right val) (SumBoolRec left_pred right_pred choice on_left' on_right val)
  | sumbool_rec_on_right :
    forall left_pred right_pred choice on_left on_right on_right' val, red1 on_right on_right' -> red1 (SumBoolRec left_pred right_pred choice on_left on_right val) (SumBoolRec left_pred right_pred choice on_left on_right' val)
  | sumbool_rec_val :
    forall left_pred right_pred choice on_left on_right val val', red1 val val' -> red1 (SumBoolRec left_pred right_pred choice on_left on_right val) (SumBoolRec left_pred right_pred choice on_left on_right val')
  | sumbool_rec_left :
    forall left_pred_a right_pred_a choice on_left on_right left_pred_b right_pred_b proof, red1 (SumBoolRec left_pred_a right_pred_a choice on_left on_right (SumBoolLeft left_pred_b right_pred_b proof)) (App on_left proof)
  | sumbool_rec_right :
    forall left_pred_a right_pred_a choice on_left on_right left_pred_b right_pred_b proof, red1 (SumBoolRec left_pred_a right_pred_a choice on_left on_right (SumBoolRight left_pred_b right_pred_b proof)) (App on_right proof)
  (* Refinment types *)
  | refine_type :
    forall type type' property, red1 type type' -> red1 (Refine type property) (Refine type' property)
  | refine_property :
    forall type property property', red1 property property' -> red1 (Refine type property) (Refine type property')
  | refine_constr_type :
    forall type type' property val proof, red1 type type' -> red1 (RefineConstr type property val proof) (RefineConstr type' property val proof)
  | refine_constr_property :
    forall type property property' val proof, red1 property property' -> red1 (RefineConstr type property val proof) (RefineConstr type property' val proof)
  | refine_constr_val :
    forall type property val val' proof, red1 val val' -> red1 (RefineConstr type property val proof) (RefineConstr type property val' proof)
  | refine_constr_proof :
    forall type property val proof proof', red1 proof proof' -> red1 (RefineConstr type property val proof) (RefineConstr type property val proof')
  | refine_proj_val_type :
    forall type type' property ref, red1 type type' -> red1 (RefineProjVal type property ref) (RefineProjVal type' property ref)
  | refine_proj_val_property :
    forall type property property' ref, red1 property property' -> red1 (RefineProjVal type property ref) (RefineProjVal type property' ref)
  | refine_proj_val_ref :
    forall type property ref ref', red1 ref ref' -> red1 (RefineProjVal type property ref) (RefineProjVal type property ref')
  | refine_proj_proof_type :
    forall type type' property ref, red1 type type' -> red1 (RefineProjProof type property ref) (RefineProjProof type' property ref)
  | refine_proj_proof_property :
    forall type property property' ref, red1 property property' -> red1 (RefineProjProof type property ref) (RefineProjProof type property' ref)
  | refine_proj_proof_ref :
    forall type property ref ref', red1 ref ref' -> red1 (RefineProjProof type property ref) (RefineProjProof type property ref')
  | refine_proj_val_exec :
    forall type_a property_a type_b property_b val proof, red1 (RefineProjVal type_a property_a (RefineConstr type_b property_b val proof)) val
  | refine_proj_proof_exec :
    forall type_a property_a type_b property_b val proof, red1 (RefineProjProof type_a property_a (RefineConstr type_b property_b val proof)) proof
  (* Equality *)
  | eq_prop_type :
    forall type type' l r, red1 type type' -> red1 (Eq type l r) (Eq type' l r)
  | eq_prop_l :
    forall type l l' r, red1 l l' -> red1 (Eq type l r) (Eq type l' r)
  | eq_prop_r :
    forall type l r r', red1 r r' -> red1 (Eq type l r) (Eq type l r')
  | eq_refl_type :
    forall type type' val, red1 type type' -> red1 (EqRefl type val) (EqRefl type' val)
  | eq_refl_val :
    forall type val val', red1 val val' -> red1 (EqRefl type val) (EqRefl type val')
  | eq_ind_type :
    forall type type' l r property impl proof, red1 type type' -> red1 (EqInd type l r property impl proof) (EqInd type' l r property impl proof)
  | eq_ind_l :
    forall type l l' r property impl proof, red1 l l' -> red1 (EqInd type l r property impl proof) (EqInd type l' r property impl proof)
  | eq_ind_r :
    forall type l r r' property impl proof, red1 r r' -> red1 (EqInd type l r property impl proof) (EqInd type l r' property impl proof)
  | eq_ind_property :
    forall type l r property property' impl proof, red1 property property' -> red1 (EqInd type l r property impl proof) (EqInd type l r property' impl proof)
  | eq_ind_impl :
    forall type l r property impl impl' proof, red1 impl impl' -> red1 (EqInd type l r property impl proof) (EqInd type l r property impl' proof)
  | eq_ind_proof :
    forall type l r property impl proof proof', red1 proof proof' -> red1 (EqInd type l r property impl proof) (EqInd type l r property impl proof')
  | eq_ind_exec :
    forall type_a l r property impl type_b val, red1 (EqInd type_a l r property impl (EqRefl type_b val)) impl
  | eq_rec_type :
    forall type type' l r property impl proof, red1 type type' -> red1 (EqRec type l r property impl proof) (EqRec type' l r property impl proof)
  | eq_rec_l :
    forall type l l' r property impl proof, red1 l l' -> red1 (EqRec type l r property impl proof) (EqRec type l' r property impl proof)
  | eq_rec_r :
    forall type l r r' property impl proof, red1 r r' -> red1 (EqRec type l r property impl proof) (EqRec type l r' property impl proof)
  | eq_rec_property :
    forall type l r property property' impl proof, red1 property property' -> red1 (EqRec type l r property impl proof) (EqRec type l r property' impl proof)
  | eq_rec_impl :
    forall type l r property impl impl' proof, red1 impl impl' -> red1 (EqRec type l r property impl proof) (EqRec type l r property impl' proof)
  | eq_rec_proof :
    forall type l r property impl proof proof', red1 proof proof' -> red1 (EqRec type l r property impl proof) (EqRec type l r property impl proof')
  | eq_rec_exec :
    forall type_a l r property impl type_b val, red1 (EqRec type_a l r property impl (EqRefl type_b val)) impl
  (* Falsity *)
  | false_ind_proof :
    forall proof proof' property, red1 proof proof' -> red1 (FalseInd proof property) (FalseInd proof' property)
  | false_ind_property :
    forall proof property property', red1 property property' -> red1 (FalseInd proof property) (FalseInd proof property')
  | false_rec_proof :
    forall proof proof' property, red1 proof proof' -> red1 (FalseRec proof property) (FalseRec proof' property)
  | false_rec_property :
    forall proof property property', red1 property property' -> red1 (FalseRec proof property) (FalseRec proof property')
  (* well founded recursion *)
  | wf_rec_type : 
    forall type type' rel choice f proof, red1 type type' -> red1 (WFrec type rel choice f proof) (WFrec type' rel choice f proof)
  | wf_rec_rel : 
    forall type rel rel' choice f proof, red1 rel rel' -> red1 (WFrec type rel choice f proof) (WFrec type rel' choice f proof)
  | wf_rec_choice : 
    forall type rel choice choice' f proof, red1 choice choice' -> red1 (WFrec type rel choice f proof) (WFrec type rel choice' f proof)
  | wf_rec_f : 
    forall type rel choice f f' proof, red1 f f' -> red1 (WFrec type rel choice f proof) (WFrec type rel choice f' proof)
  | wf_rec_proof : 
    forall type rel choice f proof proof', red1 proof proof' -> red1 (WFrec type rel choice f proof) (WFrec type rel choice f proof')
  | wf_rec_expand :
    forall type rel choice f proof,
    red1 (WFrec type rel choice f proof) 
    (
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
    )
  (* bool prop choice *)
  | bool_prop_choice_on_true : forall on_true on_true' on_false val, red1 on_true on_true' -> red1 (BoolPropChoice on_true on_false val) (BoolPropChoice on_true' on_false val)
  | bool_prop_choice_on_false : forall on_true on_false on_false' val, red1 on_false on_false' -> red1 (BoolPropChoice on_true on_false val) (BoolPropChoice on_true on_false' val)
  | bool_prop_choice_val : forall on_true on_false val val', red1 val val' -> red1 (BoolPropChoice on_true on_false val) (BoolPropChoice on_true on_false val')
  | bool_prop_true : forall on_true on_false, red1 (BoolPropChoice on_true on_false BoolTrue) on_true
  | bool_prop_false : forall on_true on_false, red1 (BoolPropChoice on_true on_false BoolFalse) on_false
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
    forall M M', par_red1 M M' ->
    forall N N', par_red1 N N' -> 
    forall T, par_red1 (App (Abs T M) N) (subst N' M')
  | sort_par_red : forall s, par_red1 (Srt s) (Srt s)
  | ref_par_red : forall n, par_red1 (Ref n) (Ref n)
  | abs_par_red :
    forall M M', par_red1 M M' ->
    forall T T', par_red1 T T' -> par_red1 (Abs T M) (Abs T' M')
  | app_par_red :
    forall M M', par_red1 M M' ->
    forall N N', par_red1 N N' -> 
    par_red1 (App M N) (App M' N')
  | prod_par_red :
    forall M M', par_red1 M M' ->
    forall N N', par_red1 N N' -> 
    par_red1 (Prod M N) (Prod M' N')
  (* Natural number eliminators *)
  | nat_destruct_par_red :
    forall choice choice', par_red1 choice choice' ->
    forall on_zero on_zero', par_red1 on_zero on_zero' ->
    forall on_succ on_succ', par_red1 on_succ on_succ' ->
    forall num num', par_red1 num num' ->
    par_red1 (NatDestruct choice on_zero on_succ num) (NatDestruct choice' on_zero' on_succ' num')
  | nat_destruct_on_zero_par_red :
    forall on_zero on_zero', par_red1 on_zero on_zero' ->
    forall choice on_succ, par_red1 (NatDestruct choice on_zero on_succ NatO) on_zero'
  | nat_destruct_on_succ_par_red :
    forall on_succ on_succ', par_red1 on_succ on_succ' ->
    forall num num', par_red1 num num' ->
    forall choice on_zero, par_red1 (NatDestruct choice on_zero on_succ (NatSucc num)) (App on_succ' num') 
  | nat_cases_par_red :
    forall choice choice', par_red1 choice choice' ->
    forall on_zero on_zero', par_red1 on_zero on_zero' ->
    forall on_succ on_succ', par_red1 on_succ on_succ' ->
    forall num num', par_red1 num num' ->
    par_red1 (NatCases choice on_zero on_succ num) (NatCases choice' on_zero' on_succ' num')
  | nat_cases_on_zero_par_red :
    forall on_zero on_zero', par_red1 on_zero on_zero' ->
    forall choice on_succ, par_red1 (NatCases choice on_zero on_succ NatO) on_zero'
  | nat_cases_on_succ_par_red :
    forall on_succ on_succ', par_red1 on_succ on_succ' ->
    forall num num', par_red1 num num' ->
    forall choice on_zero, par_red1 (NatCases choice on_zero on_succ (NatSucc num)) (App on_succ' num') 
  (* Natural numbers constructor *)
  | nat_succ_par_red :
    forall x x', par_red1 x x' ->
    par_red1 (NatSucc x) (NatSucc x')
  | nat_par_red : par_red1 Nat Nat
  | nat_o_par_red : par_red1 NatO NatO
  (* Natural numbers recursors *)
  | nat_rec_par_red :
    forall choice choice', par_red1 choice choice' ->
    forall on_zero on_zero', par_red1 on_zero on_zero' ->
    forall on_succ on_succ', par_red1 on_succ on_succ' ->
    forall num num', par_red1 num num' ->
    par_red1 (NatRec choice on_zero on_succ num) (NatRec choice' on_zero' on_succ' num')
  | nat_rec_on_zero_par_red :
    forall on_zero on_zero', par_red1 on_zero on_zero' ->
    forall choice on_succ, par_red1 (NatRec choice on_zero on_succ NatO) on_zero'
  | nat_rec_on_succ_par_red :
    forall choice choice', par_red1 choice choice' ->
    forall on_zero on_zero', par_red1 on_zero on_zero' ->
    forall on_succ on_succ', par_red1 on_succ on_succ' ->
    forall num num', par_red1 num num' ->
    par_red1 (NatRec choice on_zero on_succ (NatSucc num)) (App (App on_succ' num') (NatRec choice' on_zero' on_succ' num'))
  | nat_ind_par_red :
    forall choice choice', par_red1 choice choice' ->
    forall on_zero on_zero', par_red1 on_zero on_zero' ->
    forall on_succ on_succ', par_red1 on_succ on_succ' ->
    forall num num', par_red1 num num' ->
    par_red1 (NatInd choice on_zero on_succ num) (NatInd choice' on_zero' on_succ' num')
  | nat_ind_on_zero_par_red :
    forall on_zero on_zero', par_red1 on_zero on_zero' ->
    forall choice on_succ, par_red1 (NatInd choice on_zero on_succ NatO) on_zero'
  | nat_ind_on_succ_par_red :
    forall choice choice', par_red1 choice choice' ->
    forall on_zero on_zero', par_red1 on_zero on_zero' ->
    forall on_succ on_succ', par_red1 on_succ on_succ' ->
    forall num num', par_red1 num num' ->
    par_red1 (NatInd choice on_zero on_succ (NatSucc num)) (App (App on_succ' num') (NatInd choice' on_zero' on_succ' num'))
  (* Well founded induction *)
  | acc_prop_par_red :
    forall type type', par_red1 type type' ->
    forall rel rel', par_red1 rel rel' ->
    forall val val', par_red1 val val' ->
    par_red1 (AccProp type rel val) (AccProp type' rel' val')
  | acc_intro_par_red :
    forall type type', par_red1 type type' -> 
    forall rel rel', par_red1 rel rel' ->
    forall val val', par_red1 val val' ->
    forall proof proof', par_red1 proof proof' -> 
    par_red1 (AccIntro type rel val proof) (AccIntro type' rel' val' proof')
  | acc_rec_par_red :
    forall type type', par_red1 type type' -> 
    forall rel rel', par_red1 rel rel' -> 
    forall choice choice', par_red1 choice choice' -> 
    forall f f', par_red1 f f' -> 
    forall val val', par_red1 val val' ->
    forall proof proof', par_red1 proof proof' -> 
    par_red1 (AccRec type rel choice f val proof) (AccRec type' rel' choice' f' val' proof')
  | acc_rec_exec_par :
    forall type_a type_a', par_red1 type_a type_a' ->
    forall rel_a rel_a', par_red1 rel_a rel_a' ->
    forall val_a val_a', par_red1 val_a val_a' ->
    forall choice choice', par_red1 choice choice' -> 
    forall f f', par_red1 f f' -> 
    forall proof proof', par_red1 proof proof' ->
    forall type_b rel_b val_b,
    par_red1 
    (AccRec type_a rel_a choice f val_a (AccIntro type_b rel_b val_b proof)) 
    (
      App
      (App f' val_a')
      (
        Abs type_a' (
          Abs (App (App (lift 1 rel_a') (Ref 0)) (lift 1 val_a')) (
            AccRec
            (lift 2 type_a')
            (lift 2 rel_a')
            (lift 2 choice')
            (lift 2 f')
            (Ref 1)
            (App (App (lift 2 proof') (Ref 1)) (Ref 0))
          )
        )
      )
    )
  | acc_ind_par_red :
    forall type type', par_red1 type type' -> 
    forall rel rel', par_red1 rel rel' -> 
    forall choice choice', par_red1 choice choice' -> 
    forall f f', par_red1 f f' -> 
    forall val val', par_red1 val val' ->
    forall proof proof', par_red1 proof proof' -> 
    par_red1 (AccInd type rel choice f val proof) (AccInd type' rel' choice' f' val' proof')
  | acc_ind_exec_par :
    forall type_a type_a', par_red1 type_a type_a' ->
    forall rel_a rel_a', par_red1 rel_a rel_a' ->
    forall val_a val_a', par_red1 val_a val_a' ->
    forall choice choice', par_red1 choice choice' -> 
    forall f f', par_red1 f f' -> 
    forall proof proof', par_red1 proof proof' ->
    forall type_b rel_b val_b,
    par_red1 
    (AccInd type_a rel_a choice f val_a (AccIntro type_b rel_b val_b proof)) 
    (
      App
      (App f' val_a')
      (
        Abs type_a' (
          Abs (App (App (lift 1 rel_a') (Ref 0)) (lift 1 val_a')) (
            AccInd
            (lift 2 type_a')
            (lift 2 rel_a')
            (lift 2 choice')
            (lift 2 f')
            (Ref 1)
            (App (App (lift 2 proof') (Ref 1)) (Ref 0))
          )
        )
      )
    )
  (* Order for naturals *)
  | le_prop_par_red :
    forall l l', par_red1 l l' -> 
    forall r r', par_red1 r r' -> 
    par_red1 (Le l r) (Le l' r') 
  | le_n_par_red :
    forall n n' : term, par_red1 n n' -> 
    par_red1 (LeN n) (LeN n')
  | le_s_par_red :
    forall l l', par_red1 l l' ->
    forall r r', par_red1 r r' ->
    forall proof proof', par_red1 proof proof' -> 
    par_red1 (LeS l r proof) (LeS l' r' proof')
  | le_cases_par_red :
    forall choice choice', par_red1 choice choice' ->
    forall on_le_n on_le_n', par_red1 on_le_n on_le_n' ->
    forall on_le_s on_le_s', par_red1 on_le_s on_le_s' ->
    forall l l', par_red1 l l' ->
    forall r r', par_red1 r r' ->
    forall proof proof', par_red1 proof proof' ->
    par_red1 (LeCases choice on_le_n on_le_s l r proof) (LeCases choice' on_le_n' on_le_s' l' r' proof')
  | le_cases_on_le_n_par :
    forall on_le_n on_le_n', par_red1 on_le_n on_le_n' ->
    forall choice on_le_s l r n : term, par_red1 (LeCases choice on_le_n on_le_s l r (LeN n)) on_le_n'
  | le_cases_on_le_s_par :
    forall on_le_s on_le_s', par_red1 on_le_s on_le_s' ->
    forall r_b r_b', par_red1 r_b r_b' ->
    forall proof proof', par_red1 proof proof' ->
    forall choice on_le_n l_a r_a l_b, par_red1 (LeCases choice on_le_n on_le_s l_a r_a (LeS l_b r_b proof)) (App (App on_le_s' r_b') proof') 
  | le_ind_par_red :
    forall choice choice', par_red1 choice choice' -> 
    forall on_le_n on_le_n', par_red1 on_le_n on_le_n' ->
    forall on_le_s on_le_s', par_red1 on_le_s on_le_s' ->
    forall l l', par_red1 l l' ->
    forall r r', par_red1 r r' ->
    forall proof proof', par_red1 proof proof' ->
    par_red1 (LeInd choice on_le_n on_le_s l r proof) (LeInd choice' on_le_n' on_le_s' l' r' proof')
  | le_ind_on_le_n_par :
    forall on_le_n on_le_n', par_red1 on_le_n on_le_n' ->
    forall choice on_le_s l r n : term, par_red1 (LeInd choice on_le_n on_le_s l r (LeN n)) on_le_n'
  | le_ind_on_le_s_par :
    forall choice choice', par_red1 choice choice' ->
    forall on_le_n on_le_n', par_red1 on_le_n on_le_n' ->
    forall on_le_s on_le_s', par_red1 on_le_s on_le_s' ->
    forall l_b l_b', par_red1 l_b l_b' ->
    forall r_b r_b', par_red1 r_b r_b' ->
    forall proof proof', par_red1 proof proof' ->
    forall l_a r_a, par_red1 (LeInd choice on_le_n on_le_s l_a r_a (LeS l_b r_b proof)) (App (App (App on_le_s' r_b') proof') (LeInd choice' on_le_n' on_le_s' l_b' r_b' proof'))
  (* Bool and SumBool *)
  | bool_par_red : par_red1 Bool Bool
  | bool_true_par_red : par_red1 BoolTrue BoolTrue
  | bool_false_par_red : par_red1 BoolFalse BoolFalse
  | sumbool_type_par_red :
    forall l l', par_red1 l l' ->
    forall r r', par_red1 r r' ->
    par_red1 (SumBool l r) (SumBool l' r')
  | sumbool_left_par_red :
    forall left_pred left_pred', par_red1 left_pred left_pred' -> 
    forall right_pred right_pred', par_red1 right_pred right_pred' ->
    forall proof proof', par_red1 proof proof' ->
    par_red1 (SumBoolLeft left_pred right_pred proof) (SumBoolLeft left_pred' right_pred' proof')
  | sumbool_right_par_red :
    forall left_pred left_pred', par_red1 left_pred left_pred' -> 
    forall right_pred right_pred', par_red1 right_pred right_pred' ->
    forall proof proof', par_red1 proof proof' ->
    par_red1 (SumBoolRight left_pred right_pred proof) (SumBoolRight left_pred' right_pred' proof')
  | bool_ind_par_red : 
    forall choice choice', par_red1 choice choice' -> 
    forall on_true on_true', par_red1 on_true on_true' ->
    forall on_false on_false', par_red1 on_false on_false' ->
    forall bool bool', par_red1 bool bool' ->
    par_red1 (BoolInd choice on_true on_false bool) (BoolInd choice' on_true' on_false' bool')
  | bool_ind_true_par :
    forall on_true on_true', par_red1 on_true on_true' ->
    forall choice on_false, par_red1 (BoolInd choice on_true on_false BoolTrue) on_true'
  | bool_ind_false_par :
    forall on_false on_false', par_red1 on_false on_false' ->
    forall choice on_true, par_red1 (BoolInd choice on_true on_false BoolFalse) on_false'
  | bool_rec_par_red : 
    forall choice choice', par_red1 choice choice' -> 
    forall on_true on_true', par_red1 on_true on_true' ->
    forall on_false on_false', par_red1 on_false on_false' ->
    forall bool bool', par_red1 bool bool' ->
    par_red1 (BoolRec choice on_true on_false bool) (BoolRec choice' on_true' on_false' bool')
  | bool_rec_true_par :
    forall on_true on_true', par_red1 on_true on_true' ->
    forall choice on_false, par_red1 (BoolRec choice on_true on_false BoolTrue) on_true'
  | bool_rec_false_par :
    forall on_false on_false', par_red1 on_false on_false' ->
    forall choice on_true, par_red1 (BoolRec choice on_true on_false BoolFalse) on_false'
  | sumbool_ind_par_red :
    forall left_pred left_pred', par_red1 left_pred left_pred' -> 
    forall right_pred right_pred', par_red1 right_pred right_pred' ->
    forall choice choice', par_red1 choice choice' ->
    forall on_left on_left', par_red1 on_left on_left' ->
    forall on_right on_right', par_red1 on_right on_right' ->
    forall val val', par_red1 val val' ->
    par_red1 (SumBoolInd left_pred right_pred choice on_left on_right val) (SumBoolInd left_pred' right_pred' choice' on_left' on_right' val')
  | sumbool_ind_on_left_par :
    forall on_left on_left', par_red1 on_left on_left' ->
    forall proof proof', par_red1 proof proof' ->
    forall choice left_pred_a right_pred_a on_right left_pred_b right_pred_b,
    par_red1 (SumBoolInd left_pred_a right_pred_a choice on_left on_right (SumBoolLeft left_pred_b right_pred_b proof)) (App on_left' proof')
  | sumbool_ind_on_right_par :
    forall on_right on_right', par_red1 on_right on_right' ->
    forall proof proof', par_red1 proof proof' ->
    forall choice left_pred_a right_pred_a on_left left_pred_b right_pred_b,
    par_red1 (SumBoolInd left_pred_a right_pred_a choice on_left on_right (SumBoolRight left_pred_b right_pred_b proof)) (App on_right' proof')
  | sumbool_rec_par_red :
    forall left_pred left_pred', par_red1 left_pred left_pred' -> 
    forall right_pred right_pred', par_red1 right_pred right_pred' ->
    forall choice choice', par_red1 choice choice' ->
    forall on_left on_left', par_red1 on_left on_left' ->
    forall on_right on_right', par_red1 on_right on_right' ->
    forall val val', par_red1 val val' ->
    par_red1 (SumBoolRec left_pred right_pred choice on_left on_right val) (SumBoolRec left_pred' right_pred' choice' on_left' on_right' val')
  | sumbool_rec_on_left_par :
    forall on_left on_left', par_red1 on_left on_left' ->
    forall proof proof', par_red1 proof proof' ->
    forall choice left_pred_a right_pred_a on_right left_pred_b right_pred_b,
    par_red1 (SumBoolRec left_pred_a right_pred_a choice on_left on_right (SumBoolLeft left_pred_b right_pred_b proof)) (App on_left' proof')
  | sumbool_rec_on_right_par :
    forall on_right on_right', par_red1 on_right on_right' ->
    forall proof proof', par_red1 proof proof' ->
    forall choice left_pred_a right_pred_a on_left left_pred_b right_pred_b,
    par_red1 (SumBoolRec left_pred_a right_pred_a choice on_left on_right (SumBoolRight left_pred_b right_pred_b proof)) (App on_right' proof')
  (* Refinment types *)
  | refine_par_red :
    forall type type', par_red1 type type' ->
    forall property property', par_red1 property property' ->
    par_red1 (Refine type property) (Refine type' property')
  | refine_constr_par_red :
    forall type type', par_red1 type type' ->
    forall property property', par_red1 property property' ->
    forall val val', par_red1 val val' ->
    forall proof proof', par_red1 proof proof' ->
    par_red1 (RefineConstr type property val proof) (RefineConstr type' property' val' proof')
  | refine_proj_val_par_red :
    forall type type', par_red1 type type' ->
    forall property property', par_red1 property property' ->
    forall ref ref', par_red1 ref ref' ->
    par_red1 (RefineProjVal type property ref) (RefineProjVal type' property' ref')
  | refine_proj_proof_par_red :
    forall type type', par_red1 type type' ->
    forall property property', par_red1 property property' ->
    forall ref ref', par_red1 ref ref' ->
    par_red1 (RefineProjProof type property ref) (RefineProjProof type' property' ref')
  | refine_proj_val_exec_par :
    forall val val', par_red1 val val' ->
    forall type_a property_a type_b property_b proof, par_red1 (RefineProjVal type_a property_a (RefineConstr type_b property_b val proof)) val'
  | refine_proj_proof_exec_par :
    forall proof proof', par_red1 proof proof' ->
    forall type_a property_a type_b property_b val, par_red1 (RefineProjProof type_a property_a (RefineConstr type_b property_b val proof)) proof'
  (* Equality *)
  | eq_par_red :
    forall type type', par_red1 type type' ->
    forall l l', par_red1 l l' ->
    forall r r', par_red1 r r' ->
    par_red1 (Eq type l r) (Eq type' l' r')
  | eq_refl_par_red :
    forall type type', par_red1 type type' ->
    forall val val', par_red1 val val' -> 
    par_red1 (EqRefl type val) (EqRefl type' val')
  | eq_ind_par_red :
    forall type type', par_red1 type type' -> 
    forall l l', par_red1 l l' ->
    forall r r', par_red1 r r' ->
    forall property property', par_red1 property property' ->
    forall impl impl', par_red1 impl impl' ->
    forall proof proof', par_red1 proof proof' ->
    par_red1 (EqInd type l r property impl proof) (EqInd type' l' r' property' impl' proof')
  | eq_ind_par_exec :
    forall impl impl', par_red1 impl impl' ->
    forall type_a l r property type_b val, par_red1 (EqInd type_a l r property impl (EqRefl type_b val)) impl'
  | eq_rec_par_red :
    forall type type', par_red1 type type' -> 
    forall l l', par_red1 l l' ->
    forall r r', par_red1 r r' ->
    forall property property', par_red1 property property' ->
    forall impl impl', par_red1 impl impl' ->
    forall proof proof', par_red1 proof proof' ->
    par_red1 (EqRec type l r property impl proof) (EqRec type' l' r' property' impl' proof')
  | eq_rec_par_exec :
    forall impl impl', par_red1 impl impl' ->
    forall type_a l r property type_b val, par_red1 (EqRec type_a l r property impl (EqRefl type_b val)) impl'
  (* Falsity *)
  | false_par_red : par_red1 Falsity Falsity
  | false_ind_par_red :
    forall proof proof', par_red1 proof proof' ->
    forall property property', par_red1 property property' ->
    par_red1 (FalseInd proof property) (FalseInd proof' property')
  | false_rec_par_red :
    forall proof proof', par_red1 proof proof' ->
    forall property property', par_red1 property property' ->
    par_red1 (FalseRec proof property) (FalseRec proof' property')
  (* Unit *)
  | unit_par_red : par_red1 Unit Unit
  | nil_par_red : par_red1 Nil Nil
  (* well-founded recursion scheme *)
  | wf_rec_par_red : 
    forall type type', par_red1 type type' ->
    forall rel rel', par_red1 rel rel' ->
    forall choice choice', par_red1 choice choice' ->
    forall f f', par_red1 f f' ->
    forall proof proof', par_red1 proof proof' -> 
    par_red1 (WFrec type rel choice f proof) (WFrec type' rel' choice' f' proof')
  | wf_rec_expand_par :
    forall type type', par_red1 type type' ->
    forall rel rel', par_red1 rel rel' ->
    forall choice choice', par_red1 choice choice' ->
    forall f f', par_red1 f f' ->
    forall proof proof', par_red1 proof proof' ->
    par_red1 (WFrec type rel choice f proof) 
    (
      Abs type'
      (
        AccRec 
        (lift 1 type')
        (lift 1 rel')
        (lift 1 choice')
        (
          Abs (lift 1 type') (
            Abs (
              Prod (lift 2 type')
              (
                Prod (App (App (lift 3 rel') (Ref 0)) (Ref 1))
                (App (lift 4 choice') (Ref 1))
              )
            ) (
              App (App (lift 3 f') (Ref 1))
              (
                Abs (
                  Refine
                  (lift 3 type')
                  (Abs (lift 3 type') (App (App (lift 4 rel') (Ref 0)) (Ref 3)))
                )
                (
                  App 
                  (
                    App (Ref 1) 
                    (RefineProjVal (lift 4 type') (Abs (lift 4 type') (App (App (lift 5 rel') (Ref 0)) (Ref 3))) (Ref 0))
                  ) 
                  (RefineProjProof (lift 4 type') (Abs (lift 4 type') (App (App (lift 5 rel') (Ref 0)) (Ref 3))) (Ref 0)) 
                )
              )
            )  
          )
        )
        (Ref 0)
        (App (lift 1 proof') (Ref 0))
      )
    )
  (* bool prop choice *)
  | bool_prop_choice_par_red : 
    forall on_true on_true', par_red1 on_true on_true' ->
    forall on_false on_false', par_red1 on_false on_false' ->
    forall val val', par_red1 val val' ->
    par_red1 (BoolPropChoice on_true on_false val) (BoolPropChoice on_true' on_false' val')
  | bool_prop_true_par :
    forall on_true on_true', par_red1 on_true on_true' ->
    forall on_false, par_red1 (BoolPropChoice on_true on_false BoolTrue) on_true'
  | bool_prop_false_par :
    forall on_false on_false', par_red1 on_false on_false' ->
    forall on_true, par_red1 (BoolPropChoice on_true on_false BoolFalse) on_false'
  .

  (* Multistep parallel reduction *)
  Definition par_red := clos_trans term par_red1.

End Beta_Reduction.


Hint Resolve beta abs_red_l abs_red_r app_red_l app_red_r prod_red_l
  prod_red_r nat_destruct_choice nat_destruct_on_zero nat_destruct_on_succ 
  nat_destruct_num nat_destruct_choose_zero nat_destruct_choose_succ
  nat_cases_choice nat_cases_on_zero nat_cases_on_succ 
  nat_cases_num nat_cases_choose_zero nat_cases_choose_succ 
  nat_succ_red nat_rec_choice nat_rec_on_zero nat_rec_on_succ 
  nat_rec_num nat_rec_choose_zero nat_rec_choose_succ
  nat_ind_choice nat_ind_on_zero nat_ind_on_succ 
  nat_ind_num nat_ind_choose_zero nat_ind_choose_succ 
  acc_prop_type acc_prop_rel acc_prop_val acc_intro_type acc_intro_rel
  acc_intro_val acc_intro_proof acc_rec_type acc_rec_rel acc_rec_choice acc_rec_val
  acc_ind_val acc_rec_f acc_rec_proof acc_rec_exec acc_ind_type acc_ind_rel acc_ind_choice
  acc_ind_f acc_ind_proof acc_ind_exec le_prop_l le_prop_r le_n le_s_l le_s_r
  le_s_proof le_cases_choice le_cases_on_le_n le_cases_on_le_s le_cases_l
  le_cases_r le_cases_proof le_cases_exec_1 le_cases_exec_2 le_ind_choice
  le_ind_on_le_n le_ind_on_le_s le_ind_l le_ind_r le_ind_proof le_ind_exec_1
  le_ind_exec_2 sumbool_type_left sumbool_type_right sumbool_left_left_pred
  sumbool_left_right_pred sumbool_left_proof sumbool_right_left_pred sumbool_right_right_pred
  sumbool_right_proof bool_ind_choice bool_ind_on_true bool_ind_on_false bool_ind_bool bool_ind_true
  bool_ind_false bool_rec_choice bool_rec_on_true bool_rec_on_false bool_rec_bool bool_rec_true
  bool_rec_false sumbool_ind_left_pred sumbool_ind_right_pred sumbool_ind_choice sumbool_ind_on_left
  sumbool_ind_on_right sumbool_ind_val sumbool_ind_left sumbool_ind_right sumbool_rec_left_pred
  sumbool_rec_right_pred sumbool_rec_choice sumbool_rec_on_left sumbool_rec_on_right sumbool_rec_val
  sumbool_rec_left sumbool_rec_right refine_type refine_property refine_constr_type refine_constr_property
  refine_constr_val refine_constr_proof eq_prop_type eq_prop_l
  eq_prop_r eq_refl_type eq_refl_val eq_ind_type eq_ind_l eq_ind_r eq_ind_property eq_ind_proof eq_ind_exec
  eq_rec_type eq_rec_l eq_rec_r eq_rec_property eq_rec_proof eq_rec_exec refine_proj_val_exec refine_proj_proof_exec
  eq_ind_impl eq_rec_impl false_ind_proof false_ind_property false_rec_proof false_rec_property
  wf_rec_type wf_rec_rel wf_rec_choice wf_rec_f wf_rec_proof wf_rec_expand bool_prop_choice_on_true
  bool_prop_choice_on_false bool_prop_choice_val bool_prop_true bool_prop_false refine_proj_val_type
  refine_proj_val_property refine_proj_val_ref refine_proj_proof_type refine_proj_proof_property refine_proj_proof_ref
  : coc.
Hint Resolve refl_red refl_conv: coc.
Hint Resolve par_beta sort_par_red ref_par_red abs_par_red app_par_red
  prod_par_red nat_destruct_par_red nat_destruct_on_zero_par_red
  nat_destruct_on_succ_par_red nat_cases_par_red nat_cases_on_zero_par_red
  nat_cases_on_succ_par_red nat_succ_par_red nat_par_red nat_o_par_red
  nat_rec_par_red nat_rec_on_zero_par_red
  nat_rec_on_succ_par_red nat_ind_par_red nat_ind_on_zero_par_red
  nat_ind_on_succ_par_red acc_prop_par_red acc_intro_par_red acc_rec_par_red
  acc_rec_exec_par acc_ind_par_red acc_ind_exec_par le_prop_par_red le_n_par_red
  le_s_par_red le_cases_par_red le_cases_on_le_n_par le_cases_on_le_s_par le_ind_par_red
  le_ind_on_le_n_par le_ind_on_le_s_par sumbool_type_par_red sumbool_left_par_red 
  sumbool_right_par_red bool_ind_par_red bool_ind_true_par bool_ind_false_par bool_rec_par_red
  bool_rec_true_par bool_rec_false_par sumbool_ind_par_red sumbool_ind_on_left_par sumbool_ind_on_right_par
  sumbool_rec_par_red sumbool_rec_on_left_par sumbool_rec_on_right_par refine_par_red refine_constr_par_red
  refine_proj_val_par_red refine_proj_proof_par_red eq_par_red eq_refl_par_red eq_ind_par_red eq_ind_par_exec
  eq_rec_par_red eq_rec_par_exec false_par_red false_ind_par_red false_rec_par_red bool_par_red unit_par_red
  nil_par_red bool_true_par_red bool_false_par_red refine_proj_val_exec_par refine_proj_proof_exec_par
  wf_rec_par_red wf_rec_expand_par bool_prop_choice_par_red bool_prop_true_par bool_prop_false_par
  : coc.

Hint Unfold par_red: coc.


Section Normalisation_Forte.

  (* Irreducable term *)
  Definition normal t : Prop := forall u, ~ red1 t u.

  (* 
    Strongly normalizing term. 
    It's a term which is accassible with 
    transitively closed one-step reduction. 

    TODO: show equivalence to classical definition
  *)
  Definition sn : term -> Prop := Acc (transp _ red1).

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
  try (rewrite H by (auto with coc core arith sets); simpl in |- *);
  try (rewrite H0 by (auto with coc core arith sets); simpl in |- *);
  try (rewrite H1 by (auto with coc core arith sets); simpl in |- *);
  try (rewrite H2 by (auto with coc core arith sets); simpl in |- *);
  try (rewrite H3 by (auto with coc core arith sets); simpl in |- *);
  try (rewrite H4 by (auto with coc core arith sets); simpl in |- *);
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
  forall type type0 property property0 val val0,
  red type type0 -> red property property0 -> red val val0 -> 
  red (RefineProjVal type property val) (RefineProjVal type0 property0 val0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (RefineProjVal type property P); auto with core coc arith sets.

  intros.
  apply trans_red with (RefineProjVal type P val0); auto with core coc arith sets.

  intros.
  apply trans_red with (RefineProjVal P property0 val0); auto with core coc arith sets.
Qed.

Lemma red_red_proj_proof :
  forall type type0 property property0 val val0,
  red type type0 -> red property property0 -> red val val0 ->
  red (RefineProjProof type property val) (RefineProjProof type0 property0 val0)
.
Proof.
  simple induction 1.
  simple induction 1.
  simple induction 1; intros; auto with coc core arith sets.

  apply trans_red with (RefineProjProof type property P); auto with core coc arith sets.

  intros.
  apply trans_red with (RefineProjProof type P val0); auto with core coc arith sets.

  intros.
  apply trans_red with (RefineProjProof P property0 val0); auto with core coc arith sets.
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

  change (S (S (S (S (S k))))) with (5 + k).
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

  change (S (S (S (S (S k))))) with (5 + k).
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
    ); auto with coc core arith sets.
    unfold lift; auto 15 with coc core arith sets.

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
  change (S (S (S (S (S k))))) with (5 + k).
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

  change (S (S (S (S (S k))))) with (5 + k).
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

  inversion_clear H2.
  apply mem_refine_proj_val_type; apply H with n k; auto with coc core arith sets.
  apply mem_refine_proj_val_property; apply H0 with n k; auto with coc core arith sets.
  apply mem_refine_proj_val_ref; apply H1 with n k; auto with coc core arith sets.

  inversion_clear H2.
  apply mem_refine_proj_proof_type; apply H with n k; auto with coc core arith sets.
  apply mem_refine_proj_proof_property; apply H0 with n k; auto with coc core arith sets.
  apply mem_refine_proj_proof_ref; apply H1 with n k; auto with coc core arith sets.

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

  inversion_clear H2.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.

  inversion_clear H2.
  elim H with a n s; auto with coc core arith sets.
  elim H0 with a n s; auto with coc core arith sets.
  elim H1 with a n s; auto with coc core arith sets.

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

  inversion_clear H2; auto with coc.
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
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H2.
  inversion_clear H2.
  apply mem_sort_lift in H3; auto with coc core arith sets.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  inversion_clear H3.
  inversion_clear H3.
  inversion_clear H3.
  apply mem_sort_lift in H2; auto with coc core arith sets.
  inversion_clear H2.
  apply mem_sort_lift in H3; auto with coc core arith sets.
  inversion_clear H3.
  inversion_clear H2.
  apply mem_sort_lift in H3; auto with coc core arith sets.
  inversion_clear H3.
  inversion_clear H2.
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

  exists (RefineProjVal z a2 a3); auto with coc core arith sets.

  exists (RefineProjVal a1 z a3); auto with coc core arith sets.

  exists (RefineProjVal a1 a2 z); auto with coc core arith sets.

  exists (RefineProjProof z a2 a3); auto with coc core arith sets.

  exists (RefineProjProof a1 z a3); auto with coc core arith sets.

  exists (RefineProjProof a1 a2 z); auto with coc core arith sets.

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
