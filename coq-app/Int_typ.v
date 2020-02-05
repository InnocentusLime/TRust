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
  This is another module about interpretations. The first drafts were
  made in the `Int_term.v` module, so go see it if you haven't. This
  module also uses the notion of `scheme` --- check `Can.v` for more
  info.
  
  We'll keep quoting the original `coq-in-coq` article.
*)

Require Import Termes.
Require Import Conv.
Require Import Types.
Require Import Class.
Require Import Can.


(* 
  The interpretation of variables is either a dependent pair or 
  `square`. Thie original artice then shows the the dependent
  pair will correspond to the `Kind s` (`s` is a skelton) and the 
  `square` corresponds to `Type *`. 

  The idea is that to interpret a term variable, we only need a
  term (I n) whereas a predicate variable has to be interepted
  both by scheme and a term.
*)
Inductive Int_K : Type :=
| iK : forall s : skel, Can s -> Int_K  (* For predicate variables *)
| iT : Int_K                            (* For term variables *)
.

(* `intP` is the same thing for contexts? *)
Definition intP := TList Int_K.

(*
  Here our idea of what each constructor of `Int_K` corresponds
  to is expressed with this function.
*)
Definition class_of_ik (ik : Int_K) :=
  match ik with
  | iK s _ => Knd s
  | iT => Typ PROP
end.

(*
  We create the same function for mapping `intP` to class 
  context
*)
Definition cls_of_int : intP -> cls := Tmap _ _ class_of_ik.

(* 
  This function infers the `Int_K` for a term given the
  environment.
*)
Definition ext_ik (T : term) (ip : intP) (s : skel) 
(C : Can s) : Int_K 
:=
  match cl_term T (cls_of_int ip) with
  | Knd _ => iK s C
  | _ => iT
  end
.

(* 
  The `cons` operator for `intP` which puts a term
  into an environment.
*)
Definition int_cons (T : term) (ip : intP) (s : skel) 
(C : Can s) : intP 
:= TCs _ (ext_ik T ip s C) ip.

(*
  We can append canonical schemes.
*)
Definition def_cons (T : term) (I : intP) : intP :=
  int_cons T I _ (default_can (cv_skel (cl_term T (cls_of_int I))))
.

(* Skeleton (order) projection *)
Definition skel_int (t : term) (I : intP) := typ_skel (cl_term t (cls_of_int I)).

(* 
  A lemma about element in an evironment we get by
  `interpreting` a context. 
*)
Lemma ins_in_cls :
  forall (c : class) (y : Int_K) (k : nat) (ipe ipf : intP),
  class_of_ik y = c ->
  TIns Int_K y k ipe ipf -> 
  TIns _ c k (cls_of_int ipe) (cls_of_int ipf)
.
Proof.
  unfold cls_of_int in |- *.
  simple induction 1.
  simple induction 1; simpl in |- *; auto with coc core arith datatypes.
Qed.

(* 
  A function which by skeleton and interpretation can
  constructor a scheme of corresponding order.
*)
Definition coerce_CR (s : skel) (i : Int_K) : Can s :=
  match i with
  | iK si Ci => (
    match EQ_skel si s with
    | left y =>
      match y in (_ = x) return (Can x) with
      | refl_equal => Ci
      end
    | _ => default_can s
    end
  )
  | _ => default_can s
  end
.

(*
  We show that this function is capable of building a candidate
  of order `s'`
*)
Lemma is_can_coerce :
  forall s s' C, is_can s C -> is_can s' (coerce_CR s' (iK s C))
.
Proof.
  simpl in |- *; intros.
  elim (EQ_skel s s'); intros; auto with coc.
  case a; trivial.
Qed.

Hint Resolve is_can_coerce: coc.

(*
  It is enough to prove a property for the original scheme to
  make it hold to its coerced counterpart.
*)
Lemma extr_eq :
  forall (P : forall s : skel, Can s -> Prop) (s : skel) (c : Can s),
  P s c -> P s (coerce_CR s (iK s c))
.
Proof.
  intros.
  unfold coerce_CR in |- *.
  elim (EQ_skel s s).
  intro Heq.
  change
    ((fun s0 (e : s = s0) =>
      P s0 match e in (_ = x) return (Can x) with
          | refl_equal => c
          end) s Heq) in |- *.
  case Heq; trivial.

  simple induction 1; auto with coc core arith datatypes.
Qed.

(*
  Coercsions of existensially equal schemes are existensially
  equal.
*)
Lemma eq_can_extr :
  forall (s si : skel) (X Y : Can s),
  eq_can s X Y -> eq_can si (coerce_CR si (iK s X)) (coerce_CR si (iK s Y))
.
Proof.
  unfold coerce_CR in |- *.
  intros.
  elim (EQ_skel s si); auto with coc core arith datatypes.
  intro Heq; case Heq; auto with coc core arith datatypes.
Qed.

Hint Resolve eq_can_extr: coc.

(* Equaity of two type interpretations *)
Inductive ik_eq : Int_K -> Int_K -> Prop :=
| eqi_K :
  forall (s : skel) (X Y : Can s),
    eq_can s X X ->
    eq_can s Y Y -> eq_can s X Y -> 
  ik_eq (iK s X) (iK s Y)
| eqi_T : ik_eq iT iT
.

Hint Resolve eqi_K eqi_T: coc.

(* Equality of schemes imples equality of interpretations *)
Lemma iki_K : forall (s : skel) (C : Can s), eq_can s C C -> ik_eq (iK s C) (iK s C).
Proof.
  auto with coc core arith datatypes.
Qed.

Hint Resolve iki_K: coc.

(* Equality for interpretation context *)
Definition int_eq_can : intP -> intP -> Prop := Tfor_all2 _ _ ik_eq.
(* We define the invariant interpretation context *)
Definition int_inv (i : intP) := int_eq_can i i.

Hint Unfold int_eq_can int_inv: coc.

(* A lemma about preserving invariant by removing a element *)
Lemma ins_int_inv :
  forall (e f : intP) (k : nat) (y : Int_K),
  TIns _ y k e f -> int_inv f -> int_inv e
.
Proof.
  unfold int_inv, int_eq_can in |- *.
  simple induction 1; intros; auto with coc core arith datatypes.
  inversion_clear H0; auto with coc core arith datatypes.

  inversion_clear H2; auto with coc core arith datatypes.
Qed.

(* Just unfolding the definition of invaraint *)
Lemma int_inv_int_eq_can : forall i : intP, int_inv i -> int_eq_can i i.
Proof.
  auto with coc core arith datatypes.
Qed.


Hint Resolve int_inv_int_eq_can: coc.

(*
  If two interpretations of contexts are equal, their class
  environments are equal
*)
Lemma int_eq_can_cls :
  forall i i' : intP, int_eq_can i i' -> cls_of_int i = cls_of_int i'
.
Proof.
  unfold cls_of_int in |- *.
  simple induction 1; simpl in |- *; intros; auto with coc core arith datatypes.
  inversion_clear H0; simpl in |- *; intros; elim H2;
  auto with coc core arith datatypes.
Qed.

(* 
  Let `T` be a term. Give the interpretation context `ip` 
  and a skeleton one defines the type interpretation (scheme) by:
*)
Fixpoint int_typ (T : term) : intP -> forall s : skel, Can s :=
  fun (ip : intP) (s : skel) =>
  match T with
  | Srt _ => default_can s
  | Ref n => coerce_CR s (Tnth_def _ (iK PROP sn) ip n)
  | Abs A t =>
    match cl_term A (cls_of_int ip) with
    | Knd _ =>
      match s as x return (Can x) with
      | PROD s1 s2 =>
        fun C : Can s1 => int_typ t (TCs _ (iK s1 C) ip) s2
      | PROP => default_can PROP
      end
    | Typ _ => int_typ t (def_cons A ip) s
    | _ => default_can s
    end
  | App u v =>
    match cl_term v (cls_of_int ip) with
    | Trm => int_typ u ip s
    | Typ sv => int_typ u ip (PROD sv s) (int_typ v ip sv)
    | _ => default_can s
    end
  | Prod A B =>
    match s as x return (Can x) with
    | PROP =>
      let s := cv_skel (cl_term A (cls_of_int ip)) in
      Pi s (int_typ A ip PROP) (fun C => int_typ B (int_cons A ip s C) PROP)
    | PROD s1 s2 => default_can (PROD s1 s2)
    end
  (* New terms *)
  | Nat => default_can s
  | NatO => default_can s
  | NatSucc _ => default_can s
  | NatDestruct _ _ _ _ => default_can s
  | NatCases _ _ _ _ => default_can s 
  (* They are `defauly_can`s because are never supposed to reduce to types *)
  end
.