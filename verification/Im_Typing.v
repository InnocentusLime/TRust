Require Import Program.Equality.

Require List.
Require Import Term.
Require Import String.
Require Import Context.
Require Import ListLemmas.
Require Import TermReduction.

Reserved Notation "G |-im x := y" (at level 85, no associativity).

(* Typing rules *)
Inductive typing_im : context -> term -> term -> Prop :=
(* Core typing *)
| Im_TNat :
    forall (ctx : context),
    WF_im ctx ->
    ctx |-im Nat := SmallKind
| Im_TNatO : 
    forall (ctx : context),
    WF_im ctx ->
    ctx |-im NatO := Nat
| Im_TNatSucc : 
    forall (ctx : context),
    WF_im ctx ->
    ctx |-im NatSucc := Forall "_"%string Nat Nat
| Im_TNatRec : 
    forall (ctx : context),
    forall choice zero step num : term,
    ctx |-im choice := Nat ===> SmallKind -> 
    ctx |-im zero := App choice NatO ->
    ctx |-im step := Forall "n"%string Nat (App (lift choice 0 1) (Var 0) ===> App (lift choice 0 2) (App NatSucc (Var 1))) ->
    ctx |-im num := Nat ->
    ctx |-im NatRec choice zero step num := App choice num
| Im_TApp : 
    forall (ctx : context),
    forall (str : string) (domain range : term) (l r : term),
    ctx |-im l := Forall str domain range ->
    ctx |-im r := domain ->
    ctx |-im App l r := top_subst range r
| Im_TAbsSmall : 
    forall (ctx : context),
    forall (str : string) (range : term) (arg_type body : term),
    ctx |-im arg_type := SmallKind ->
    push_var ctx str arg_type |-im body := range ->
    ctx |-im Abs str arg_type body := Forall str arg_type range
| Im_TAbsType : 
    forall (ctx : context),
    forall (str : string) (range : term) (arg_type body : term) (i : nat),
    ctx |-im arg_type := TypeKind i ->
    { str == arg_type } :: ctx |-im body := range ->
    ctx |-im Abs str arg_type body := Forall str arg_type range
| Im_TAbsProp : 
    forall (ctx : context),
    forall (str : string) (range : term) (arg_type body : term),
    ctx |-im arg_type := PropKind ->
    { str == arg_type } :: ctx |-im body := range ->
    ctx |-im Abs str arg_type body := Forall str arg_type range
| Im_TVar : 
    forall (ctx : context),
    forall (n : nat) (t : term), 
    WF_im ctx -> 
    ctx[n] := t -> 
    ctx |-im Var n := t
| Im_TSmallKind : 
    forall (ctx : context),
    WF_im ctx -> 
    ctx |-im SmallKind := TypeKind 0
| Im_TPropKind :
    forall (ctx : context),
    WF_im ctx -> 
    ctx |-im PropKind := TypeKind 0
| Im_TTypeKind : 
    forall (ctx : context),
    WF_im ctx -> 
    forall n : nat, ctx |-im TypeKind n := TypeKind (S n)
| Im_TForallType : 
    forall (ctx : context),
    forall (str : string) (domain range : term) (universe : nat),
    ctx |-im domain := TypeKind universe ->
    { str == domain } :: ctx |-im range := TypeKind universe ->
    ctx |-im Forall str domain range := TypeKind universe
| Im_TForallPropSmall : 
    forall (ctx : context),
    forall (str : string) (domain range : term),
    ctx |-im domain := SmallKind ->
    { str == domain } :: ctx |-im range := PropKind ->
    ctx |-im Forall str domain range := PropKind
| Im_TForallPropProp : 
    forall (ctx : context),
    forall (str : string) (domain range : term),
    ctx |-im domain := PropKind ->
    { str == domain } :: ctx |-im range := PropKind ->
    ctx |-im Forall str domain range := PropKind
| Im_TForallPropType : 
    forall (ctx : context),
    forall (str : string) (domain range : term),
    forall (i : nat), ctx |-im domain := TypeKind i ->
    { str == domain } :: ctx |-im range := PropKind ->
    ctx |-im Forall str domain range := PropKind
| Im_TForallSmallSmall : 
    forall (ctx : context),
    forall (str : string) (domain range : term),
    ctx |-im domain := SmallKind ->
    { str == domain } :: ctx |-im range := SmallKind ->
    ctx |-im Forall str domain range := SmallKind
| Im_TForallSmallProp : 
    forall (ctx : context),
    forall (str : string) (domain range : term),
    ctx |-im domain := PropKind ->
    { str == domain } :: ctx |-im range := SmallKind ->
    ctx |-im Forall str domain range := SmallKind
(* Universe transition rules *)
| Im_JumpToTypeUniverseSmall :
    forall (ctx : context),
    forall (t : term),
    ctx |-im t := SmallKind ->
    ctx |-im t := TypeKind 0
| Im_JumpToTypeUniverseProp :
    forall (ctx : context),
    forall (t : term),
    ctx |-im t := PropKind ->
    ctx |-im t := TypeKind 0
| Im_RaiseUniverse : 
    forall (ctx : context),
    forall (t : term) (universe : nat),
    ctx |-im t := TypeKind universe ->
    ctx |-im t := TypeKind (S universe)
(* Conversion axioms *)
| Im_ConversionSmallL : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |-im t := type ->
    ctx |-im type := SmallKind ->
    type ->b type' ->
    ctx |-im type' := SmallKind ->
    ctx |-im t := type'
| Im_ConversionPropL : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |-im t := type ->
    ctx |-im type := PropKind ->
    type ->b type' ->
    ctx |-im type' := PropKind ->
    ctx |-im t := type'
| Im_ConversionTypeL : 
    forall (ctx : context),
    forall (t : term) (type type' : term) (i : nat),
    ctx |-im t := type ->
    ctx |-im type := TypeKind i ->
    type ->b type' ->
    ctx |-im type' := TypeKind i ->
    ctx |-im t := type'
| Im_ConversionSmallR : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |-im t := type ->
    ctx |-im type := SmallKind ->
    type' ->b type ->
    ctx |-im type' := SmallKind ->
    ctx |-im t := type'
| Im_ConversionPropR : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |-im t := type ->
    ctx |-im type := PropKind ->
    type' ->b type ->
    ctx |-im type' := PropKind ->
    ctx |-im t := type'
| Im_ConversionTypeR : 
    forall (ctx : context),
    forall (t : term) (type type' : term) (i : nat),
    ctx |-im t := type ->
    ctx |-im type := TypeKind i ->
    type' ->b type ->
    ctx |-im type' := TypeKind i ->
    ctx |-im t := type'
| Im_ConversionSmallRename : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |-im t := type ->
    ctx |-im type := SmallKind ->
    type =a type' ->
    ctx |-im type' := SmallKind ->
    ctx |-im t := type'
| Im_ConversionPropRename : 
    forall (ctx : context),
    forall (t : term) (type type' : term),
    ctx |-im t := type ->
    ctx |-im type := PropKind ->
    type =a type' ->
    ctx |-im type' := PropKind ->
    ctx |-im t := type'
| Im_ConversionTypeRename : 
    forall (ctx : context),
    forall (t : term) (type type' : term) (i : nat),
    ctx |-im t := type ->
    ctx |-im type := TypeKind i ->
    type =a type' ->
    ctx |-im type' := TypeKind i ->
    ctx |-im t := type'
(*Refinement types!*)
| Im_RefinementSmall :
    forall (ctx : context),
    forall (t condition : term) (type : term),
    ctx |-im t := type ->
    ctx |-im type := SmallKind ->
    ctx |-im condition := type ===> PropKind ->
    ctx |-im (Refine t condition) := SmallKind
| Im_RefinementType :
    forall (ctx : context),
    forall (t condition : term) (type : term) (universe : nat),
    ctx |-im t := type ->
    ctx |-im type := TypeKind universe ->
    ctx |-im condition := type ===> PropKind ->
    ctx |-im (Refine t condition) := TypeKind universe
(* Well formed context axioms *)
with WF_im : context -> Prop :=
| Im_WF_empty : WF_im nil
| Im_WF_assum_small : 
    forall (ctx : context) (str : string) (t : term),
    WF_im ctx ->
    ctx |-im t := SmallKind ->
    WF_im (push_var ctx str t)
| Im_WF_assum_prop :
    forall (ctx : context) (str : string) (t : term),
    WF_im ctx ->
    ctx |-im t := PropKind ->
    WF_im (push_var ctx str t)
| Im_WF_assum_type :
    forall (ctx : context) (str : string) (t : term) (i : nat),
    WF_im ctx ->
    ctx |-im t := TypeKind i ->
    WF_im (push_var ctx str t)
| Im_WF_dummy_assum :
    forall (ctx : context),
    WF_im ctx ->
    WF_im (push_dummy ctx)

where "G |-im x := y" := (typing_im G x y)
.

(* Induction scheme when the simple induction won't do the trick *)
Scheme typing_im_ind_mut := Induction for 
typing_im Sort Prop
with wf_im_ind_mut := Induction for 
WF_im Sort Prop.

Definition typable (ctx : context) (t : term) := exists type : term, ctx |-im t := type.
Notation "G |-im x := ?" := (typable G x) (at level 85, no associativity).

Theorem typable_wf : forall (ctx : context) (t type : term),
    ctx |-im t := type ->
    WF_im ctx
.
Proof.
    intros.
    induction H; try easy.
Qed.