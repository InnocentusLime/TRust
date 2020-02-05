Require Import ImTermes.
Require Import Termes.
Require Import Types.
Require Export MyList.

Fixpoint extract (t : Termes.term) { struct t } : ImTermes.term :=
    match t with
    | RefineConstr _ _ val _ => extract val
    | Ref i => ImTermes.Ref i
    | Abs T M => ImTermes.Abs T (extract M)
    | App u v => ImTermes.App (extract u) (extract v)
    (* Eliminators *)
    | NatDestruct choice on_zero on_succ num => ImTermes.NatDestruct choice (extract on_zero) (extract on_succ) (extract num)
    | BoolRec choice on_true on_false bool => ImTermes.BoolRec choice (extract on_true) (extract on_false) (extract bool)
    | WFrec type rel choice f proof => ImTermes.Rec type rel choice (extract f)
    | _ => StrictBox t
    end
.

Definition interepts (t : Termes.term) (t' : ImTermes.term) : Prop := extract t = t'.

Definition assums := list (Types.env * Termes.term).

Definition item_lift t e n :=
  ex2 (fun u => t = lift (S n) u) (fun u => item term u (e:list term) n)
.

Inductive subtyp : Types.env -> assums -> Termes.term -> Termes.term -> Prop :=

with typ : Types.env -> assums -> ImTermes.term -> Termes.term -> Prop :=
| add_assum :   
    forall e ass t T, typ e ass t T ->
    forall e0 P, Types.typ e0 P (Srt prop) ->
    typ e ((e0, P) :: ass) t T
| type_boxed : 
    forall e t T,
    Types.typ e t T ->
    typ e nil (StrictBox t) T
| type_var :
    forall e,
    wf e -> forall (v : nat) t, item_lift t e v -> typ e nil (ImTermes.Ref v) t (* Instead the items get lifted afterwards... I guess that's more convinient? *)
| type_abs :
    forall e ass T s1,
    Types.typ e T (Termes.Srt s1) ->
    forall M (U : Termes.term) s2,
    Types.typ (T :: e) U (Termes.Srt s2) ->
    typ (T :: e) ass M U -> 
    typ e ass (ImTermes.Abs T M) (Termes.Prod T U)
| type_app :
    forall e ass (v : ImTermes.term) (v' : Termes.term) (V : Termes.term),
    typ e ass v V ->
    forall u (Ur : Termes.term),
    Types.typ e v' V ->
    interepts v' v ->
    typ e ass u (Prod V Ur) -> typ e ass (ImTermes.App u v) (subst v' Ur)
| type_conv :
    forall e ass t (U V : Termes.term),
    typ e ass t U -> Termes.conv U V -> forall s, Types.typ e V (Srt s) -> typ e ass t V
| type_subtype : 
    forall e ass t T1 T2,
    typ e ass t T1 ->
    subtyp e ass T1 T2 ->
    typ e ass t T2
| type_nat_destruct :
    forall e ass (x1 : Termes.term) x2 x3 x4 x4', 
    Types.typ e x1 (Termes.Prod Termes.Nat (Termes.Srt Termes.set)) ->
    typ e ass x2 (Termes.App x1 Termes.NatO) ->
    typ e ass x3 
    (
      Termes.Prod Termes.Nat 
      (
        Termes.App 
        (Termes.lift 1 x1) 
        (Termes.NatSucc (Termes.Ref 0))
      )
    ) ->
    typ e ass x4 Termes.Nat ->
    x4 = extract x4' ->
    typ e ass (NatDestruct x1 x2 x3 x4) (Termes.App x1 x4')
.
