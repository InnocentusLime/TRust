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



Require Import Termes.
Require Import Conv.
Require Import Types.
Require Import Strong_Norm.
Require Import Conv_Dec.

Load "ImpVar".

(* 
  We either return a sort the term reduces to or give nothing and prove 
  that the the term is not convertible to a sort.
*)
Definition red_to_sort :
  forall t,
  sn t -> {s : sort | red t (Srt s)} + {(forall s, ~ conv t (Srt s))}.
Proof.
  intros t snt.
  elim compute_nf with (1 := snt); 
  intros [
    s | n | T b | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redt nt;
  try (
    solve [
      (
        match goal with
        | nt : normal ?W |- _ => (
          right; red in |- *; intros;
          elim church_rosser with (Srt s) W; 
          [>
            intros W' H0 H1;
            generalize H0;
            elim (red_normal W W'); auto with coc; intros;
            apply red_sort_sort with s W; auto with coc;
            discriminate |
            intros;
            apply trans_conv_conv with t; auto with coc
          ]
        )
        end
      )
    ]
  ).
  left; exists s; trivial.
Defined.

(* Same goes for reduction to a product *)
Definition red_to_prod :
  forall t, sn t ->
  {
    p : term * term | 
    match p with
    | (u, v) => red t (Prod u v)
    end
  } + 
  {
    (forall u v, ~ conv t (Prod u v))
  }.
Proof.
  intros t snt.
  elim compute_nf with (1 := snt); 
  intros [
    s | n | T b | a b | T U | (**) | (**) | num_x | x1 x2 x3 x4 | x1 x2 x3 x4 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | x1 x2 | x | x1 x2 x3 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | (**) | (**) | x1 x2 x3 | x1 x2 x3 |
    x1 x2 x3 x4 | x1 x2 x3 x4 | x1 x2 x3 x4 x5 x6 | x1 x2 x3 x4 x5 x6 |
    x1 x2 | x1 x2 x3 x4 | x | x | x1 x2 x3 | x1 x2 | x1 x2 x3 x4 x5 x6 |
    x1 x2 x3 x4 x5 x6 | (**) | x1 x2 | x1 x2 | (**) | (**) | x1 x2 x3 x4 x5 | x1 x2 x3
  ] redt nt;
  try (
    solve [
      (
        match goal with
        | nt : normal ?W |- _ => (
          right; red in |- *; intros;
          elim church_rosser with (Prod u v) W; 
          [>
            intros W' H0 H1;
            generalize H0;
            elim (red_normal W W'); auto with coc; intros;
            apply red_prod_prod with u v W; auto with coc; intros;
            discriminate H3 |
            intros;
            apply trans_conv_conv with t; auto with coc
          ]
        )
        end
      )
    ]
  ).

  left; exists (T, U); trivial.
Defined.

Section TypeChecker.

(*)
  (* Type-checker's error code *)
  Inductive type_error : Set :=
  (* 
    A special wrapper-error-code to show that an error has happened in 
    an extended environment 
  *)
  | Under : term -> type_error -> type_error
  (*
    We expected a type, but got not a type?
  *)
  | Expected_type : term -> term -> term -> type_error
  (*
    Ill-formed kind
  *)
  | Kind_ill_typed : type_error
  (*
    Failed to fetch a variable
  *)
  | Db_error : nat -> type_error
  (*
    Attempt to abstract over `kind`
  *)
  | Lambda_kind : term -> type_error
  (*
    Expected a type, got a term
  *)
  | Not_a_type : term -> term -> type_error
  (*
    The left part of the application is not
    a function.
  *)
  | Not_a_fun : term -> term -> type_error
  (*
    THe right side of application has a type
    which doesn't match the left side's domain.
  *)
  | Apply_err : term -> term -> term -> term -> type_error
  (* New errors *)
  (*
    The successor constructor got a wrong 
    argument
  *)
  | NatSucc_err : term -> term -> type_error
  (*
    The match statement for natural numbers
    got a wrong choice function
  *)
  | NatDestruct_Choice_err : term -> term -> type_error
  (*
    The match statement for natural numbers
    got a wrong reaction for zero
  *)
  | NatDestruct_OnZero_err : term -> term -> term -> type_error
  (*
    The match statement for natural numbers
    got a wrong recution for succ
  *)
  | NatDestruct_OnSucc_err : term -> term -> term -> type_error
  (*
    The match statement for natural numbers
    got a wrong recursion argument
  *)
  | NatDestruct_Num_err : term -> term -> type_error
  (*
    The case statement for natural numbers
    got a wrong choice function
  *)
  | NatCases_Choice_err : term -> term -> type_error
  (*
    The case statement for natural numbers
    got a wrong reaction for zero
  *)
  | NatCases_OnZero_err : term -> term -> term -> type_error
  (*
    The case statement for natural numbers
    got a wrong recution for succ
  *)
  | NatCases_OnSucc_err : term -> term -> term -> type_error
  (*
    The case statement for natural numbers
    got a wrong recursion argument
  *)
  | NatCases_Num_err : term -> term -> type_error
  .

  (* meaning of errors *)
  Inductive expln : env -> type_error -> Prop :=
  | Exp_under :
    forall e t (err : type_error),
    expln (t :: e) err -> expln e (Under t err)
  | Exp_exp_type :
    forall e (m at_ et : term),
    typ e m at_ ->
    typ e m et ->
    free_db (length e) et -> expln e (Expected_type m at_ et)
  | Exp_kind :
    forall e,
    wf e -> (forall t, ~ typ e (Srt kind) t) -> expln e Kind_ill_typed
  | Exp_db : forall e n, wf e -> length e <= n -> expln e (Db_error n)
  | Exp_lam_kind :
    forall e (m : term) t,
    typ (t :: e) m (Srt kind) -> expln e (Lambda_kind (Abs t m))
  | Exp_type :
    forall e (m : term) t,
    typ e m t ->
    (forall s, ~ typ e m (Srt s)) -> expln e (Not_a_type m t)
  | Exp_fun :
    forall e (m : term) t,
    typ e m t ->
    (forall a b : term, ~ typ e m (Prod a b)) -> expln e (Not_a_fun m t)
  | Exp_appl_err :
    forall e u v (a b tv : term),
    typ e u (Prod a b) ->
    typ e v tv -> ~ typ e v a -> expln e (Apply_err u (Prod a b) v tv)
  (* New terms *)
  | Exp_nat_succ :
    forall e t T,
    typ e t T ->
    ~ typ e t Nat ->
    expln e (NatSucc_err t T)
  | Exp_nat_destruct_choice :
    forall e choice T,
    typ e choice T ->
    ~ typ e choice (Prod Nat (Srt set)) ->
    expln e (NatDestruct_Choice_err choice T)
  | Exp_nat_destruct_on_zero :
    forall e choice on_zero T,
    typ e on_zero T ->
    ~ typ e on_zero (App choice NatO) ->
    expln e (NatDestruct_OnZero_err choice on_zero T)
  | Exp_nat_destruct_on_succ :
    forall e choice on_succ T,
    typ e on_succ T ->
    ~ typ e on_succ (Prod Nat (App (lift 1 choice) (NatSucc (Ref 0)))) ->
    expln e (NatDestruct_OnSucc_err choice on_succ T)
  | Exp_nat_destruct_num :
    forall e num T,
    typ e num T ->
    ~ typ e num Nat ->
    expln e (NatDestruct_Num_err num T)
  | Exp_nat_cases_choice :
    forall e choice T,
    typ e choice T ->
    ~ typ e choice (Prod Nat (Srt prop)) ->
    expln e (NatCases_Choice_err choice T)
  | Exp_nat_cases_on_zero :
    forall e choice on_zero T,
    typ e on_zero T ->
    ~ typ e on_zero (App choice NatO) ->
    expln e (NatCases_OnZero_err choice on_zero T)
  | Exp_nat_cases_on_succ :
    forall e choice on_succ T,
    typ e on_succ T ->
    ~ typ e on_succ (Prod Nat (App (lift 1 choice) (NatSucc (Ref 0)))) ->
    expln e (NatCases_OnSucc_err choice on_succ T)
  | Exp_nat_cases_num :
    forall e num T,
    typ e num T ->
    ~ typ e num Nat ->
    expln e (NatCases_Num_err num T)
  .

  Hint Resolve Exp_under Exp_exp_type Exp_kind Exp_db Exp_lam_kind Exp_type
    Exp_fun Exp_appl_err: coc.

  (* Explanation is always given under a well-formed context *)
  Lemma expln_wf : forall e (err : type_error), expln e err -> wf e.
  Proof.
    simple induction 1; intros; auto with coc arith.
    inversion_clear H1.
    apply typ_wf with t (Srt s); auto with coc arith.

    apply typ_wf with m at_; auto with coc arith.

    cut (wf (t :: e0)); intros.
    inversion_clear H1.
    apply typ_wf with t (Srt s); auto with coc arith.

    apply typ_wf with m (Srt kind); auto with coc arith.

    apply typ_wf with m t; auto with coc arith.

    apply typ_wf with m t; auto with coc arith.

    apply typ_wf with v tv; auto with coc arith.

    apply typ_wf with t T; auto with coc arith.

    apply typ_wf with choice T; auto with coc arith.

    apply typ_wf with on_zero T; auto with coc arith.

    apply typ_wf with on_succ T; auto with coc arith.

    apply typ_wf with num T; auto with coc arith.

    apply typ_wf with choice T; auto with coc arith.

    apply typ_wf with on_zero T; auto with coc arith.

    apply typ_wf with on_succ T; auto with coc arith.

    apply typ_wf with num T; auto with coc arith.
  Qed.

  (* Inference error *)
  Inductive inf_error : term -> type_error -> Prop :=
  (* This error happened in a subterm *)
  | Infe_subt :
    forall (m n : term) (err : type_error),
    subt_nobind m n -> inf_error m err -> inf_error n err
  (* This error happened in an extneded environment *)
  | Infe_under :
    forall (m n : term) T (err : type_error),
    subt_bind T m n -> inf_error m err -> inf_error n (Under T err)
  (* This is a kind error *)
  | Infe_kind : inf_error (Srt kind) Kind_ill_typed
  (* This is an error about DB *)
  | Infe_db : forall n, inf_error (Ref n) (Db_error n)
  (* This is an error about lamda using a kind *)
  | Infe_lam_kind : forall M T, inf_error (Abs T M) (Lambda_kind (Abs T M))
  (* This is an error  *)
  | Infe_type_abs :
    forall (m n : term) t, inf_error (Abs m n) (Not_a_type m t)
  (* This is an error about a term not being a function *)
  | Infe_fun : forall (m n : term) t, inf_error (App m n) (Not_a_fun m t)
  (* This is an error about term's type4 not satisfying the domain type *)
  | Infe_appl_err :
    forall m n tf ta : term, inf_error (App m n) (Apply_err m tf n ta)
  (* This is an error about left part of product not being a type *)
  | Infe_type_prod_l :
    forall (m n : term) t, inf_error (Prod m n) (Not_a_type m t)
  (* This is an error about right aprt of product not being a type *)
  | Infe_type_prod_r :
    forall (m n : term) t,
    inf_error (Prod m n) (Under m (Not_a_type n t))
  (* New terms! *)
  | Infe_nat_succ :
    forall t T, inf_error (NatSucc t) (NatSucc_err t T)
  | Infe_nat_destruct_choice :
    forall choice on_zero on_succ num T, inf_error (NatDestruct choice on_zero on_succ num) (NatDestruct_Choice_err choice T) 
  | Infe_nat_destruct_on_zero :
    forall choice on_zero on_succ num T, inf_error (NatDestruct choice on_zero on_succ num) (NatDestruct_OnZero_err choice on_zero T) 
  | Infe_nat_destruct_on_succ :
    forall choice on_zero on_succ num T, inf_error (NatDestruct choice on_zero on_succ num) (NatDestruct_OnSucc_err choice on_succ T) 
  | Infe_nat_destruct_num :
    forall choice on_zero on_succ num T, inf_error (NatDestruct choice on_zero on_succ num) (NatDestruct_Num_err num T) 
  | Infe_nat_cases_choice :
    forall choice on_zero on_succ num T, inf_error (NatCases choice on_zero on_succ num) (NatCases_Choice_err choice T) 
  | Infe_nat_cases_on_zero :
    forall choice on_zero on_succ num T, inf_error (NatCases choice on_zero on_succ num) (NatCases_OnZero_err choice on_zero T) 
  | Infe_nat_cases_on_succ :
    forall choice on_zero on_succ num T, inf_error (NatCases choice on_zero on_succ num) (NatCases_OnSucc_err choice on_succ T) 
  | Infe_nat_cases_num :
    forall choice on_zero on_succ num T, inf_error (NatCases choice on_zero on_succ num) (NatCases_Num_err num T) 
  .

  Hint Resolve Infe_kind Infe_db Infe_lam_kind Infe_type_abs Infe_fun
    Infe_appl_err Infe_type_prod_l Infe_type_prod_r: coc.

  (* If an error happened, there's no way the term is typable *)
  Lemma inf_error_no_type :
    forall (m : term) (err : type_error),
    inf_error m err -> forall e, expln e err -> forall t, ~ typ e m t.
  Proof.
    simple induction 1; intros.
    inversion_clear H0; red in |- *; intros.
    apply inv_typ_abs with e m0 n0 t; intros; auto with coc arith.
    elim H2 with e (Srt s1); auto with coc arith.

    apply inv_typ_app with e m0 v t; intros; auto with coc arith.
    elim H2 with e (Prod V Ur); auto with coc arith.

    apply inv_typ_app with e u m0 t; intros; auto with coc arith.
    elim H2 with e V; auto with coc arith.

    apply inv_typ_prod with e m0 n0 t; intros; auto with coc arith.
    elim H2 with e (Srt s1); auto with coc arith.

    apply inv_typ_nat_destruct with e m0 a2 a3 a4 t; intros; auto with coc arith.
    elim H2 with e Tx1; auto with coc arith.

    apply inv_typ_nat_destruct with e a1 m0 a3 a4 t; intros; auto with coc arith.
    elim H2 with e Tx2; auto with coc arith.

    apply inv_typ_nat_destruct with e a1 a2 m0 a4 t; intros; auto with coc arith.
    elim H2 with e Tx3; auto with coc arith.

    apply inv_typ_nat_destruct with e a1 a2 a3 m0 t; intros; auto with coc arith.
    elim H2 with e Tx4; auto with coc arith.

    apply inv_typ_nat_cases with e m0 a2 a3 a4 t; intros; auto with coc arith.
    elim H2 with e Tx1; auto with coc arith.

    apply inv_typ_nat_cases with e a1 m0 a3 a4 t; intros; auto with coc arith.
    elim H2 with e Tx2; auto with coc arith.

    apply inv_typ_nat_cases with e a1 a2 m0 a4 t; intros; auto with coc arith.
    elim H2 with e Tx3; auto with coc arith.

    apply inv_typ_nat_cases with e a1 a2 a3 m0 t; intros; auto with coc arith.
    elim H2 with e Tx4; auto with coc arith.

    apply inv_typ_nat_succ with e m0 t; intros; auto with coc arith.
    elim H2 with e Tx; auto with coc arith.

    inversion_clear H3.
    inversion_clear H0; red in |- *; intros.
    apply inv_typ_abs with e T m0 t; intros; auto with coc arith.
    elim H2 with (T :: e) T0; auto with coc arith.

    apply inv_typ_prod with e T m0 t; intros; auto with coc arith.
    elim H2 with (T :: e) (Srt s2); auto with coc arith.

    inversion_clear H0; auto with coc arith.

    red in |- *; intros.
    apply inv_typ_ref with e t n; intros; auto with coc arith.
    inversion_clear H0.
    generalize H5.
    elim H2; simpl in |- *; intros; auto with coc arith.
    inversion_clear H0.

    inversion_clear H0.
    red in |- *; intros.
    apply inv_typ_abs with e T M t; intros; auto with coc arith.
    elim inv_typ_conv_kind with (T :: e) T0 (Srt s2); auto with coc arith.
    apply typ_unique with (T :: e) M; auto with coc arith.

    inversion_clear H0.
    red in |- *; intros.
    apply inv_typ_abs with e m0 n t0; intros; auto with coc arith.
    elim H2 with s1; auto with coc arith.

    inversion_clear H0.
    red in |- *; intros.
    apply inv_typ_app with e m0 n t0; intros; auto with coc arith.
    elim H2 with V Ur; auto with coc arith.

    inversion_clear H0.
    red in |- *; intros.
    apply inv_typ_app with e m0 n t; intros; auto with coc arith.
    elim type_case with e m0 (Prod a b); intros; auto with coc arith.
    inversion_clear H7.
    apply inv_typ_prod with e a b (Srt x); intros; auto with coc arith.
    apply H3.
    apply type_conv with V s1; auto with coc arith.
    apply inv_conv_prod_l with Ur b.
    apply typ_unique with e m0; auto with coc arith.

    discriminate H7.

    inversion_clear H0.
    red in |- *; intros.
    apply inv_typ_prod with e m0 n t0; intros; auto with coc arith.
    elim H2 with s1; auto with coc arith.

    inversion_clear H0.
    inversion_clear H1.
    red in |- *; intros.
    apply inv_typ_prod with e m0 n t0; intros; auto with coc arith.
    elim H2 with s2; auto with coc arith.

    inversion_clear H0.
    intro F.
    apply inv_typ_nat_succ with e t t0; auto with coc core; intros.
    apply type_conv with e t Tx Nat set in H0; auto with coc core.
    apply type_nat; eapply typ_wf; eauto.

    inversion_clear H0.
    intro F.
    apply inv_typ_nat_destruct with e choice on_zero on_succ num t; auto with coc core; intros.
    apply type_conv with e choice Tx1 (Prod Nat (Srt set)) kind in H0; auto with coc core.
    apply type_prod with set; auto with coc core.
    apply type_nat; eapply typ_wf; eauto.
    apply type_set; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.

    inversion_clear H0.
    intro F.
    apply inv_typ_nat_destruct with e choice on_zero on_succ num t; auto with coc core; intros.
    apply type_conv with e on_zero Tx2 (App choice NatO) set in H3; auto with coc core.
    change (Srt set) with (subst NatO (Srt set)).
    apply type_app with Nat.
    apply type_nat_o; eapply typ_wf; eauto.
    apply type_conv with Tx1 kind; auto with coc core.
    apply type_prod with set; auto with coc core.
    apply type_nat; eapply typ_wf; eauto.
    apply type_set; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.

    inversion_clear H0.
    intro F.
    apply inv_typ_nat_destruct with e choice on_zero on_succ num t; auto with coc core; intros.
    apply type_conv with e on_succ Tx3 (Prod Nat (App (lift 1 choice) (NatSucc (Ref 0)))) set in H4; auto with coc core.
    apply type_prod with set.
    apply type_nat; eapply typ_wf; eauto.
    change (Srt set) with (subst (NatSucc (Ref 0)) (Srt set)).
    apply type_app with Nat.
    apply type_nat_succ; apply type_var.
    apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
    exists Nat; auto with coc core.
    change (Prod Nat (Srt set)) with (lift 1 (Prod Nat (Srt set))).
    apply thinning; auto with coc core.
    apply type_conv with e choice Tx1 (Prod Nat (Srt set)) kind in H0; auto with coc core.
    apply type_prod with set.
    apply type_nat; eapply typ_wf; eauto.
    apply type_set; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
    apply wf_var with set; apply type_nat; eapply typ_wf; eauto.

    inversion_clear H0.
    intro F.
    apply inv_typ_nat_destruct with e choice on_zero on_succ num t; auto with coc core; intros.
    apply type_conv with e num Tx4 Nat set in H5; auto with coc core.
    apply type_nat; eapply typ_wf; eauto.
    
    

    
    inversion_clear H0.
    intro F.
    apply inv_typ_nat_cases with e choice on_zero on_succ num t; auto with coc core; intros.
    apply type_conv with e choice Tx1 (Prod Nat (Srt prop)) kind in H0; auto with coc core.
    apply type_prod with set; auto with coc core.
    apply type_nat; eapply typ_wf; eauto.
    apply type_prop; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.

    inversion_clear H0.
    intro F.
    apply inv_typ_nat_cases with e choice on_zero on_succ num t; auto with coc core; intros.
    apply type_conv with e on_zero Tx2 (App choice NatO) prop in H3; auto with coc core.
    change (Srt prop) with (subst NatO (Srt prop)).
    apply type_app with Nat.
    apply type_nat_o; eapply typ_wf; eauto.
    apply type_conv with Tx1 kind; auto with coc core.
    apply type_prod with set; auto with coc core.
    apply type_nat; eapply typ_wf; eauto.
    apply type_prop; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.

    inversion_clear H0.
    intro F.
    apply inv_typ_nat_cases with e choice on_zero on_succ num t; auto with coc core; intros.
    apply type_conv with e on_succ Tx3 (Prod Nat (App (lift 1 choice) (NatSucc (Ref 0)))) prop in H4; auto with coc core.
    apply type_prod with set.
    apply type_nat; eapply typ_wf; eauto.
    change (Srt prop) with (subst (NatSucc (Ref 0)) (Srt prop)).
    apply type_app with Nat.
    apply type_nat_succ; apply type_var.
    apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
    exists Nat; auto with coc core.
    change (Prod Nat (Srt prop)) with (lift 1 (Prod Nat (Srt prop))).
    apply thinning; auto with coc core.
    apply type_conv with e choice Tx1 (Prod Nat (Srt prop)) kind in H0; auto with coc core.
    apply type_prod with set.
    apply type_nat; eapply typ_wf; eauto.
    apply type_prop; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
    apply wf_var with set; apply type_nat; eapply typ_wf; eauto.

    inversion_clear H0.
    intro F.
    apply inv_typ_nat_cases with e choice on_zero on_succ num t; auto with coc core; intros.
    apply type_conv with e num Tx4 Nat set in H5; auto with coc core.
    apply type_nat; eapply typ_wf; eauto.
  Qed.
*)

  (* The inference of type is decidable *)
  Definition infer :
   forall e t,
   wf e ->
   {T : term | typ e t T} +
   {forall T : term, ~ typ e t T}.
  Proof.
    do 2 intro.
    generalize t e.
    clear e t.

    simple induction t.

    (*sorts*)
    intros.
    case s.
    (*type of kind*)
    right.
    apply inv_typ_kind.
    (*type of prop*)
    left.
    exists (Srt kind).
    apply type_prop; auto with coc arith.
    (*type of set*)
    left.
    exists (Srt kind).
    apply type_set; auto with coc arith.

    (*var*)
    intros.
    generalize (list_item term e n); 
    intros [(T, H0)| b].
    (*okay*)
    left.
    exists (lift (S n) T).
    apply type_var; auto with coc arith.
    exists T; auto with coc arith.
    (*failed to fetch from env*)
    right.
    intros T H0.
    apply inv_typ_ref with e T n; auto with coc core arith datatypes.
    intros.
    elim b with U; trivial.

    (*Abs*)
    intros a Ha b Hb e H.
    elim Ha with e; trivial with coc arith.
    intros (T, ty_a).
    elim (red_to_sort T); trivial with coc arith.
    intros (s, srt_T).
    cut (wf (a :: e)); intros.
    elim Hb with (a :: e); trivial with coc arith.
    intros (B, ty_b).
    elim (eqterm (Srt kind) B).
    intro eq_kind.
    (*failure*)
    right.
    intros T0 H1.
    subst B.
    apply inv_typ_abs with e a b T0; auto with coc arith.
    intros.
    
(*)
      (*good*)
      intro not_kind.
      left.
      exists (Prod t1 B).
      elim type_case with (1 := ty_b).
      intros (s2, knd_b).
      apply type_abs with s s2; auto with coc arith.
      apply type_reduction with T; auto with coc arith.
      intros; elim not_kind; auto.
      intros (err, expl_err, inf_err).
      right.
      exists (Under t1 err); auto with coc arith.
      apply Infe_under with t2; auto with coc arith.
      apply wf_var with s.
      apply type_reduction with T; auto with coc arith.
      intro not_type.
      right.
      exists (Not_a_type t1 T); auto with coc arith.
      apply Exp_type; auto with coc arith.
      red in |- *; intros.
      elim not_type with s.
      apply typ_unique with a t1; auto with coc arith.
      apply type_sn with a t1; auto with coc arith.
      intros (err, expl_err, inf_err).
      right.
      exists err; auto with coc arith.
      apply Infe_subt with t1; auto with coc arith.

    (*app*)
      intros e w.
      elim IHt1 with e; trivial with coc arith.
      intros (T, ty_u).
      elim red_to_prod with T.
      intros ((V, Ur), red_prod).
      cut (typ e t1 (Prod V Ur)); intros.
      elim IHt2 with e; trivial with coc arith.
      intros (B, ty_v).
      elim is_conv with V B.
      intros domain_conv.

      left.
      exists (subst t2 Ur).
      apply type_app with V; auto with coc arith.
      elim type_case with e t1 (Prod V Ur); auto with coc arith.
      intros (s, ty_prod).
      apply inv_typ_prod with (1 := ty_prod); auto with coc arith; intros.
      apply type_conv with B s1; auto with coc arith.

      intro not_prod; discriminate not_prod.

      intro dom_not_conv.
      right.
      exists (Apply_err t1 (Prod V Ur) t2 B); auto with coc arith.
      apply Exp_appl_err; auto with coc arith.
      red in |- *; intros.
      apply dom_not_conv.
      apply typ_unique with e t2; auto with coc arith.

      apply subterm_sn with (Prod V Ur); auto with coc arith.
      apply sn_red_sn with T; auto with coc arith.
      apply type_sn with e t1; auto with coc arith.

      apply type_sn with e t2; auto with coc arith.

      intros (err, expl_err, inf_err).
      right.
      exists err; auto with coc arith.
      apply Infe_subt with t2; auto with coc arith.

      apply type_reduction with T; auto with coc arith.

      intros not_prod.
      right.
      exists (Not_a_fun t1 T); auto with coc arith.
      apply Exp_fun; auto with coc arith.
      red in |- *; intros.
      elim not_prod with a b.
      apply typ_unique with e t1; auto with coc arith.
      apply type_sn with e t1; auto with coc arith.

      intros (err, expl_err, inf_err).
      right.
      exists err; auto with coc arith.
      apply Infe_subt with t1; auto with coc arith.
      intros e w.
      elim IHt1 with e; trivial with coc arith.
      intros (T, ty_a).
      elim red_to_sort with T.
      intros (s, red_sort).
      cut (wf (t1 :: e)); intros.
      elim IHt2 with (t1 :: e); trivial with coc arith.
      intros (B, ty_b).
      elim red_to_sort with B.
      intros (s2, red_s2).
      left.
      exists (Srt s2).
      apply type_prod with s; auto with coc arith.
      apply type_reduction with T; auto with coc arith.
      apply type_reduction with B; auto with coc arith.

      intros b_not_type.
      right.
      exists (Under t1 (Not_a_type t2 B)); auto with coc arith.
      apply Exp_under; auto with coc arith.
      apply Exp_type; auto with coc arith.
      red in |- *; intros.
      elim b_not_type with s0.
      apply typ_unique with (t1 :: e) t2; auto with coc arith.
      apply type_sn with (t1 :: e) t2; auto with coc arith.

      intros (err, expl_err, inf_err).
      right.
      exists (Under t1 err); auto with coc arith.
      apply Infe_under with t2; auto with coc arith.
      apply wf_var with s.
      apply type_reduction with T; auto with coc arith.

      intros a_not_type.
      right.
      exists (Not_a_type t1 T); auto with coc arith.
      apply Exp_type; auto with coc arith.
      red in |- *; intros.
      elim a_not_type with s.
      apply typ_unique with e t1; auto with coc arith.
      apply type_sn with e t1; auto with coc arith.
      intros (err, expl_err, inf_err).
      right.
      exists err; auto with coc arith.
      apply Infe_subt with t1; auto with coc arith.

    (* nat *)
      intros; left; exists (Srt set); apply type_nat; auto with coc arith.

    (* nat o *)
      intros; left; exists Nat; apply type_nat_o; auto with coc arith.

    (* nat succ *)
      intros.
      elim IHt with e; intros; auto with coc arith.
      elim a; intros.
      elim is_conv with Nat x; intros.
      left; exists Nat; apply type_nat_succ; apply type_conv with e t x Nat set in p; auto with coc core.
      apply type_nat; eapply typ_wf; eauto.
      right.
      exists (NatSucc_err t x).
      apply Exp_nat_succ; intros; auto with coc core.
      intro F.
      apply b.
      apply typ_unique with e t; auto with coc core.
      apply Infe_nat_succ.
      apply str_norm with e (Srt set); apply type_nat; eapply typ_wf; eauto.
      apply type_sn with e t; auto with coc core.
      elim b; intros.
      right.
      exists x; auto with coc core.
      apply Infe_subt with t; auto with coc core.

    (* nat destruct *)
      intros.
      elim IHt1 with e; auto with coc core; intros.
      elim IHt2 with e; auto with coc core; intros.
      elim IHt3 with e; auto with coc core; intros.
      elim IHt4 with e; auto with coc core; intros.
      elim a2; elim a1; elim a0; elim a; intros.
      elim (is_conv x (Prod Nat (Srt set))); intros.
      elim (is_conv x0 (App t1 NatO)); intros.
      elim (is_conv x1 (Prod Nat (App (lift 1 t1) (NatSucc (Ref 0))))); intros.
      elim (is_conv x2 Nat); intros.
      eapply type_conv with _ _ _ _ kind in p; eauto.
      eapply type_conv with _ _ _ _ set in p0; eauto.
      eapply type_conv with _ _ _ _ set in p1; eauto.
      eapply type_conv with _ _ _ _ set in p2; eauto.
      left; exists (App t1 t4); apply type_nat_destruct; auto with coc core.
      apply type_nat; eapply typ_wf; eauto.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      change (Srt set) with (subst (NatSucc (Ref 0)) (Srt set)).
      apply type_app with Nat.
      apply type_nat_succ; apply type_var.
      apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      exists Nat; auto with coc core.
      change (Prod Nat (Srt set)) with (lift 1 (Prod Nat (Srt set))); apply thinning; auto with coc core.
      apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      change (Srt set) with (subst NatO (Srt set)); apply type_app with Nat; auto with coc core.
      apply type_nat_o; eapply typ_wf; eauto.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      apply type_set; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      right; exists (NatDestruct_Num_err t4 x2).
      apply Exp_nat_destruct_num; auto with coc core.
      intro F; apply b; eapply typ_unique with e t4; auto with coc core.
      apply Infe_nat_destruct_num.
      exact (type_sn _ _ _ p2).
      apply (str_norm e Nat (Srt set)).
      apply type_nat; eapply typ_wf; eauto.
      right; exists (NatDestruct_OnSucc_err t1 t3 x1).
      apply Exp_nat_destruct_on_succ; auto with coc core.
      intro F; apply b; eapply typ_unique with e t3; auto with coc core.
      apply Infe_nat_destruct_on_succ; auto with coc core.
      exact (type_sn _ _ _ p1).
      cut (typ e (Prod Nat (App (lift 1 t1) (NatSucc (Ref 0)))) (Srt set)).
      apply str_norm.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      change (Srt set) with (subst (NatSucc (Ref 0)) (Srt set)).
      apply type_app with Nat.
      apply type_nat_succ; apply type_var.
      apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      exists Nat; auto with coc core.
      change (Prod Nat (Srt set)) with (lift 1 (Prod Nat (Srt set))); apply thinning; auto with coc core.
      apply type_conv with x kind; auto with coc core.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      apply type_set; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      right; exists (NatDestruct_OnZero_err t1 t2 x0); auto with coc core.
      apply Exp_nat_destruct_on_zero; auto with coc core.
      intro F; apply b; eapply typ_unique with e t2; auto with coc core.
      apply Infe_nat_destruct_on_zero; auto with coc core.
      exact (type_sn _ _ _ p0).
      cut (typ e (App t1 NatO) (Srt set)).
      apply str_norm.
      change (Srt set) with (subst NatO (Srt set)); apply type_app with Nat.
      apply type_nat_o; eapply typ_wf; eauto.
      apply type_conv with x kind; auto with coc core.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      apply type_set; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      right; exists (NatDestruct_Choice_err t1 x); auto with coc core.
      apply Exp_nat_destruct_choice; auto with coc core.
      intro F; apply b; eapply typ_unique with e t1; auto with coc core.
      apply Infe_nat_destruct_choice; auto with coc core.
      exact (type_sn _ _ _ p).
      cut (typ e (Prod Nat (Srt set)) (Srt kind)).
      apply str_norm.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      apply type_set; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      elim b; intros.
      right; exists x; auto with coc core.
      apply Infe_subt with t4; auto with coc core.
      elim b; intros.
      right; exists x; auto with coc core.
      apply Infe_subt with t3; auto with coc core.
      elim b; intros.
      right; exists x; auto with coc core.
      apply Infe_subt with t2; auto with coc core.
      elim b; intros.
      right; exists x; auto with coc core.
      apply Infe_subt with t1; auto with coc core.

    (* nat cases *)
      intros.
      elim IHt1 with e; auto with coc core; intros.
      elim IHt2 with e; auto with coc core; intros.
      elim IHt3 with e; auto with coc core; intros.
      elim IHt4 with e; auto with coc core; intros.
      elim a2; elim a1; elim a0; elim a; intros.
      elim (is_conv x (Prod Nat (Srt prop))); intros.
      elim (is_conv x0 (App t1 NatO)); intros.
      elim (is_conv x1 (Prod Nat (App (lift 1 t1) (NatSucc (Ref 0))))); intros.
      elim (is_conv x2 Nat); intros.
      eapply type_conv with _ _ _ _ kind in p; eauto.
      eapply type_conv with _ _ _ _ prop in p0; eauto.
      eapply type_conv with _ _ _ _ prop in p1; eauto.
      eapply type_conv with _ _ _ _ set in p2; eauto.
      left; exists (App t1 t4); apply type_nat_cases; auto with coc core.
      apply type_nat; eapply typ_wf; eauto.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      change (Srt prop) with (subst (NatSucc (Ref 0)) (Srt prop)).
      apply type_app with Nat.
      apply type_nat_succ; apply type_var.
      apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      exists Nat; auto with coc core.
      change (Prod Nat (Srt prop)) with (lift 1 (Prod Nat (Srt prop))); apply thinning; auto with coc core.
      apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      change (Srt prop) with (subst NatO (Srt prop)); apply type_app with Nat; auto with coc core.
      apply type_nat_o; eapply typ_wf; eauto.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      apply type_prop; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      right; exists (NatCases_Num_err t4 x2).
      apply Exp_nat_cases_num; auto with coc core.
      intro F; apply b; eapply typ_unique with e t4; auto with coc core.
      apply Infe_nat_cases_num.
      exact (type_sn _ _ _ p2).
      apply (str_norm e Nat (Srt set)).
      apply type_nat; eapply typ_wf; eauto.
      right; exists (NatCases_OnSucc_err t1 t3 x1).
      apply Exp_nat_cases_on_succ; auto with coc core.
      intro F; apply b; eapply typ_unique with e t3; auto with coc core.
      apply Infe_nat_cases_on_succ; auto with coc core.
      exact (type_sn _ _ _ p1).
      cut (typ e (Prod Nat (App (lift 1 t1) (NatSucc (Ref 0)))) (Srt prop)).
      apply str_norm.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      change (Srt prop) with (subst (NatSucc (Ref 0)) (Srt prop)).
      apply type_app with Nat.
      apply type_nat_succ; apply type_var.
      apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      exists Nat; auto with coc core.
      change (Prod Nat (Srt prop)) with (lift 1 (Prod Nat (Srt prop))); apply thinning; auto with coc core.
      apply type_conv with x kind; auto with coc core.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      apply type_prop; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      right; exists (NatCases_OnZero_err t1 t2 x0); auto with coc core.
      apply Exp_nat_cases_on_zero; auto with coc core.
      intro F; apply b; eapply typ_unique with e t2; auto with coc core.
      apply Infe_nat_cases_on_zero; auto with coc core.
      exact (type_sn _ _ _ p0).
      cut (typ e (App t1 NatO) (Srt prop)).
      apply str_norm.
      change (Srt prop) with (subst NatO (Srt prop)); apply type_app with Nat.
      apply type_nat_o; eapply typ_wf; eauto.
      apply type_conv with x kind; auto with coc core.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      apply type_prop; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      right; exists (NatCases_Choice_err t1 x); auto with coc core.
      apply Exp_nat_cases_choice; auto with coc core.
      intro F; apply b; eapply typ_unique with e t1; auto with coc core.
      apply Infe_nat_cases_choice; auto with coc core.
      exact (type_sn _ _ _ p).
      cut (typ e (Prod Nat (Srt prop)) (Srt kind)).
      apply str_norm.
      apply type_prod with set.
      apply type_nat; eapply typ_wf; eauto.
      apply type_prop; apply wf_var with set; apply type_nat; eapply typ_wf; eauto.
      elim b; intros.
      right; exists x; auto with coc core.
      apply Infe_subt with t4; auto with coc core.
      elim b; intros.
      right; exists x; auto with coc core.
      apply Infe_subt with t3; auto with coc core.
      elim b; intros.
      right; exists x; auto with coc core.
      apply Infe_subt with t2; auto with coc core.
      elim b; intros.
      right; exists x; auto with coc core.
      apply Infe_subt with t1; auto with coc core.
  Defined.
*)
(*)
  Inductive chk_error (m : term) t : type_error -> Prop :=
  | Chke_subj :
    forall err : type_error, inf_error m err -> chk_error m t err
  | Chke_type :
    forall err : type_error,
    inf_error t err -> t <> Srt kind -> chk_error m t err
  | Chke_exp : forall at_ : term, chk_error m t (Expected_type m at_ t)
  .

  Hint Resolve Chke_subj Chke_type Chke_exp: coc.
*)
(*)
  Lemma chk_error_no_type :
   forall e (m : term) t (err : type_error),
   chk_error m t err -> expln e err -> ~ typ e m t.
  Proof.
    simple destruct 1; intros.
    apply inf_error_no_type with err0; auto with coc arith.

    red in |- *; intros.
    elim type_case with e m t; intros; auto with coc arith.
    inversion_clear H4.
    elim inf_error_no_type with t err0 e (Srt x); auto with coc arith.

    inversion_clear H0; auto with coc arith.
  Qed.


  Definition check_typ :
   forall e t (tp : term),
   wf e ->
   {err : type_error | expln e err &  chk_error t tp err} + {typ e t tp}.
  Proof.
    intros.
    elim infer with e t; auto with coc arith.
    intros (tp', typ_t).
    elim eqterm with (Srt kind) tp.
    intros cast_kind.
    elim eqterm with (Srt kind) tp'.
    intros inf_kind.
    right.
    elim cast_kind; rewrite inf_kind; trivial.

    intros inf_not_kind.
    left.
    exists (Expected_type t tp' tp); auto with coc.
    apply Exp_exp_type; auto with coc arith.
    red in |- *; intros; apply inf_not_kind.
    symmetry  in |- *.
    apply type_kind_not_conv with e t; auto with coc arith.
    rewrite cast_kind; trivial.

    elim cast_kind; auto with coc.

    intros cast_not_kind.
    elim infer with e tp; auto with coc.
    intros (k, ty_tp).
    elim is_conv with tp tp'.
    intros cast_ok.
    right.
    elim red_to_sort with k; auto with coc.
    intros (s, red_sort).
    apply type_conv with tp' s; auto with coc.
    apply type_reduction with k; auto with coc.

    intros not_sort.
    elim type_case with (1 := typ_t).
    intros (s, kind_inf).
    elim not_sort with s.
    apply typ_conv_conv with e tp tp'; auto with coc arith.

    intros is_kind.
    elim inv_typ_conv_kind with e tp k; auto with coc arith.
    elim is_kind; auto with coc arith.

    apply type_sn with e tp; auto with coc arith.

    intros cast_err.
    left.
    exists (Expected_type t tp' tp); auto with coc arith.
    apply Exp_exp_type; auto with coc arith.
    red in |- *; intros; apply cast_err; apply typ_unique with e t;
    auto with coc arith.

    apply typ_free_db with k; auto with coc arith.

    apply str_norm with e k; auto with coc arith.

    apply type_sn with e t; auto with coc arith.

    intros (err, expl_err, inf_err).
    left.
    exists err; auto with coc arith.

    intros (err, expl_err, inf_err).
    left.
    exists err; auto with coc arith.
  Defined.

  Inductive decl_error (m : term) : type_error -> Prop :=
    | Decax_ill :
        forall err : type_error, inf_error m err -> decl_error m err
    | Decax_type : forall t, decl_error m (Not_a_type m t).

  Hint Resolve Decax_ill Decax_type: coc.


  Lemma decl_err_not_wf :
   forall e t (err : type_error),
   decl_error t err -> expln e err -> ~ wf (t :: e).
  Proof.
    red in |- *.
    simple destruct 1; intros.
    inversion_clear H2.
    elim inf_error_no_type with t err0 e (Srt s); auto with coc arith.

    inversion_clear H0.
    inversion_clear H1.
    elim H3 with s; auto with coc arith.
  Qed.


  Definition add_typ :
   forall e t,
   wf e ->
   {err : type_error | expln e err &  decl_error t err} + {wf (t :: e)}.
  Proof.
    intros.
    elim infer with e t; auto with coc.
    intros (T, typ_t).
    elim red_to_sort with T.
    intros (s, red_sort).
    right.
    apply wf_var with s.
    apply type_reduction with T; auto with coc.

    intros not_sort.
    left.
    exists (Not_a_type t T); auto with coc.
    apply Exp_type; auto with coc.
    red in |- *; intros.
    elim not_sort with s.
    apply typ_unique with e t; auto with coc.

    apply type_sn with e t; auto with coc.

    intros (err, expl_err, inf_err).
    left.
    exists err; auto with coc arith.
  Defined.


End TypeChecker.

Section Decidabilite_typage.

  Lemma decide_wf : forall e, {wf e} + {~ wf e}.
  Proof.
    simple induction e; intros.
    left.
    apply wf_nil.

    elim H.
    intros wf_l.
    elim add_typ with l a; trivial.
    intros (err, expl_err, decl_err).
    right.
    apply decl_err_not_wf with (1 := decl_err) (2 := expl_err).

    left; trivial.

    intros not_wf_l.
    right; red in |- *; intros.
    apply not_wf_l.
    inversion_clear H0.
    apply typ_wf with (1 := H1).
  Qed.


  Lemma decide_typ : forall e t (tp : term), {typ e t tp} + {~ typ e t tp}.
  Proof.
    intros.
    elim decide_wf with e.
    intros wf_e.
    elim check_typ with e t tp; trivial.
    intros (err, expl_err, chk_err).
    right.
    apply chk_error_no_type with (1 := chk_err) (2 := expl_err).

    left; trivial.

    intros not_wf_e.
    right; red in |- *; intros.
    apply not_wf_e.
    apply typ_wf with (1 := H).
  Qed.

End Decidabilite_typage.
*)