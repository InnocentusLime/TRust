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
  Here we define the external terms. The ones which carry strings around
  we then will provide a mapping from internal terms to external terms and
  show how typing and reduction is preserved. 
*)

Require Import MyList.
Require Import Termes.
Require Export Names.

(* The definition *)
Inductive expr : Set :=
| SRT : sort -> expr
| REF : name -> expr
| ABS : name -> expr -> expr -> expr
| APP : expr -> expr -> expr
| PROD : name -> expr -> expr -> expr
(* New terms *)
| NAT : expr
| NAT_O : expr
| NAT_SUCC : expr -> expr
| NAT_DESTRUCT : expr -> expr -> expr -> expr -> expr
| NAT_CASES : expr -> expr -> expr -> expr -> expr
.

(* Var occurance predicate *)
Inductive expr_vars (x : name) : expr -> Prop :=
| ev_ref : expr_vars x (REF x)
| ev_abs_l :
  forall (y : name) (T M : expr),
  expr_vars x T -> expr_vars x (ABS y T M)
| ev_abs_r :
  forall (y : name) (T M : expr),
  x <> y -> expr_vars x M -> expr_vars x (ABS y T M)
| ev_app_l : forall u v : expr, expr_vars x u -> expr_vars x (APP u v)
| ev_app_r : forall u v : expr, expr_vars x v -> expr_vars x (APP u v)
| ev_prod_l :
  forall (y : name) (T U : expr),
  expr_vars x T -> expr_vars x (PROD y T U)
| ev_prod_r :
  forall (y : name) (T U : expr),
  x <> y -> expr_vars x U -> expr_vars x (PROD y T U)
(* New terms *)
| ev_nat_succ : 
  forall (M : expr),
  expr_vars x M -> expr_vars x (NAT_SUCC M)
| ev_nat_destruct_choice :
  forall (choice on_zero on_succ num : expr),
  expr_vars x choice ->
  expr_vars x (NAT_DESTRUCT choice on_zero on_succ num)
| ev_nat_destruct_on_zero :
  forall (choice on_zero on_succ num : expr),
  expr_vars x on_zero ->
  expr_vars x (NAT_DESTRUCT choice on_zero on_succ num)
| ev_nat_destruct_on_succ :
  forall (choice on_zero on_succ num : expr),
  expr_vars x on_succ ->
  expr_vars x (NAT_DESTRUCT choice on_zero on_succ num)
| ev_nat_destruct_num :
  forall (choice on_zero on_succ num : expr),
  expr_vars x num ->
  expr_vars x (NAT_DESTRUCT choice on_zero on_succ num)
| ev_nat_cases_choice :
  forall (choice on_zero on_succ num : expr),
  expr_vars x choice ->
  expr_vars x (NAT_CASES choice on_zero on_succ num)
| ev_nat_cases_on_zero :
  forall (choice on_zero on_succ num : expr),
  expr_vars x on_zero ->
  expr_vars x (NAT_CASES choice on_zero on_succ num)
| ev_nat_cases_on_succ :
  forall (choice on_zero on_succ num : expr),
  expr_vars x on_succ ->
  expr_vars x (NAT_CASES choice on_zero on_succ num)
| ev_nat_cases_num :
  forall (choice on_zero on_succ num : expr),
  expr_vars x num ->
  expr_vars x (NAT_CASES choice on_zero on_succ num)
.

  Hint Resolve ev_ref ev_abs_l ev_abs_r ev_app_l ev_app_r ev_prod_l
    ev_prod_r ev_nat_succ ev_nat_destruct_choice ev_nat_destruct_on_zero
    ev_nat_destruct_on_succ ev_nat_destruct_num ev_nat_cases_choice
    ev_nat_cases_on_zero ev_nat_cases_on_succ ev_nat_cases_num
  : coc.

(* Checking freedom of a var is decidable *)
Definition is_free_var : forall (x : name) (e : expr), 
  {expr_vars x e} + {~ expr_vars x e}
.
Proof.
  simple induction e.
  right; red in |- *; intros; inversion H.

  intro y; case (name_dec x y); intros; [ left | right ].
  rewrite e0; auto with coc.
  red in |- *; intros A; inversion A; auto.
                      
  intros y t H u H1.
  elim H; intros;
  [ idtac | elim (name_dec x y); intros; [ idtac | elim H1; intros ] ];
  auto with coc; right; red in |- *; intros A; inversion A; 
  auto.

  intros u H v H1.
  elim H; intros; [ idtac | elim H1; intros ]; auto with coc; right;
  red in |- *; intros A; inversion A; auto.

  intros y t H u H1.
  elim H; intros;
  [ idtac | elim (name_dec x y); intros; [ idtac | elim H1; intros ] ];
  auto with coc; right; red in |- *; intros A; inversion A; 
  auto.

  right; red in |- *; intros; inversion H.

  right; red in |- *; intros; inversion H.

  intros e0 H; elim H; intros.
  left; auto with coc core.
  right; auto with coc core.
  intro H0; inversion_clear H0; auto with coc core.

  intros.
  destruct H; try (left; solve [auto with coc core]).
  destruct H0; try (left; solve [auto with coc core]).
  destruct H1; try (left; solve [auto with coc core]).
  destruct H2; try (left; solve [auto with coc core]).
  right; intro H3; inversion_clear H3; auto with coc core.

  intros.
  destruct H; try (left; solve [auto with coc core]).
  destruct H0; try (left; solve [auto with coc core]).
  destruct H1; try (left; solve [auto with coc core]).
  destruct H2; try (left; solve [auto with coc core]).
  right; intro H3; inversion_clear H3; auto with coc core.
Defined.


(* Translation of two naming contexts *)
Inductive transl_name : list name -> name -> list name -> name -> Prop :=
| tr_nil : forall x : name, transl_name nil x nil x
| tr_hd :
  forall (x y : name) (l1 l2 : list name),
  transl_name (x :: l1) x (y :: l2) y
| tr_tl :
  forall (x x0 y y0 : name) (l1 l2 : list name),
  x <> x0 ->
  y <> y0 ->
  transl_name l1 x l2 y -> 
  transl_name (x0 :: l1) x (y0 :: l2) y
.

(* Alpha equality *)
Inductive alpha : list name -> expr -> list name -> expr -> Prop :=
| alp_srt :
  forall (l1 l2 : list name) (s : sort), alpha l1 (SRT s) l2 (SRT s)
| alp_ref :
  forall (l1 l2 : list name) (x y : name),
  transl_name l1 x l2 y -> alpha l1 (REF x) l2 (REF y)
| alp_abs :
  forall (l1 l2 : list name) (x y : name) (A A' M M' : expr),
  alpha l1 A l2 A' ->
  alpha (x :: l1) M (y :: l2) M' ->
  alpha l1 (ABS x A M) l2 (ABS y A' M')
| alp_app :
  forall (l1 l2 : list name) (A A' M M' : expr),
  alpha l1 A l2 A' ->
  alpha l1 M l2 M' -> alpha l1 (APP A M) l2 (APP A' M')
| alp_prod :
  forall (l1 l2 : list name) (x y : name) (A A' M M' : expr),
  alpha l1 A l2 A' ->
  alpha (x :: l1) M (y :: l2) M' ->
  alpha l1 (PROD x A M) l2 (PROD y A' M')
(* New terms *)
| alp_nat : forall l1 l2, alpha l1 NAT l2 NAT
| alp_nat_o : forall l1 l2, alpha l1 NAT_O l2 NAT_O
| alp_nat_succ : 
  forall l1 l2 (M M' : expr),
  alpha l1 M l2 M' ->
  alpha l1 (NAT_SUCC M) l2 (NAT_SUCC M')
| alp_nat_destruct :
  forall l1 l2 (choice choice' on_zero on_zero' on_succ on_succ' num num' : expr),
  alpha l1 choice l2 choice' ->
  alpha l1 on_zero l2 on_zero' ->
  alpha l1 on_succ l2 on_succ' ->
  alpha l1 num l2 num' ->
  alpha l1 (NAT_DESTRUCT choice on_zero on_succ num) l2 (NAT_DESTRUCT choice' on_zero' on_succ' num')
| alp_nat_cases :
  forall l1 l2 (choice choice' on_zero on_zero' on_succ on_succ' num num' : expr),
  alpha l1 choice l2 choice' ->
  alpha l1 on_zero l2 on_zero' ->
  alpha l1 on_succ l2 on_succ' ->
  alpha l1 num l2 num' ->
  alpha l1 (NAT_CASES choice on_zero on_succ num) l2 (NAT_CASES choice' on_zero' on_succ' num')
.


(* conversion of `term` to `expr` *)
Inductive term_expr_equiv : prt_names -> term -> expr -> Prop :=
| eqv_srt :
  forall (l : prt_names) (s : sort), term_expr_equiv l (Srt s) (SRT s)
| eqv_ref :
  forall (l : prt_names) (x : name) (n : nat),
  first_item _ x l n -> term_expr_equiv l (Ref n) (REF x)
| eqv_abs :
  forall (l : prt_names) (A M : term) (B N : expr) (x : name),
  term_expr_equiv l A B ->
  term_expr_equiv (x :: l) M N ->
  term_expr_equiv l (Abs A M) (ABS x B N)
| eqv_app :
  forall (l : prt_names) (u v : term) (a b : expr),
  term_expr_equiv l u a ->
  term_expr_equiv l v b -> term_expr_equiv l (App u v) (APP a b)
| eqv_prod :
  forall (l : prt_names) (A M : term) (B N : expr) (x : name),
  term_expr_equiv l A B ->
  term_expr_equiv (x :: l) M N ->
  term_expr_equiv l (Prod A M) (PROD x B N)
(* New terms *)  
| eqv_nat : forall (l : prt_names), term_expr_equiv l Nat NAT
| eqv_nat_o : forall (l : prt_names), term_expr_equiv l NatO NAT_O
| eqv_nat_succ : 
  forall (l : prt_names) (x : term) (x' : expr),
  term_expr_equiv l x x' ->
  term_expr_equiv l (NatSucc x) (NAT_SUCC x')
| eqv_nat_destruct  :
  forall (l : prt_names) (choice on_zero on_succ num : term)
  (choice' on_zero' on_succ' num' : expr),
  term_expr_equiv l choice choice' ->
  term_expr_equiv l on_zero on_zero' ->
  term_expr_equiv l on_succ on_succ' ->
  term_expr_equiv l num num' ->
  term_expr_equiv l (NatDestruct choice on_zero on_succ num) (NAT_DESTRUCT choice' on_zero' on_succ' num')
| eqv_nat_cases  :
  forall (l : prt_names) (choice on_zero on_succ num : term)
  (choice' on_zero' on_succ' num' : expr),
  term_expr_equiv l choice choice' ->
  term_expr_equiv l on_zero on_zero' ->
  term_expr_equiv l on_succ on_succ' ->
  term_expr_equiv l num num' ->
  term_expr_equiv l (NatCases choice on_zero on_succ num) (NAT_CASES choice' on_zero' on_succ' num')
.

(* A trick to find `freed_db`ish variables *)
Lemma equiv_free_db :
  forall (l : prt_names) (t : term) (e : expr),
  term_expr_equiv l t e -> free_db (length l) t.
Proof.
  simple induction 1; simpl in |- *; intros; auto with coc core arith datatypes.
  apply db_ref.
  elim H0; simpl in |- *; auto with coc core arith datatypes.
Qed.

(* If two nameless terms convert into the same named term, they are equal *)
Lemma equiv_unique :
  forall (l : prt_names) (t : term) (e : expr), term_expr_equiv l t e -> 
  forall u : term, term_expr_equiv l u e -> t = u
.
Proof.
  simple induction 1; intros.
  inversion_clear H0; auto with coc core arith datatypes.

  inversion_clear H1.
  elim first_item_unique with name x l0 n n0;
  auto with coc core arith datatypes.

  inversion_clear H4.
  elim H1 with A0; auto with coc core arith datatypes.
  elim H3 with M0; auto with coc core arith datatypes.

  inversion_clear H4.
  elim H1 with u1; auto with coc core arith datatypes.
  elim H3 with v0; auto with coc core arith datatypes.

  inversion_clear H4.
  elim H1 with A0; auto with coc core arith datatypes.
  elim H3 with M0; auto with coc core arith datatypes.

  inversion_clear H0.
  auto with coc core.

  inversion_clear H0.
  auto with coc core.

  inversion_clear H2.
  elim H1 with x0; auto with coc core.

  inversion_clear H8.
  elim H1 with choice0; auto with coc core.
  elim H3 with on_zero0; auto with coc core.
  elim H5 with on_succ0; auto with coc core.
  elim H7 with num0; auto with coc core.

  inversion_clear H8.
  elim H1 with choice0; auto with coc core.
  elim H3 with on_zero0; auto with coc core.
  elim H5 with on_succ0; auto with coc core.
  elim H7 with num0; auto with coc core.
Qed.

(* All the named terms equivalent to the same nameless term are alpha equal *)
Lemma unique_alpha :
  forall (l1 : prt_names) (t : term) (e : expr), term_expr_equiv l1 t e ->
  forall (l2 : prt_names) (f : expr), term_expr_equiv l2 t f -> 
  alpha l1 e l2 f
.
Proof.
  simple induction 1; intros.
  inversion_clear H0.
  apply alp_srt.

  inversion_clear H1.
  apply alp_ref.
  generalize l2 H2.
  elim H0; intros.
  inversion_clear H1.
  apply tr_hd.

  inversion_clear H5.
  apply tr_tl; auto with coc core arith datatypes.

  inversion_clear H4.
  apply alp_abs; auto with coc core arith datatypes.

  inversion_clear H4.
  apply alp_app; auto with coc core arith datatypes.

  inversion_clear H4.
  apply alp_prod; auto with coc core arith datatypes.

  inversion_clear H0.
  apply alp_nat.

  inversion_clear H0.
  apply alp_nat_o.

  inversion_clear H2.
  apply alp_nat_succ; auto with coc core.

  inversion_clear H8.
  apply alp_nat_destruct; auto with coc core.

  inversion_clear H8.
  apply alp_nat_cases; auto with coc core.
Qed.

(* 
  Provided a good naming context, finding a named term for a 
  nameless term is a decidable problem.
*)
Definition expr_of_term :
  forall (t : term) (l : prt_names),
  name_unique l ->
  free_db (length l) t -> {e : expr | term_expr_equiv l t e}.
Proof.
  simple induction t; intros.
  exists (SRT s).
  apply eqv_srt.

  elim (list_item _ l n); intros.
  inversion_clear a.
  exists (REF x).
  apply eqv_ref.
  apply name_unique_first; auto with coc core arith datatypes.

  elimtype False.
  inversion_clear H0.
  generalize n b H1.
  elim l; simpl in |- *.
  intros.
  inversion_clear H0.

  simple destruct n0; intros.
  elim b0 with a; auto with coc core arith datatypes.

  apply H0 with n1; auto with coc core arith datatypes.
  red in |- *; intros.
  elim b0 with t0; auto with coc core arith datatypes.

  elim H with l; intros; auto with coc core arith datatypes.
  elim find_free_var with l; intros.
  elim H0 with (x0 :: l); intros.
  exists (ABS x0 x x1).
  apply eqv_abs; auto with coc core arith datatypes.

  apply fv_ext; auto with coc core arith datatypes.

  inversion_clear H2; auto with coc core arith datatypes.

  inversion_clear H2; auto with coc core arith datatypes.

  elim H with l; intros; auto with coc core arith datatypes.
  elim H0 with l; intros; auto with coc core arith datatypes.
  exists (APP x x0).
  apply eqv_app; auto with coc core arith datatypes.

  inversion_clear H2; auto with coc core arith datatypes.

  inversion_clear H2; auto with coc core arith datatypes.

  elim H with l; intros; auto with coc core arith datatypes.
  elim find_free_var with l; intros.
  elim H0 with (x0 :: l); intros.
  exists (PROD x0 x x1).
  apply eqv_prod; auto with coc core arith datatypes.

  apply fv_ext; auto with coc core arith datatypes.

  inversion_clear H2; auto with coc core arith datatypes.

  inversion_clear H2; auto with coc core arith datatypes.

  exists NAT.
  apply eqv_nat; auto with coc core datatypes.

  exists NAT_O.
  apply eqv_nat_o; auto with coc core datatypes.

  elim H with l; auto with coc core datatypes.
  intros; exists (NAT_SUCC x).
  apply eqv_nat_succ; auto with coc core datatypes.
  inversion H1; auto with coc core datatypes.

  elim H2 with l; (auto with coc core datatypes || (inversion_clear H4; assumption) || idtac).
  elim H1 with l; (auto with coc core datatypes || (inversion_clear H4; assumption) || idtac).
  elim H0 with l; (auto with coc core datatypes || (inversion_clear H4; assumption) || idtac).
  elim H with l; (auto with coc core datatypes || (inversion_clear H4; assumption) || idtac).
  intros.
  exists (NAT_DESTRUCT x x0 x1 x2); apply eqv_nat_destruct; auto with coc core datatypes.

  elim H2 with l; (auto with coc core datatypes || (inversion_clear H4; assumption) || idtac).
  elim H1 with l; (auto with coc core datatypes || (inversion_clear H4; assumption) || idtac).
  elim H0 with l; (auto with coc core datatypes || (inversion_clear H4; assumption) || idtac).
  elim H with l; (auto with coc core datatypes || (inversion_clear H4; assumption) || idtac).
  intros.
  exists (NAT_CASES x x0 x1 x2); apply eqv_nat_cases; auto with coc core datatypes.
Defined.

(* The condition for an expression to contain undefined vars *)
Definition undef_vars (e : expr) (def undef : prt_names) : Prop :=
  list_disjoint _ def undef /\
  (forall x : name, In _ x undef -> expr_vars x e)
.

(* An inclusion lemma *)
Lemma undef_vars_incl :
  forall (e : expr) (l u1 u2 : prt_names),
  incl _ u1 u2 -> undef_vars e l u2 -> undef_vars e l u1.
Proof.
  unfold undef_vars in |- *; split.
  inversion_clear H0.
  red in |- *; simpl in |- *; intros.
  apply H1 with x; auto with coc core arith datatypes.

  inversion_clear H0; auto with coc core arith datatypes.
Qed.

(* Undefined variables in abs *)
Lemma undef_vars_abs :
  forall (x : name) (e1 e2 : expr) (l u1 u2 : prt_names),
  undef_vars e1 l u1 ->
  undef_vars e2 (x :: l) u2 -> undef_vars (ABS x e1 e2) l (u1 ++ u2)
.
Proof.
  split; intros.
  inversion_clear H.
  inversion_clear H0.
  red in |- *; simpl in |- *; intros.
  elim In_app with name x0 u1 u2; intros; auto with coc core arith datatypes.
  apply H1 with x0; auto with coc core arith datatypes.

  apply H with x0; auto with coc core arith datatypes.

  inversion_clear H.
  inversion_clear H0.
  elim In_app with name x0 u1 u2; intros; auto with coc core arith datatypes.
  apply ev_abs_r; auto with coc core arith datatypes.
  red in |- *; intros.
  apply H with x0; auto with coc core arith datatypes.
  rewrite H5; auto with coc core arith datatypes.
Qed.

(* Undefined variables in app *)
Lemma undef_vars_app :
  forall (e1 e2 : expr) (l u1 u2 : prt_names),
  undef_vars e1 l u1 ->
  undef_vars e2 l u2 -> undef_vars (APP e1 e2) l (u1 ++ u2)
.
Proof.
  split; intros.
  inversion_clear H.
  inversion_clear H0.
  red in |- *; simpl in |- *; intros.
  elim In_app with name x u1 u2; intros; auto with coc core arith datatypes.
  apply H1 with x; auto with coc core arith datatypes.

  apply H with x; auto with coc core arith datatypes.

  inversion_clear H.
  inversion_clear H0.
  elim In_app with name x u1 u2; intros; auto with coc core arith datatypes.
Qed.

(* Undefined variables in prod *)
Lemma undef_vars_prod :
  forall (x : name) (e1 e2 : expr) (l u1 u2 : prt_names),
  undef_vars e1 l u1 ->
  undef_vars e2 (x :: l) u2 -> undef_vars (PROD x e1 e2) l (u1 ++ u2)
.
Proof.
  split; intros.
  inversion_clear H.
  inversion_clear H0.
  red in |- *; simpl in |- *; intros.
  elim In_app with name x0 u1 u2; intros; auto with coc core arith datatypes.
  apply H1 with x0; auto with coc core arith datatypes.

  apply H with x0; auto with coc core arith datatypes.

  inversion_clear H.
  inversion_clear H0.
  elim In_app with name x0 u1 u2; intros; auto with coc core arith datatypes.
  apply ev_prod_r; auto with coc core arith datatypes.
  red in |- *; intros.
  apply H with x0; auto with coc core arith datatypes.
  rewrite H5; auto with coc core arith datatypes.
Qed.

(* Undefined variables in nat_succ *)
Lemma undef_vars_nat_succ :
  forall (e : expr) (l u : prt_names),
  undef_vars e l u -> undef_vars (NAT_SUCC e) l u
.
Proof.
  split; intros.

  inversion_clear H.
  auto with coc core datatypes.
  inversion_clear H.
  apply ev_nat_succ; auto with coc core datatypes.
Qed.

(* Undefined variables in nat_destruct *)
Lemma undef_vars_nat_destruct :
  forall (e1 e2 e3 e4 : expr) (l u1 u2 u3 u4 : prt_names),
  undef_vars e1 l u1 ->
  undef_vars e2 l u2 ->
  undef_vars e3 l u3 ->
  undef_vars e4 l u4 ->
  undef_vars (NAT_DESTRUCT e1 e2 e3 e4) l (u1 ++ u2 ++ u3 ++ u4)
.
Proof.
  split; intros.

  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H2.
  red in |- *; simpl in |- *; intros.
  elim In_app with name x u1 (u2 ++ u3 ++ u4); intros; auto with coc core datatypes.
  apply H3 with x; auto with coc core datatypes.
  elim In_app with name x u2 (u3 ++ u4); intros; auto with coc core datatypes.
  apply H with x; auto with coc core datatypes.
  elim In_app with name x u3 u4; intros; auto with coc core datatypes.
  apply H0 with x; auto with coc core datatypes.
  apply H1 with x; auto with coc core datatypes.

  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H2.
  elim In_app with name x u1 (u2 ++ u3 ++ u4); intros; auto with coc core datatypes.
  elim In_app with name x u2 (u3 ++ u4); intros; auto with coc core datatypes.
  elim In_app with name x u3 u4; intros; auto with coc core datatypes.
Qed.

(* Undefined variables in nat_destruct *)
Lemma undef_vars_nat_cases :
  forall (e1 e2 e3 e4 : expr) (l u1 u2 u3 u4 : prt_names),
  undef_vars e1 l u1 ->
  undef_vars e2 l u2 ->
  undef_vars e3 l u3 ->
  undef_vars e4 l u4 ->
  undef_vars (NAT_CASES e1 e2 e3 e4) l (u1 ++ u2 ++ u3 ++ u4)
.
Proof.
  split; intros.

  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H2.
  red in |- *; simpl in |- *; intros.
  elim In_app with name x u1 (u2 ++ u3 ++ u4); intros; auto with coc core datatypes.
  apply H3 with x; auto with coc core datatypes.
  elim In_app with name x u2 (u3 ++ u4); intros; auto with coc core datatypes.
  apply H with x; auto with coc core datatypes.
  elim In_app with name x u3 u4; intros; auto with coc core datatypes.
  apply H0 with x; auto with coc core datatypes.
  apply H1 with x; auto with coc core datatypes.

  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H2.
  elim In_app with name x u1 (u2 ++ u3 ++ u4); intros; auto with coc core datatypes.
  elim In_app with name x u2 (u3 ++ u4); intros; auto with coc core datatypes.
  elim In_app with name x u3 u4; intros; auto with coc core datatypes.
Qed.

(* 
  If we find a named term for an unnmaed one, it doesn't have any undefined vars
*)
Lemma equiv_no_undef :
  forall (l : prt_names) (t : term) (e : expr),
  term_expr_equiv l t e ->
  forall undef : prt_names, undef_vars e l undef -> undef = nil
.
Proof.
  simple induction 1; simple destruct undef; intros;
  auto with coc core arith datatypes.

  inversion_clear H0.
  cut (expr_vars n (SRT s)); intros; auto with coc core arith datatypes.
  inversion_clear H0.

  inversion_clear H1.
  elim H2 with n0; auto with coc core arith datatypes.
  cut (expr_vars n0 (REF x)); intros; auto with coc core arith datatypes.
  inversion_clear H1.
  elim H0; auto with coc core arith datatypes.

  inversion_clear H4.
  cut (expr_vars n (ABS x B N)); intros; auto with coc core arith datatypes.
  cut (n :: nil = nil); intros.
  discriminate H7.

  inversion_clear H4.
  apply H1.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H5 with n; auto with coc core arith datatypes.
  generalize H4.
  inversion_clear H8; auto with coc core arith datatypes.
  inversion H9.

  generalize H7.
  inversion_clear H4; auto with coc core arith datatypes.
  inversion H8.

  apply H3.
  split; intros.
  red in |- *; simpl in |- *; intros.
  inversion H4.
  apply H7.
  elim H11.
  inversion_clear H9; auto with coc core arith datatypes.
  inversion H10.

  elim H5 with x0; auto with coc core arith datatypes.
  inversion_clear H9; auto with coc core arith datatypes.
  inversion H13.

  generalize H8.
  inversion_clear H4; auto with coc core arith datatypes.
  inversion H9.

  inversion_clear H4.
  cut (expr_vars n (APP a b)); intros; auto with coc core arith datatypes.
  cut (n :: nil = nil); intros.
  discriminate H7.
  inversion_clear H4.
  apply H1.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H5 with n; auto with coc core arith datatypes.
  generalize H4.
  inversion_clear H8; auto with coc core arith datatypes.
  inversion H9.

  generalize H7.
  inversion_clear H4; auto with coc core arith datatypes.
  inversion H8.

  apply H3.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H5 with n; auto with coc core arith datatypes.
  generalize H4.
  inversion_clear H8; auto with coc core arith datatypes.
  inversion H9.

  generalize H7.
  inversion_clear H4; auto with coc core arith datatypes.
  inversion H8.

  inversion_clear H4.
  cut (expr_vars n (PROD x B N)); intros; auto with coc core arith datatypes.
  cut (n :: nil = nil); intros.
  discriminate H7.

  inversion_clear H4.
  apply H1.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H5 with n; auto with coc core arith datatypes.
  generalize H4.
  inversion_clear H8; auto with coc core arith datatypes.
  inversion H9.

  generalize H7.
  inversion_clear H4; auto with coc core arith datatypes.
  inversion H8.

  apply H3.
  split; intros.
  red in |- *; simpl in |- *; intros.
  inversion H4.
  apply H7.
  elim H11.
  inversion_clear H9; auto with coc core arith datatypes.
  inversion H10.

  elim H5 with x0; auto with coc core arith datatypes.
  inversion_clear H9; auto with coc core arith datatypes.
  inversion H13.

  generalize H8.
  inversion_clear H4; auto with coc core arith datatypes.
  inversion H9.

  inversion_clear H0.
  cut (expr_vars n NAT); intros; auto with coc core arith datatypes.
  inversion_clear H0.

  inversion_clear H0.
  cut (expr_vars n NAT_O); intros; auto with coc core arith datatypes.
  inversion_clear H0.

  inversion H2.
  apply H1.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H3 with x0; auto with coc core arith datatypes.
  cut (expr_vars x0 (NAT_SUCC x')); intros; auto with coc core arith datatypes.
  inversion_clear H6.
  auto with coc core datatypes.

  inversion_clear H8.
  cut (expr_vars n (NAT_DESTRUCT choice' on_zero' on_succ' num')); intros; auto with coc core arith datatypes.
  cut (n :: nil = nil); intros.
  discriminate H11.
  inversion_clear H8.

  apply H1.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H9 with x; auto with coc core arith datatypes.
  inversion_clear H12; auto with coc core.
  inversion H13.
  inversion_clear H8; auto with coc core.
  inversion H12.

  apply H3.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H9 with x; auto with coc core arith datatypes.
  inversion_clear H12; auto with coc core.
  inversion H13.
  inversion_clear H8; auto with coc core.
  inversion H12.

  apply H5.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H9 with x; auto with coc core arith datatypes.
  inversion_clear H12; auto with coc core.
  inversion H13.
  inversion_clear H8; auto with coc core.
  inversion H12.

  apply H7.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H9 with x; auto with coc core arith datatypes.
  inversion_clear H12; auto with coc core.
  inversion H13.
  inversion_clear H8; auto with coc core.
  inversion H12.

  inversion_clear H8.
  cut (expr_vars n (NAT_CASES choice' on_zero' on_succ' num')); intros; auto with coc core arith datatypes.
  cut (n :: nil = nil); intros.
  discriminate H11.
  inversion_clear H8.

  apply H1.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H9 with x; auto with coc core arith datatypes.
  inversion_clear H12; auto with coc core.
  inversion H13.
  inversion_clear H8; auto with coc core.
  inversion H12.

  apply H3.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H9 with x; auto with coc core arith datatypes.
  inversion_clear H12; auto with coc core.
  inversion H13.
  inversion_clear H8; auto with coc core.
  inversion H12.

  apply H5.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H9 with x; auto with coc core arith datatypes.
  inversion_clear H12; auto with coc core.
  inversion H13.
  inversion_clear H8; auto with coc core.
  inversion H12.

  apply H7.
  split; intros.
  red in |- *; simpl in |- *; intros.
  elim H9 with x; auto with coc core arith datatypes.
  inversion_clear H12; auto with coc core.
  inversion H13.
  inversion_clear H8; auto with coc core.
  inversion H12.
Qed.

(* Finding a fitting nameless term is a decidable problem *)
  Definition term_of_expr :
   forall (e : expr) (l : prt_names),
   {t : term | term_expr_equiv l t e} +
   {undef : prt_names | undef_vars e l undef &  undef <> nil}.
Proof.
  simple induction e; intros.
  left.
  exists (Srt s).
  apply eqv_srt.

  elim (list_index _ name_dec n l); intros.
  left.
  inversion_clear a.
  exists (Ref x).
  apply eqv_ref; auto with coc core arith datatypes.

  right.
  exists (n :: nil).
  split.
  red in |- *; simpl in |- *; intros.
  generalize H.
  inversion_clear H0.
  intros.
  elim H0; intros; auto with coc core arith datatypes.

  inversion_clear H1.

  intros.
  inversion_clear H.
  apply ev_ref.

  inversion_clear H0.

  discriminate.

  elim H with l; intros.
  elim H0 with (n :: l); intros.
  left.
  inversion_clear a.
  inversion_clear a0.
  exists (Abs x x0).
  apply eqv_abs; auto with coc core arith datatypes.

  inversion_clear b.
  right.
  exists x.
  replace x with (nil ++ x); auto with coc core arith datatypes.
  apply undef_vars_abs; auto with coc core arith datatypes.
  split; intros.
  red in |- *; simpl in |- *; intros.
  inversion_clear H4.

  inversion_clear H3.

  auto with coc core arith datatypes.

  inversion_clear b.
  elim H0 with (n :: l); intros.
  right.
  exists x; auto with coc core arith datatypes.
  apply undef_vars_incl with (x ++ nil).
  red in |- *; simpl in |- *; intros.
  elim H3; simpl in |- *; auto with coc core arith datatypes.

  apply undef_vars_abs; auto with coc core arith datatypes.
  split; intros.
  red in |- *; simpl in |- *; intros.
  inversion_clear H4.

  inversion_clear H3.

  inversion_clear b.
  right.
  exists (x ++ x0); intros.
  apply undef_vars_abs; auto with coc core arith datatypes.

  generalize H2.
  case x; simpl in |- *; intros.
  elim H5; auto with coc core arith datatypes.

  discriminate.

  elim H with l; intros.
  elim H0 with l; intros.
  left.
  inversion_clear a.
  inversion_clear a0.
  exists (App x x0).
  apply eqv_app; auto with coc core arith datatypes.

  inversion_clear b.
  right.
  exists x.
  replace x with (nil ++ x); auto with coc core arith datatypes.
  apply undef_vars_app; auto with coc core arith datatypes.
  split; intros.
  red in |- *; simpl in |- *; intros.
  inversion H4.

  inversion H3.

  auto with coc core arith datatypes.

  inversion_clear b.
  elim H0 with l; intros.
  right.
  exists x; auto with coc core arith datatypes.
  apply undef_vars_incl with (x ++ nil).
  red in |- *; simpl in |- *; intros.
  elim H3; simpl in |- *; auto with coc core arith datatypes.

  apply undef_vars_app; auto with coc core arith datatypes.
  split; intros.
  red in |- *; simpl in |- *; intros.
  inversion_clear H4.

  inversion_clear H3.

  inversion_clear b.
  right.
  exists (x ++ x0); intros.
  apply undef_vars_app; auto with coc core arith datatypes.

  generalize H2.
  case x; simpl in |- *; intros.
  elim H5; auto with coc core arith datatypes.

  discriminate.

  elim H with l; intros.
  elim H0 with (n :: l); intros.
  left.
  inversion_clear a.
  inversion_clear a0.
  exists (Prod x x0).
  apply eqv_prod; auto with coc core arith datatypes.

  inversion_clear b.
  right.
  exists x.
  replace x with (nil ++ x); auto with coc core arith datatypes.
  apply undef_vars_prod; auto with coc core arith datatypes.
  split; intros.
  red in |- *; simpl in |- *; intros.
  inversion H4.

  inversion H3.

  auto with coc core arith datatypes.

  inversion_clear b.
  elim H0 with (n :: l); intros.
  right.
  exists x; auto with coc core arith datatypes.
  apply undef_vars_incl with (x ++ nil).
  red in |- *; simpl in |- *; intros.
  elim H3; simpl in |- *; auto with coc core arith datatypes.

  apply undef_vars_prod; auto with coc core arith datatypes.
  split; intros.
  red in |- *; simpl in |- *; intros.
  inversion H4.

  inversion H3.

  inversion_clear b.
  right.
  exists (x ++ x0); intros.
  apply undef_vars_prod; auto with coc core arith datatypes.

  generalize H2.
  case x; simpl in |- *; intros.
  elim H5; auto with coc core arith datatypes.

  discriminate.

  left; exists Nat; auto with coc core datatypes.
  apply eqv_nat.

  left; exists NatO; auto with coc core datatypes.
  apply eqv_nat_o.

  elim H with l; intros.
  elim a; intros.
  left; exists (NatSucc x); apply eqv_nat_succ; auto with coc core datatypes.
  elim b; intros.
  right; exists x; auto with coc core datatypes.
  apply undef_vars_nat_succ; auto with coc core datatypes.

  elim H with l; intros.
  elim H0 with l; intros.
  elim H1 with l; intros.
  elim H2 with l; intros.
  elim a2; elim a1; elim a0; elim a; intros.
  left; exists (NatDestruct x x0 x1 x2); apply eqv_nat_destruct; auto with coc core datatypes.
  elim b; intros.
  right; exists (nil ++ nil ++ nil ++ x).
  apply undef_vars_nat_destruct; auto with coc core datatypes.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  repeat rewrite app_nil_r; auto with coc core datatypes.
  elim b; intros.
  right; exists (nil ++ nil ++ x ++ nil).
  apply undef_vars_nat_destruct; auto with coc core datatypes.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  repeat rewrite app_nil_r; auto with coc core datatypes.
  elim b; intros.
  right; exists (nil ++ x ++ nil ++ nil).
  apply undef_vars_nat_destruct; auto with coc core datatypes.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  repeat rewrite app_nil_r; auto with coc core datatypes.
  elim b; intros.
  right; exists (x ++ nil ++ nil ++ nil).
  apply undef_vars_nat_destruct; auto with coc core datatypes.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  repeat rewrite app_nil_r; auto with coc core datatypes.

  elim H with l; intros.
  elim H0 with l; intros.
  elim H1 with l; intros.
  elim H2 with l; intros.
  elim a2; elim a1; elim a0; elim a; intros.
  left; exists (NatCases x x0 x1 x2); apply eqv_nat_cases; auto with coc core datatypes.
  elim b; intros.
  right; exists (nil ++ nil ++ nil ++ x).
  apply undef_vars_nat_cases; auto with coc core datatypes.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  repeat rewrite app_nil_r; auto with coc core datatypes.
  elim b; intros.
  right; exists (nil ++ nil ++ x ++ nil).
  apply undef_vars_nat_cases; auto with coc core datatypes.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  repeat rewrite app_nil_r; auto with coc core datatypes.
  elim b; intros.
  right; exists (nil ++ x ++ nil ++ nil).
  apply undef_vars_nat_cases; auto with coc core datatypes.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  repeat rewrite app_nil_r; auto with coc core datatypes.
  elim b; intros.
  right; exists (x ++ nil ++ nil ++ nil).
  apply undef_vars_nat_cases; auto with coc core datatypes.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  simpl; split; auto with coc core datatypes.
  red in |- *; intros.
  inversion H4.
  intros.
  inversion H3.
  repeat rewrite app_nil_r; auto with coc core datatypes.
Defined.
