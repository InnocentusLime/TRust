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

Require Import RustTermes.

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
    intros x y; generalize y x; clear x y.
    apply (
      par_red1_mut
      (fun x y H => forall z, transp term par_red1 z x -> exists2 y' : term, (transp term par_red1 y' y) & (par_red1 z y'))
      (fun x y H => forall z, transp (list term) par_red1_list z x -> exists2 y' : list term, (transp (list term) par_red1_list y' y) & (par_red1_list z y'))
    ); intros.

    inversion_clear H.
    exists (Srt s); auto with rust core sets.

    inversion_clear H.
    exists U8; auto with rust core sets.

    inversion_clear H1.
    elim H with args'0; auto with rust core; intros.
    elim H0 with range'0; auto with rust core; intros.
    exists (Fn x x0); auto with rust core sets.

    inversion_clear H.
    exists (NumConst n); auto with rust core sets.

    inversion H1.
    subst z; subst l0; subst r0.
    elim H with l'0; auto with rust core sets; intros.
    elim H0 with r'0; auto with rust core sets; intros.
    exists (Add x x0); auto with rust core sets.
    subst z; subst l; subst r.
    inversion p; inversion p0.
    subst n0; subst l'; subst n1; subst r'.
    exists (NumConst (n + m)); auto with rust core sets.

    inversion_clear H.
    inversion H0; inversion H1.
    subst r'; subst n1; subst l'; subst n0.
    exists (NumConst (n + m)); auto with rust core sets.
    exists (NumConst (n + m)); auto with rust core sets.

    inversion H1.
    subst z; subst l0; subst r0.
    elim H with l'0; auto with rust core sets; intros.
    elim H0 with r'0; auto with rust core sets; intros.
    exists (Sub x x0); auto with rust core sets.
    subst z; subst l; subst r.
    inversion p; inversion p0.
    subst n0; subst l'; subst n1; subst r'.
    exists (NumConst (n - m)); auto with rust core sets.

    inversion_clear H.
    inversion H0; inversion H1.
    subst r'; subst n1; subst l'; subst n0.
    exists (NumConst (n - m)); auto with rust core sets.
    exists (NumConst (n - m)); auto with rust core sets.

    inversion_clear H.
    exists (Ref n); auto with rust core sets.

    inversion H2.
    subst z; subst body0; subst range0; subst args0.
    elim H with args'0; auto with rust core sets; intros.
    elim H0 with range'0; auto with rust core sets; intros.
    elim H1 with body'0; auto with rust core sets; intros.
    exists (Func x x0 x1); auto with rust core sets.

    inversion H1.
    subst z; subst call_args0; subst body0; subst range0; subst args0.
    elim H with body'0; auto with rust core sets; intros.
    elim H0 with call_args'0; auto with rust core sets; intros.
    
(*)
  Qed.

  (*
    Strip lemma is a lemma useful in proving confluence of
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
*)