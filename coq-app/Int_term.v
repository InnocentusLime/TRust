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
  This is another part of the complicated strong normalization proof.
  This module describes the `interpretation` of term. We quote the
  original article in attempt to explain what's going on.
*)

Require Import Termes.

(*
  As usual we give ourselves an interpretation of free variables. Since
  out interpretation has two components (terms as terms and types as 
  invariant candidates), we need two levels. This is the term-level.

  The term part of an interpretation is a function from positive integers
  to terms. Here we'll denote the interpretation with `I`
*)
Definition intt := nat -> term.

(* Used in as an utility *)
Definition shift_intt (i : intt) (t : term) : intt :=
  fun n : nat => 
  match n with
  | O => t
  | S k => i k
  end
.

(*
  The interpretation of a term `t` in `I` denoted with `t[I]`, is the parallel
  substituion of any free de Brujin index `i` by `I i`. We also offset the
  substitution by `k`
*)
Fixpoint int_term (t : term) : intt -> nat -> term :=
  fun (I : intt) (k : nat) =>
  match t with
  | Srt s => Srt s
  | Ref n =>
    match le_gt_dec k n with
    | left _ => lift k (I (n - k))
    | right _ => Ref n
    end
  | Abs A t => Abs (int_term A I k) (int_term t I (S k))
  | App u v => App (int_term u I k) (int_term v I k)
  | Prod A B => Prod (int_term A I k) (int_term B I (S k))
  (* New terms *)
  | Nat => Nat
  | NatO => NatO
  | NatSucc x => NatSucc (int_term x I k)
  | NatDestruct x1 x2 x3 x4 => NatDestruct (int_term x1 I k) (int_term x2 I k) (int_term x3 I k) (int_term x4 I k)
  | NatCases x1 x2 x3 x4 => NatCases (int_term x1 I k) (int_term x2 I k) (int_term x3 I k) (int_term x4 I k)
  end
.

Opaque le_gt_dec.

(* 
  A small lemma which states that one can erase the substituion. Because
  of the parallel substituion on the inside.
*)
Lemma int_term_subst :
  forall (t : term) (it : intt) (k : nat) (x : term),
  subst_rec x (int_term t it (S k)) k = int_term t (shift_intt it x) k
.
Proof.
  simple induction t; simpl in |- *; intros; auto with coc core arith sets.
  elim (le_gt_dec (S k) n); intros.
  elim (le_gt_dec k n); intros.
  rewrite simpl_subst; auto with coc core arith sets.
  replace (n - k) with (S (n - S k)); auto with coc core arith sets.
  rewrite minus_Sn_m; auto with coc core arith sets.

  elim le_not_gt with k n; auto with coc core arith sets.

  simpl in |- *.
  elim (lt_eq_lt_dec k n); [ intro Hlt_eq | intro Hlt ].
  elim Hlt_eq; clear Hlt_eq; [ intro Hlt | intro Heq ].
  absurd (n <= k); auto with coc core arith sets.

  elim (le_gt_dec k n); [ intro Hle | intro Hgt ];
  auto with coc core arith sets.
  elim Heq.
  replace (k - k) with 0; auto with coc core arith sets.

  inversion_clear Heq in Hgt.
  elim gt_irrefl with n; auto with coc core arith sets.

  elim (le_gt_dec k n); intros; auto with coc core arith sets.
  absurd (k <= n); auto with coc core arith sets.

  rewrite H; rewrite H0; auto with coc core arith sets.

  rewrite H; rewrite H0; auto with coc core arith sets.

  rewrite H; rewrite H0; auto with coc core arith sets.

  rewrite H; auto with coc core arith sets.

  rewrite H; rewrite H0; rewrite H1; rewrite H2; auto with coc core arith sets.

  rewrite H; rewrite H0; rewrite H1; rewrite H2; auto with coc core arith sets.
Qed.
