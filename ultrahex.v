(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From mathcomp Require Import all_ssreflect.

(******************************************************************************)
(* This file contain a proof that the last digit of the ultrahex is 6         *)
(******************************************************************************)

Definition ultra_hex := 6 ^ 6 ^ 6 ^ 6 ^ 6 ^ 6.

Definition last_digit k := k %% 10.

Compute last_digit 66.

Lemma last_digit_exp6n_is_six n : 0 < n -> last_digit (6 ^ n) = 6.
Proof.
move=> nP; apply/eqP; suff : 6 ^ n == 6 %[mod 10] by [].
rewrite (chinese_remainder (isT : coprime 2 5)).
by apply/andP; split; apply/eqP; rewrite -[LHS]modnXm !(exp0n, exp1n).
Qed.

(* Alternative proof

Lemma last_digitM a b : 
  last_digit (a * b) = last_digit (last_digit a * last_digit b).
Proof. by apply/sym_equal/modnMm. Qed.

Lemma last_digit_exp6n_is_six n : 0 < n -> last_digit (6 ^ n) = 6.
Proof.
elim: n => // [] [|n] // /(_ isT) IH _; rewrite expnS last_digitM IH.
Qed.

*)

Fact last_digit_ultra_hex_is_six : last_digit ultra_hex = 6.
Proof. by apply: last_digit_exp6n_is_six; rewrite expn_gt0. Qed.
