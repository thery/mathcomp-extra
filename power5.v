From mathcomp Require Import all_ssreflect.

(******************************************************************************)
(*                                                                            *)
(* The last digit of any integer n^5 is n itself                              *)
(*                                                                            *)
(******************************************************************************)

Lemma modnMDXl p m n d : (p * d + m) ^ n  = m ^ n %[mod d].
Proof.
by elim: n p m => // n IH p m; rewrite !expnS -modnMm IH modnMDl modnMm.
Qed.

Lemma digitn_power5 n : n ^ 5 = n %[mod 10].
Proof.
rewrite [n](divn_eq _ 10) modnMDXl modnMDl.
by case: (_ %% _) (ltn_mod n 10) => //; do 9 (case => //).
Qed.
