From mathcomp Require Import all_boot.

(******************************************************************************)
(*                                                                            *)
(*   Consider n points in the plane.                                          *)
(*   Let us count in how many ways we can choose 2 line-segments              *)
(*                                                                            *)
(******************************************************************************)

Lemma binception n : 'C('C(n, 2), 2) = 3 * 'C(n.+1, 4).
Proof.
case: n => //= [] [|n]//.
have pbin2 m : 'C(m, 2).*2 = m.-1 * m.
  by case: m => //=  m; rewrite -mul2n mul_bin_left bin1 subn1.
have pbin4 m : 24 * 'C(m.+3, 4) = m * m.+1 * m.+2 * m.+3.
  rewrite -[24]/(2 * 3 *4) -!mulnA mul_bin_left [3 * _]mulnCA mul_bin_left.
  rewrite !subSS !subn0 mulnCA; congr muln.
  by rewrite mulnCA mul_bin_left bin1 subn1.
apply: double_inj; rewrite pbin2.
apply: double_inj; rewrite doubleMl double_pred pbin2.
apply: double_inj; rewrite doubleMr pbin2.
have ->: (3 * 'C(n.+3, 4)).*2.*2.*2 =  24 * 'C(n.+3, 4).
   by rewrite -!mul2n !mulnA.
rewrite pbin4.
have ->: (n.+2.-1 * n.+2).-2 = n * n.+3 by rewrite /= [RHS]mulnS.
rewrite -!mulnA; congr muln.
by rewrite mulnC !mulnA.
Qed.

