From mathcomp Require Import all_boot.

(******************************************************************************)
(*                                                                            *)
(*                    Nicomachus theorem                                      *)
(*                                                                            *)
(******************************************************************************)

Lemma sum_gauss n : (\sum_(i < n) i).*2 = n * n.-1.
Proof.
elim: n => [|n IH /=]; first by rewrite big_ord0.
rewrite big_ord_recr /= doubleD IH /= -muln2 -mulnDr addn2 [RHS]mulnC.
by case: (n).
Qed.

Lemma nicomachus n : \sum_(i < n) i ^ 3 = (\sum_(i < n) i) ^ 2.
Proof.
do 2 apply: double_inj.
rewrite -2![in RHS]muln2 -mulnAC -mulnA !muln2 !sum_gauss mulnn.
elim: n => [|n IH /=]; first by rewrite !big_ord0.
rewrite big_ord_recr /= !doubleD IH !expnMn.
rewrite [n ^ 3]expnS [n * _]mulnC -!muln2 -2!mulnA -mulnDr mulnC !muln2.
case: (n) => [//|n1 /=]; congr (_ * _).
by rewrite -[in RHS]addn2 sqrnD mulSn addnA -doubleMr !(muln2, mul2n).
Qed.
