From mathcomp Require Import all_ssreflect.

(******************************************************************************)
(*                                                                            *)
(* f is a strictly increasing function such that f (f 3 n)                    *)
(* does it exist an n0 such that f n0 = 2022                                  *)
(*                                                                            *)
(******************************************************************************)


Section PuzzleFF.

Variable f : nat -> nat.

Hypothesis HI : forall m n, f n < f m <-> n < m.

Lemma HI1 a b : f a + b <= f (a + b).
Proof.
elim: b a => [a|b IH a]; first by rewrite !addn0.
rewrite !addnS (leq_ltn_trans (IH a)) //=.
by apply/HI.
Qed.

Lemma HI2 a b c : f (a + c) <= b + c -> f a <= b.
Proof.
elim: c => [|c IH fLb]; first by rewrite !addn0.
apply: IH.
rewrite -ltnS -addnS (leq_trans _ fLb) //.
by apply/HI; rewrite addnS.
Qed.

Lemma HI3 a b c : f (a + b) = f a + b -> c <= b -> f (a + c) = f a + c.
Proof.
elim: c => [|c IH  fabE cLb]; first by by rewrite !addn0.
have facE : f (a + c) = f a + c by apply: IH => //; apply: ltnW.
apply/eqP; rewrite eqn_leq HI1 andbT.
apply: HI2 (_ : _ <= _ + (b - c.+1)).
by do 2 rewrite -addnA (subnKC cLb) ?fabE.
Qed.

Lemma Hsub n : n <= f n.
Proof.
elim: n => // n IH.
apply: leq_ltn_trans IH _.
by apply/HI.
Qed.

Hypothesis Hff : forall n, f (f n) = 3 * n. 

Lemma Hsubs n : 0 < n -> n < f n.
Proof.
move=> n_gt0.
have := Hsub n; rewrite leq_eqVlt; case: eqP => // nE _.
have : f n = 3 * n by rewrite [in LHS]nE Hff.
move=> /eqP; rewrite -nE -{1}(mul1n n) eqn_mul2r.
by case: (n) n_gt0.
Qed.

Lemma Hsub3 n : f n <= 3 * n.
Proof.
rewrite -ltnS; apply/HI.
by rewrite Hff (Hsub (S (3 * n))).
Qed.

Lemma Hsub3s n : 0 < n -> f n < 3 * n.
Proof.
move=> n_gt0.
have := Hsub3 n; rewrite leq_eqVlt; case: eqP => // fnE _.
have : 3 * n < f (3 * n) by apply: Hsubs; rewrite muln_gt0.
by rewrite -[in X in _ < X -> _]fnE Hff ltnn.
Qed.

Lemma Hf1 : f 1 = 2.
Proof.
by apply/eqP; rewrite eqn_leq Hsubs // -ltnS Hsub3s.
Qed.

Lemma Hf2 : f 2 = 3.
Proof. by rewrite -[in LHS]Hf1 Hff. Qed.

Lemma Hf3n n : f (3 ^ n) = 2 * 3 ^ n /\ f (2 * 3 ^ n) = 3 ^ (S n).
Proof.
elim: n => [|n [IH1 IH2]]; first by rewrite Hf1 Hf2.
have HL : f (3 ^ n.+1) = 2 * 3 ^ n.+1 . 
  by rewrite -[in LHS]IH2 Hff mulnC -mulnA expnS [3 * _]mulnC.
by split => //; rewrite -HL Hff !expnS.
Qed.

Fact f_1293 : f 1293 = 2022.
Proof.
destruct (Hf3n 6) as [H1 H2].
rewrite -[2022]/(2 * 3 ^ 6 + (2022 - 2 * (3 ^ 6))).
rewrite -{1}[1293]/(3 ^ 6 + (2022 - 2 * (3 ^ 6))).
rewrite -[X in _ = X + _]H1.
apply: HI3 (_ : _ = _ + 3 ^ 6) _ => //.
by rewrite -[3 ^ 6 + 3 ^ 6]/(2 * 3 ^ 6) H2 H1.
Qed.

End PuzzleFF.