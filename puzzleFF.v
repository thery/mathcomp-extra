From mathcomp Require Import all_ssreflect.

(******************************************************************************)
(*                                                                            *)
(* f is a strictly increasing function such that f (f n) = 3 n                *)
(* does it exist an n0 such that f n0 = 2022                                  *)
(*                                                                            *)
(******************************************************************************)


Section PuzzleFF.

Variable f : nat -> nat.

Hypothesis monof : {mono f : m n / m < n}.

Lemma leqfD a b : f a + b <= f (a + b).
Proof.
elim: b a => [a|b IH a]; first by rewrite !addn0.
by rewrite !addnS (leq_ltn_trans (IH a)) //= monof.
Qed.

Lemma leqf2D a b c : f (a + c) <= b + c -> f a <= b.
Proof.
elim: c => [|c IH fLb]; first by rewrite !addn0.
apply: IH.
by rewrite -ltnS -addnS (leq_trans _ fLb) // monof addnS.
Qed.

Lemma eqf2D a b c : f (a + b) = f a + b -> c <= b -> f (a + c) = f a + c.
Proof.
elim: c => [|c IH  fabE cLb]; first by by rewrite !addn0.
have facE : f (a + c) = f a + c by apply: IH => //; apply: ltnW.
apply/eqP; rewrite eqn_leq leqfD andbT.
apply: leqf2D (_ : _ <= _ + (b - c.+1)).
by do 2 rewrite -addnA (subnKC cLb) ?fabE.
Qed.

Lemma leqnfn n : n <= f n.
Proof.
by elim: n => // n IH; apply: leq_ltn_trans IH _; rewrite monof.
Qed.

Hypothesis ffE : forall n, f (f n) = 3 * n. 

Lemma ltnfn n : 0 < n -> n < f n.
Proof.
move=> n_gt0.
have := leqnfn n; rewrite leq_eqVlt; case: eqP => // nE _.
have : f n = 3 * n by rewrite [in LHS]nE ffE.
move=> /eqP; rewrite -nE -{1}(mul1n n) eqn_mul2r.
by case: (n) n_gt0.
Qed.

Lemma leqfn3n n : f n <= 3 * n.
Proof. by rewrite -ltnS -monof ffE (leqnfn (S (3 * n))). Qed.

Lemma ltfn3n n : 0 < n -> f n < 3 * n.
Proof.
move=> n_gt0.
have := leqfn3n n; rewrite leq_eqVlt; case: eqP => // fnE _.
have : 3 * n < f (3 * n) by apply: ltnfn; rewrite muln_gt0.
by rewrite -[in X in _ < X -> _]fnE ffE ltnn.
Qed.

Lemma f1E : f 1 = 2.
Proof.
by apply/eqP; rewrite eqn_leq ltnfn // -ltnS ltfn3n.
Qed.

Lemma f2E : f 2 = 3.
Proof. by rewrite -[in LHS]f1E ffE. Qed.

Lemma f3nE n : f (3 ^ n) = 2 * 3 ^ n /\ f (2 * 3 ^ n) = 3 ^ (S n).
Proof.
elim: n => [|n [IH1 IH2]]; first by rewrite f1E f2E.
have f3SnE : f (3 ^ n.+1) = 2 * 3 ^ n.+1 . 
  by rewrite -[in LHS]IH2 ffE mulnC -mulnA expnS [3 * _]mulnC.
by split => //; rewrite -f3SnE ffE !expnS.
Qed.

Fact f1293E : f 1293 = 2022.
Proof.
destruct (f3nE 6) as [H1 H2].
rewrite -[2022]/(2 * 3 ^ 6 + (2022 - 2 * (3 ^ 6))).
rewrite -{1}[1293]/(3 ^ 6 + (2022 - 2 * (3 ^ 6))).
rewrite -[X in _ = X + _]H1.
apply: eqf2D (_ : _ = _ + 3 ^ 6) _ => //.
by rewrite -[3 ^ 6 + 3 ^ 6]/(2 * 3 ^ 6) H2 H1.
Qed.

End PuzzleFF.