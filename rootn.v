(* Computation of nth root (code from Yves.Bertot@inria.fr)                   *)
From mathcomp Require Import all_boot.

(******************************************************************************)
(*                                                                            *)
(*   rootn n i      ==  computes the integer n^th root of i                   *)
(*   is_rootn n i   ==  check if i is of n^th root of a number                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint rootn_rec k r n :=
  if r == 0 then 0 else
  if n is n1.+1 then
  let v := (rootn_rec k (r %/ (2 ^ k)) n1).*2 in
  if v.+1 ^ k <= r then v.+1 else v
  else 0.

Definition rootn k n :=
  if k == 0 then 0 else rootn_rec k n n.

Lemma rootn_rec_bound k r n : 
  0 < k -> r <= n -> (rootn_rec k r n) ^ k  <= r < (rootn_rec k r n ).+1 ^ k.
Proof.
case: k => // k _.
have F : 1 < 2 ^ k.+1 by rewrite -{1}[1](exp1n k.+1) ltn_exp2r.
elim: n r => [[] //=|n IH [|[|r]] rLn /=]; rewrite ?(exp0n, exp1n) //.
  rewrite divn_small //=.
  have -> : rootn_rec k.+1 0 n = 0 by case: (n).
  by rewrite exp1n /= exp1n.
set x := _ %/ _; set u := rootn_rec _ _ _.
have /IH : x <= n.
  apply: leq_trans (rLn : _ < n).
  have /mulnK H : 0 < 2 ^ k.+1 by rewrite expn_gt0.
  rewrite -[r.+1]H leq_div2r //.
  by rewrite -{1}[r.+1]muln1 ltn_mul2l.
rewrite -/u => /andP[uLx xLu].  
case: (leqP (u.*2.+1 ^ k.+1 ) r.+2) => ->; rewrite !(andbT, andTb).
  rewrite -doubleS -muln2 expnMn.
  rewrite (divn_eq r.+2 (2 ^ k.+1)) -/x.
  apply: leq_trans (_ : x.+1 * 2 ^ k.+1 <= _).
    by rewrite mulSn addnC ltn_add2r // ltn_mod ?expn_gt0.
  by rewrite leq_mul2r // expn_eq0.
rewrite -muln2 expnMn (divn_eq r.+2 (2 ^ k.+1)) -/x.
apply: leq_trans (leq_addr _ _).
by rewrite leq_mul2r // expn_eq0.
Qed.

Lemma root0n i : rootn 0 i = 0.
Proof. by rewrite /rootn eqxx. Qed.

Lemma rootn_bound n i : 0 < n -> rootn n i ^ n <= i < (rootn n i).+1 ^ n.
Proof. by case: n => // n  _; apply: rootn_rec_bound. Qed.

Lemma rootn0 n : rootn n 0 = 0.
Proof. by case: n. Qed.

Definition is_rootn n i := (i == rootn n i ^ n).

Lemma is_rootnE n i : is_rootn n i = (i == rootn n i ^ n).
Proof. by []. Qed.

Lemma leq_rootn n x y : 0 < n -> x <= y -> rootn n x <= rootn n y.
Proof.
move=> n_gt0 xLy.
rewrite -ltnS -(ltn_exp2r _ _ n_gt0).
have /andP[rLx _] := rootn_bound x n_gt0.
have /andP[_ yLr] := rootn_bound y n_gt0.
by apply: leq_ltn_trans rLx (leq_ltn_trans _ yLr).
Qed.

Lemma rootnE n x y :
  0 < n -> y ^ n <= x < y.+1 ^ n -> rootn n x = y.
Proof.
move=> n_gt0 /andP[ynLx xLySn].
have /andP[rLx xLrS] := rootn_bound x n_gt0.
apply/eqP; rewrite eqn_leq.
rewrite -ltnS -(ltn_exp2r _ _ n_gt0) (leq_ltn_trans rLx) //.
by rewrite -ltnS -(ltn_exp2r _ _ n_gt0) (leq_ltn_trans ynLx).
Qed.

Lemma expnK n x : 0 < n -> rootn n (x ^ n) = x.
Proof.
by move=> n_gt0; apply: rootnE; rewrite // leqnn ltn_exp2r ?ltnSn.
Qed.

Lemma rootn_leq n x y :
  0 < n -> x ^ n <= y -> x <= rootn n y.
Proof. by move=> n_gt0 xnLy; rewrite -(expnK x n_gt0) leq_rootn. Qed.

Lemma rootn_ltn n x y :
  0 < n -> x < y.+1 ^ n -> rootn n x <= y.
Proof.
move=> n_gt0; rewrite ltnNge [in X in _ -> X]leqNgt.
apply: contra => yLrx.
have /andP[rLx _] := rootn_bound x n_gt0.
by apply: leq_trans rLx; rewrite leq_exp2r.
Qed.

Definition sqrtn := rootn 2.

Lemma sqrtn_bound n : (sqrtn n) ^ 2 <= n < ((sqrtn n).+1) ^ 2.
Proof. by apply: rootn_bound. Qed.

Lemma sqrtnE n x : x ^ 2 <= n < x.+1^2 -> sqrtn n = x.
Proof. by apply: rootnE. Qed.

Lemma leq_sqrtn m n : m <= n -> sqrtn m <= sqrtn n.
Proof. by apply: leq_rootn. Qed.

Lemma sqrnK n : sqrtn (n ^ 2) = n.
Proof. by apply: expnK. Qed.

Lemma sqrtn_gt0 n : (0 < sqrtn n) = (0 < n).
Proof.
by case: n => [|n]; rewrite // -[1%N]/(sqrtn 1) // leq_sqrtn.
Qed.
