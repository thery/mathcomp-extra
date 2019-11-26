(* Computation of nth root (code from Yves.Bertot@inria.fr)                   *)
From mathcomp Require Import all_ssreflect.

(******************************************************************************)
(*                                                                            *)
(*   rootn n i      ==  computes the integer n^th root of i                   *)
(*   is_rootn n i   ==  check if i is of n^th root of a number                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint seq_pol_add (s1 s2 : seq nat) :=
  if s1 is a :: s3 then
  if s2 is b :: s4 then a + b :: seq_pol_add s3 s4
  else s1 else s2.
 
Fixpoint seq_pol_mul (s1 s2 : seq nat) :=
  if s1 is a :: s3 then 
     seq_pol_add [seq a * i | i <- s2] (seq_pol_mul s3 (0 :: s2))
  else [::].

Fixpoint seq_pol_exp (s : seq nat) n := iter n (seq_pol_mul s) [:: 1].

Definition seq_2Xp1_exp_n (n : nat) := seq_pol_exp [:: 1; 2] n.

Fixpoint seq_pol_eval (s : seq nat) (x : nat) :=
  if s is a :: s1 then a + x * seq_pol_eval s1 x else 0.

Fixpoint pre_rootn l n (fuel i : nat) :=
  if fuel is fuel1.+1 then
    if i == 0 then 
      (0, 0)
    else
      let i' := i %/ n in
      let k' := i %% n in
      let (r, k2) := pre_rootn l n fuel1 i' in
        let remainder := seq_pol_eval l r in
        if remainder <=  n * k2 + k' then
           (r.*2.+1, n * k2 + k'- remainder)
        else
           (r.*2, n * k2 + k')
  else (0, 0).

Definition rootn (n i : nat) := 
  (pre_rootn ((take n (seq_2Xp1_exp_n n))) (2 ^ n) i i).1.

Definition is_rootn (n i : nat) :=
  (pre_rootn ((take n (seq_2Xp1_exp_n n))) (2 ^ n) i i).2.

Lemma seq_pol_addP s1 s2 x :
   seq_pol_eval (seq_pol_add s1 s2) x = 
   seq_pol_eval s1 x + seq_pol_eval s2 x.
Proof.
elim: s1 s2 => [| a s1 IH] [| b s2] //=.
Show 1.
by rewrite seq_pol_add_cons /= IH mulnDr !addnA (addnAC a).
Qed.

Lemma seq_pol_eval0 s x : all (eq_op^~ 0) s -> seq_pol_eval s x = 0.
Proof. 
by elim: s => [| a s IH] //= /andP[/eqP -> s0]; rewrite add0n IH // muln0.
Qed.

Lemma seq_pol_mul0r s s2 x : 
  all (fun y => y == 0) s2 -> seq_pol_eval (seq_pol_mul s s2) x = 0.
Proof.
elim: s s2 => [ | a s IH] s2 //= s20; rewrite seq_pol_addP.
suff /seq_pol_eval0-> : all (eq_op^~ 0) [seq a * i | i <- s2].
  by rewrite add0n IH.
elim: s2 s20 => [ | b s2 ih] //= => /andP[/eqP -> s20].
by rewrite muln0 eqxx ih.
Qed.

Lemma seq_pol_scal s a x : 
  seq_pol_eval [seq a * i | i <- s] x = a * seq_pol_eval s x.
Proof.
by elim: s => [|b s IH] //=; rewrite ?muln0 // mulnDr IH mulnCA.
Qed.

Lemma pol_mulP s1 s2 x :
   seq_pol_eval (seq_pol_mul s1 s2) x = seq_pol_eval s1 x * seq_pol_eval s2 x.
Proof.
elim: s1 s2 => [| a s1 IH] //= s2.
by rewrite seq_pol_addP seq_pol_scal mulnDl IH /= add0n mulnA (mulnC _ x).
Qed.

Lemma seq_2Xp1_exp_nP n x :
  seq_pol_eval (seq_2Xp1_exp_n n) x = x.*2.+1 ^ n.
Proof.
rewrite /seq_2Xp1_exp_n.
elim: n => [| n IH]; first by rewrite /= muln0 expn0.
by rewrite expnS /seq_pol_exp iterS pol_mulP IH /= muln0 addn0 muln2.
Qed.

Lemma seq_pol_add_size s1 s2 : 
  size (seq_pol_add s1 s2) = maxn (size s1) (size s2).
Proof.
elim: s1 s2 => [| a s1 IH] s2 //=; first by rewrite max0n.
case: s2 => [| b s2]; first by rewrite maxn0.
by rewrite /= maxnSS IH.
Qed.

Lemma seq_pol_mul_size a b s2 :
  size (seq_pol_mul [:: a; b] s2) = (size s2).+1.
Proof.
rewrite /= muln0 seq_pol_add_size /= !size_map.
by apply/maxn_idPr; rewrite leqnSn.
Qed.

Lemma seq_pol_exp_size a b n : 
  size (seq_pol_exp [:: a; b] n) = n.+1.
Proof.
rewrite /seq_pol_exp; elim: n => [| n IH] //.
by rewrite iterS seq_pol_mul_size IH.
Qed.

Lemma add_small_large_coef s1 s2 n d : size s1 <= n ->
  nth d (seq_pol_add s1 s2) n = nth d s2 n.
Proof.
elim: s1 s2 n => [| a s1 IH] s2 n //= sz.
case: s2 => [| b s2]; first by rewrite !nth_default.
by case: n sz => [| n] //; rewrite ltnS /= => s1n; apply: IH.
Qed.

Lemma seq_pol_eval_cut s n x :
   seq_pol_eval (take n s) x + x ^ n * seq_pol_eval (drop n s) x = 
   seq_pol_eval s x.
Proof.
elim: s n => [| a s IH] //= n; first by rewrite add0n muln0.
case: n => [| n]; first by rewrite /= expn0 mul1n add0n.
by rewrite /= expnS -mulnA -addnA -mulnDr IH.
Qed.

Lemma drop_seq_pol_add s1 s2 n : 
   drop n (seq_pol_add s1 s2) = seq_pol_add (drop n s1) (drop n s2).
Proof.
elim: s1 s2 n => [| a s1 IH] // [| b s2] //= [| n] //.
by case: (drop n s1).
Qed.

Lemma seq_2Xp1_exp_n_lead a b n : 
  drop n (seq_pol_exp [:: a; b] n) = [:: b ^ n].
Proof.
elim: n => [| n IH] //.
have -> : seq_pol_exp [:: a; b] n.+1 = 
          seq_pol_mul [:: a; b] (seq_pol_exp [:: a; b] n).
  by rewrite /seq_pol_exp iterS.
rewrite [seq_pol_mul _ _](_ : _ =
           seq_pol_add [seq a * c | c <- seq_pol_exp [:: a; b] n]
              [seq b * c | c <- 0 :: seq_pol_exp [:: a; b] n]); last first.
  by rewrite /=; congr (seq_pol_add _ _).
rewrite drop_seq_pol_add drop_oversize; last first.
  by rewrite size_map seq_pol_exp_size.
rewrite -[LHS]/(drop n [seq b * c | c <- seq_pol_exp [:: a; b] n]).
by rewrite -map_drop IH /= expnS.
Qed.

Lemma test_pol_correct n r:
  seq_pol_eval (take n (seq_2Xp1_exp_n n)) r + 2 ^ n * r ^ n = r.*2.+1 ^ n.
Proof.
rewrite -seq_2Xp1_exp_nP -(seq_pol_eval_cut (seq_2Xp1_exp_n n) n r).
by congr (_ + _); rewrite seq_2Xp1_exp_n_lead /= muln0 addn0 mulnC.
Qed.

Lemma pre_rootnP fuel i n (l := take n (seq_2Xp1_exp_n n)) :
  i <= fuel -> 0 < n ->
  (pre_rootn l (2 ^ n) fuel i).1 ^ n + (pre_rootn l (2 ^ n) fuel i).2 = i /\
  i < ((pre_rootn l (2 ^ n) fuel i).1.+1) ^ n.
Proof.
revert l.
case: n => [// | n] l ilefuel _; set n':= n.+1; move: ilefuel.
elim: fuel i => [| fuel IH] i //.
  rewrite leqn0 => /eqP -> /=; rewrite expnS mul0n !add0n; split => //.
  by rewrite expn_gt0.
move=> fuelc.
elim/abstract_context : (pre_rootn l (2 ^ n.+1) fuel.+1 i) => Q defQ.
rewrite /=.
case: ifP => [/eqP iis0 | in0].
  by rewrite defQ /= iis0 expnS mul0n !add0n expn_gt0; split.
set q := (i %/ _).
case recq : (pre_rootn _ _ _) => [r k'].
have t2le2p : 2 <= 2 ^ n.+1.
  elim: (n) => [//| k ih]; rewrite expnS mul2n -addnn.
  by apply/(leq_trans ih)/leq_addr.
have divgt0 : 0 < 2 ^ n.+1.
  by apply: leq_trans t2le2p.
have iltfuel : q <= fuel.
  rewrite /q.
  have igt0 : 0 < i by rewrite lt0n in0.
  have := (ltn_Pdiv t2le2p igt0) => fact.
  by rewrite -ltnS; apply: leq_trans fuelc.
have := IH q iltfuel; rewrite recq; cbn [fst snd] =>[] [req rlt].
case: ifP => [below | above].
  rewrite defQ; cbn [fst snd]; rewrite -test_pol_correct -/n'.
  rewrite (addnAC (seq_pol_eval _ _)) subnKC; last by exact below.
  rewrite (addnC (2 ^ n' * k')) -addnA -mulnDr (addnC k') req.
  rewrite addnC mulnC -divn_eq; split; first by [].
  rewrite -doubleS -mul2n expnMn.
  move: rlt; rewrite -(leq_pmul2l divgt0); apply: leq_trans.
  by rewrite mulnC; apply: (ltn_ceil i divgt0).
move/negbT: above; rewrite -ltnNge=> above.
rewrite defQ; cbn [fst snd].
rewrite addnA -mul2n expnMn mul2n -mulnDr mulnC req -divn_eq.
split; first by[].
rewrite -test_pol_correct (divn_eq i (2 ^ n.+1)) -/q addnC -req -(addnC k').
rewrite mulnDl addnA (mulnC (r ^ n')) ltn_add2r.
by rewrite addnC mulnC.
Qed.

Lemma rootn_bound n i : 0 < n -> rootn n i ^ n <= i < (rootn n i).+1 ^ n.
Proof.
rewrite /rootn => n_gt0; have [H1 H2] := pre_rootnP (leqnn i) n_gt0.
by rewrite -[X in (_ <= X) && _ ]H1 leq_addr.
Qed.

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
