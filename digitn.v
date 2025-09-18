From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

(******************************************************************************)
(*                                                                            *)
(* ndigits b n   ==  returns the number of digits of n in base b (only makes  *)
(*                      sense if 1 < b )                                      *)
(* digitn b n m  ==  returns the m^th digit of n in base b                    *)
(* rdigitn b n m ==  the bit-reversal for base b of m with bit length n       *)
(*     bin_lucas ==  Lucas theorem for binomial                               *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition digitn b n m := (n %/ b ^ m) %% b.

Lemma digit0n b m : digitn b 0 m = 0.
Proof. by rewrite /digitn div0n mod0n. Qed.

Lemma digitn0 b n : digitn b n 0 = n %% b.
Proof. by rewrite /digitn divn1. Qed.

Lemma digitnS b n m : digitn b n m.+1 = digitn b (n %/ b) m.
Proof. by rewrite /digitn -divnMA expnS. Qed.

Lemma ltn_digitn b n m : 0 < b -> digitn b n m < b.
Proof. by apply: ltn_pmod. Qed.

Lemma digitnE b n m : n < b ^ m -> n = \sum_(i < m) digitn b n i * b ^ i.
Proof.
elim: m n => [[]//=|m IH n nLb]; first by rewrite big_ord0.
rewrite {1}(divn_eq n b) [n %/ b]IH; last first.
  rewrite (divn_eq n b) in nLb.
  have := leq_ltn_trans (leq_addr _ _) nLb.
  by rewrite expnS mulnC ltn_mul2l => /andP[].
rewrite big_ord_recl addnC digitn0 muln1; congr (_ + _).
rewrite (big_morph _ (fun x y => mulnDl x y b) (mul0n b)).
apply: eq_bigr => /= i _.
by rewrite digitnS expnS mulnAC mulnA.
Qed.

Lemma digitn_exp b m n : 1 < b -> digitn b (b ^ m) n = (m == n).
Proof.
move=> b_gt1.
case: ltngtP=> [mLn|nLm|->]; rewrite /digitn.
- by rewrite divn_small ?mod0n // ltn_exp2l.
- rewrite -expnB 1?ltnW //.
  suff /dvdnP[k ->] : b %| b ^ (m - n) by rewrite modnMl.
  by rewrite dvdn_exp // subn_gt0.
by rewrite divnn expn_gt0 ltnW // modn_small.
Qed.

Lemma digitnMD b m d n : d < b -> digitn b (b * m + d) n.+1 = digitn b m n.
Proof.
move=> dLb.
have b_pos : 0 < b by apply: leq_ltn_trans dLb.
rewrite /digitn expnS divnMA mulnC divnMDl //.
by rewrite [d %/ _]divn_small ?addn0.
Qed.

Lemma digitn_uniq b n k (f : {ffun 'I_k -> 'I_b}) i :
  n < b ^ k -> n = (\sum_(i < k) f i * b ^ i)%N -> 
  f i = digitn b n i :> nat.
Proof.
elim: k n f i => [n f [] //|k IH n f i nLb].
have b_pos : 0 < b by case: (b) nLb => //; rewrite exp0n.
rewrite big_ord_recl /= muln1 => nE.
have f0E : f ord0 = n %% b :> nat.
  rewrite nE -modnDm -modn_summ big1 => [| j _].
    by rewrite mod0n addn0 modn_mod modn_small.
  by rewrite /bump add1n expnS mulnCA modnMr.
have /IH H : n %/ b = \sum_(i < k) [ffun i => f (lift ord0 i)] i * b ^ i.
  move/eqP: nE.
  rewrite f0E {1}(divn_eq n b) addnC eqn_add2l.
  under eq_bigr do rewrite /bump add1n expnS mulnCA.
  rewrite -big_distrr /= mulnC eqn_mul2l.
  rewrite eqn_leq leqNgt b_pos /= => /eqP->.
  by apply: eq_bigr => j _; rewrite !ffunE.
case i => [] [Hi|j Hj] /=.
  by rewrite digitn0 -f0E; congr (f _); apply/val_eqP.
rewrite digitnS.
have <- := H (Ordinal (Hj : j < k)).
  by rewrite ffunE /=; congr (f _); apply/val_eqP.
by rewrite ltn_divLR // mulnC -expnS.
Qed.

Definition ndigits b n := (trunc_log b n).+1.

Lemma ndigits0 b : ndigits b 0 = 1.
Proof. by rewrite /ndigits trunc_log0. Qed.

Lemma ndigits1 b : ndigits b 1 = 1.
Proof. by rewrite /ndigits trunc_log1. Qed.

Lemma ndigits_gt0 b n : 0 < ndigits b n.
Proof. by []. Qed.

Lemma ndigitsnn b n : 1 < b -> ndigits b (b ^ n) = n.+1.
Proof.
move=> b_gt1.
by rewrite /ndigits trunc_expnK // eqxx addn1 -leqn0 leqNgt expn_gt0 ltnW // 
           addn0.
Qed.

Lemma ndigits_bounds b n :
   1 < b -> 0 < n -> let k := ndigits b n in b ^ k.-1 <= n < b ^ k.
Proof.
move=> b_gt1; case: n => [//|[_|n _]]; first by rewrite ndigits1.
by have := trunc_log_bounds b_gt1 (isT : 0 < n.+2).
Qed.

Lemma ndigitsP b n : 1 < b -> n < b ^ ndigits b n.
Proof.
move=> b_gt1; case: n => [|n]; first by rewrite ndigits0 expn1 ltnW.
by case/andP: (ndigits_bounds b_gt1 (isT : 0 < n.+1)).
Qed.

Lemma ndigits_leq b n : 1 < b -> 0 < n -> b ^ (ndigits b n).-1 <= n.
Proof.
move=> b_gt1 n_pos.
by case/andP: (ndigits_bounds b_gt1 n_pos).
Qed.

Lemma ndigits_eq b n k :
   1 < b -> 0 < n -> b ^ k.-1 <= n < b ^ k -> ndigits b n = k.
Proof.
move=> b_gt1 n_pos /andP[bLn nLb].
have F1 := ndigitsP n b_gt1.
have F2 := ndigits_leq b_gt1 n_pos.
apply/eqP; case: ltngtP => H //; last first.
  move: nLb; rewrite ltnNge => /negP[].
  apply: leq_trans F2.
  apply: leq_pexp2l; first by apply/ltnW.
  by rewrite -ltnS prednK // ndigits_gt0.
move: bLn; rewrite leqNgt => /negP[].
apply: leq_trans F1 _.
apply: leq_pexp2l; first by apply/ltnW.
by rewrite -ltnS prednK // (leq_ltn_trans _ H).
Qed.

Lemma ndigits_small b d : 1 < b -> d < b -> ndigits b d = 1.
Proof.
move=> b_gt1; case: d => [_|d dLb]; first by rewrite ndigits0.
by apply: ndigits_eq.
Qed.

Lemma ndigitsMD b n d : 
  1 < b -> 0 < n -> d < b -> ndigits b (b * n + d) = (ndigits b n).+1.
Proof.
move=> b_gt1 n_pos d_digit.
apply: ndigits_eq => //.
  apply: leq_trans (leq_addr _ _).
  by rewrite muln_gt0 ltnW.
apply/andP; split.
  apply: leq_trans (leq_addr _ _).
  rewrite /= -(prednK (ndigits_gt0 b n)) expnS leq_mul2l.
  by rewrite -leqn0 leqNgt ltnW //= ndigits_leq.
apply: leq_trans (_ : b * n.+1 <= _); first by rewrite mulnS addnC ltn_add2r.
by rewrite expnS leq_mul2l -leqn0 leqNgt ltnW // ndigitsP.
Qed.

Lemma ndigitsM b n : 1 < b -> 0 < n -> ndigits b (b * n) = (ndigits b n).+1.
Proof.
move=> b_gt1 n_pos.
by rewrite -(ndigitsMD b_gt1 n_pos (_ : 0 < b)) ?addn0 // ltnW.
Qed.

Lemma ndigitsXM b n k : 
  1 < b -> 0 < n -> ndigits b (b ^ k * n) = k + ndigits b n.
Proof.
move=> b_g1 n_pos.
elim: k => [|k IH]; first by rewrite mul1n.
rewrite expnS -mulnA ndigitsM ?IH //.
by rewrite muln_gt0 expn_gt0 ltnW.
Qed.

Lemma digitnE_ndigits b n : 
  1 < b -> n = \sum_(i < ndigits b n) digitn b n i * b ^ i.
Proof. by move=> b_gt1; exact: (digitnE (ndigitsP n b_gt1)). Qed.

Definition rdigitn b n m :=
  reducebig 0 (index_iota 0 n) 
   (fun i : nat => BigBody i addn true (digitn b m (n.-1 - i) * b ^ i)).

Compute map (rdigitn 2 3) (iota 0 8).

Lemma rdigitnE b n m : 
  rdigitn b n m = \sum_(i < n) digitn b m (n.-1 - i) * b ^ i.
Proof. 
have <- := (big_mkord xpredT (fun i : nat => digitn b m (n.-1 - i) * b ^ i)).
by rewrite unlock.
Qed.

Lemma rdigitn0 b n : rdigitn b n 0 = 0.
Proof. by rewrite rdigitnE big1 // => i; rewrite digit0n mul0n. Qed.

Lemma rdigit0n b m : rdigitn b 0 m = 0.
Proof. by rewrite rdigitnE big_ord0. Qed.

Lemma rdigitnSMl b m n :
 0 < b -> rdigitn b n.+1 m = (m %% b) * b ^ n + rdigitn b n (m %/ b).
Proof.
move=> b_gt0.
rewrite !rdigitnE big_ord_recr addnC /= subnn digitn0; congr (_ + _).
apply: eq_bigr => i _.
have n_gt0 : 0 < n by apply: leq_ltn_trans (_ : i < n)%N.
by rewrite -[X in X - i](prednK n_gt0) subSn ?digitnS // -ltnS prednK.
Qed.

Lemma rdigitn_even m n : rdigitn 2 n.+1 m.*2 = rdigitn 2 n m.
Proof. by rewrite rdigitnSMl // -muln2 mulnK // modnMl. Qed.

Lemma rdigitn_odd m n : rdigitn 2 n.+1 m.*2.+1 = 2 ^ n + rdigitn 2 n m.
Proof.
by rewrite rdigitnSMl // -muln2 -addn1 modnMDl mul1n divnMDl // addn0.
Qed.

Lemma rdigitnK b n m : m < b ^ n -> rdigitn b n (rdigitn b n m) = m.
Proof.
have [|b_gt0] := leqP b 0.
  by case: b; case: n; case: m => //= [n|n m]; rewrite exp0n.
move=> mLbn.
rewrite {1}rdigitnE [RHS](digitnE mLbn).
apply: eq_bigr => i _; congr (_ * _).
rewrite rdigitnE.
pose f1 := [ffun i : 'I_n => (Ordinal (@ltn_digitn b m (n.-1 - i) b_gt0)) ].
have G : \sum_(i < n) digitn b m (n.-1 - i) * b ^ i = 
         \sum_(i < n) (f1 i * b ^ i).
  by apply: eq_bigr => j _; rewrite ffunE.
have n_gt0 : 0 < n by case: i; case: (n).
have FF : n.-1 - i < n.
  apply: leq_ltn_trans (leq_subr _ _) _.
  by rewrite prednK.
have <- := digitn_uniq (Ordinal FF) _ G.
  rewrite ffunE /= subnA //; first by rewrite subnn.
  by rewrite -ltnS prednK.
move: n.-1 => u; elim: {i f1 G mLbn n_gt0 FF}n => [|n IH].
  by rewrite big_ord0 expn0.
rewrite big_ord_recr /= -addSn.
have -> : (b ^ n.+1 = b ^ n + b.-1 * b ^ n)%nat.
  by rewrite expnS -[X in X * _ = _](prednK b_gt0) mulSn.
rewrite leq_add // leq_mul2r expn_eq0 eqn0Ngt b_gt0 /= -ltnS prednK //.
by rewrite ltn_digitn.
Qed.

Lemma ltn_rdigitn b n m : 0 < b -> rdigitn b n m < b ^ n.
Proof.
move=> b_gt0.
elim: n m => [n |n IH m]; first by rewrite rdigit0n.
rewrite rdigitnSMl // -addnS addnC.
have -> : (b ^ n.+1 = b ^ n + b.-1 * b ^ n)%nat.
  by rewrite expnS -[X in X * _ = _](prednK b_gt0) mulSn.
rewrite leq_add // leq_mul2r expn_eq0 eqn0Ngt b_gt0 /= -ltnS prednK //.
by rewrite ltn_mod.
Qed.

Import GRing.Theory.
Local Open Scope ring_scope.

Section ExtraLemma.

Variable p : nat.
Hypothesis Pp : prime p.

Lemma Fp_exprnD (p1 p2 : {poly 'F_p}) : (p1 + p2) ^+ p = p1 ^+ p + p2 ^+ p.
Proof.
rewrite -[X in _ ^+ X](prednK (prime_gt0 Pp)).
rewrite exprDn big_ord_recl /= subn0 mulr1 bin0 mulr1n.
rewrite big_ord_recr /bump add1n //= prednK // ?prime_gt0 //; congr (_ + _).
rewrite subnn binn mul1r mulr1n big1 ?add0r // => i _.
have /dvdnP[k ->] : (p %| 'C(p, (0 <= i) + i))%N.
   apply: prime_dvd_bin Pp _ => //.
   by rewrite add1n andTb -[X in (_ < X)%N](prednK (prime_gt0 Pp)) ltnS.
by rewrite mulrnA -mulr_natr -polyC1 -polyCMn pchar_Fp_0 // polyC0 !mulr0.
Qed.

Lemma Fp_exprnDn n (p1 p2 : {poly 'F_p}) :
  (p1 + p2) ^+ (p ^ n) = p1 ^+ (p ^ n) + p2 ^+ (p ^ n).
Proof. by elim: n => // n IH; rewrite expnS mulnC !exprM IH Fp_exprnD. Qed.

End ExtraLemma.

Section Lucas.

Variable p : nat.
Hypothesis Pp : prime p.

Lemma bin_lucas m n k : 
  (m < p ^ k -> n < p ^ k -> 
 'C(m, n) = \prod_(i < k) 'C(digitn p m i, digitn p n i) %[mod p])%N.
Proof.
move=> mLp nLp.
have [nLm | mLn] := leqP n m; last first.
  suff [i Hi] : exists i : 'I_k, (digitn p m i < digitn p n i)%N.
    by rewrite (bigD1 i) //= !bin_small.
  apply/existsP; apply: contraTT mLn.
  rewrite negb_exists -leqNgt => /forallP dmLdn.
  rewrite (digitnE nLp) (digitnE mLp) leq_sum // => i _.
  by rewrite leq_mul2r leqNgt dmLdn orbT.
have -> : ('C(m, n) %% p)%N = ((1 + 'X) ^+ m : {poly 'F_p})`_n.
  have nLm1 : (n < m.+1)%N by apply: leq_trans nLm.
  rewrite exprDn coef_sum.
  under eq_bigr do rewrite expr1n mul1r coefMn coefXn.
  rewrite (bigD1 (Ordinal nLm1)) //= eqxx mulr1n big1 => [|i /eqP/val_eqP/=].
    by rewrite [X in (_ = _ %% X)%N]Fp_cast // addn0 val_Fp_nat // modn_mod.
  by rewrite eq_sym => /negPf->; rewrite mulr0n // mul0rn.
rewrite {1}(digitnE mLp) expr_sum.
under eq_bigr do rewrite mulnC exprM Fp_exprnDn // expr1n exprDn.
have H i : 
  \sum_(j < (digitn p m i).+1)
    1 ^+ (digitn p m i - j) * 'X^(p ^ i) ^+ j *+ 'C(digitn p m i, j) =
  \sum_(j < p) 'X^(p ^ i) ^+ j *+ 'C(digitn p m i, j).
  under eq_bigr do rewrite expr1n mul1r.
  rewrite -!(big_mkord xpredT (fun j => 'X^(p ^ i) ^+ j *+ 'C(digitn p m i, j))).
  rewrite (big_cat_nat _ (ltn_digitn m i (prime_gt0 Pp))) //=.
  rewrite [X in _ = _ + X]big_nat_cond [X in _ = _ + X]big1 ?addr0 // => j.
  by case/andP=> /andP[/bin_small->]; rewrite mulr0n.
under eq_bigr do rewrite {}H.
rewrite bigA_distr_bigA /= coef_sum.
under eq_bigr do under eq_bigr do rewrite -exprM mulnC.
under eq_bigr do rewrite prodrMn -expr_sum coefMn coefXn.
pose f : {ffun 'I_k -> 'I_p} := 
  [ffun i : 'I_k =>  Ordinal (ltn_digitn n i (prime_gt0 Pp))].
rewrite (bigD1 f) //= [X in (_ %% X)%N]Fp_cast //= .
rewrite [in X in ((_ + X) = _ %[mod _])%N]big1 ?addn0 => [| i iDf].
  rewrite (_ : _ == _) ?mulr1n.
    under eq_bigr do rewrite ffunE /=.
    by rewrite val_Fp_nat // modn_mod.
  apply/eqP; rewrite {1}[n](digitnE nLp); apply: eq_bigr => /= i _.
  by rewrite ffunE.
case: (n =P _) => nEs //; last by rewrite mul0rn.
case/eqP: iDf; apply/ffunP => j; apply/val_eqP =>/=.
by rewrite (digitn_uniq _ _ nEs) // ffunE.
Qed.

End Lucas.
