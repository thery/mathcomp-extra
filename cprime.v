From Stdlib Require Import String NArith.
From mathcomp Require Import all_ssreflect.
Require Import digitn.

(******************************************************************************)
(*                                                                            *)
(* cpermn b n p =  a circular permutation of p digits in base b of n          *)
(*                                                                            *)
(* cprime b n =  all the circular permutations give raise to a prime number   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Cprime.

Definition cpermn b n p := 
  let v := (ndigits b n) in 
  foldr (fun i r => digitn b n i * b ^ ((i + p) %% v) + r) 0 (iota 0 v).

Compute cpermn 10 1234 1.

Lemma cpermnE b n p : 
    let v := ndigits b n in 
    cpermn b n p = \sum_(i < v) digitn b n i * b ^ ((i + p) %% v).
Proof.
move=> v.
rewrite big_mknat unlock /reducebig /cpermn -/v.
rewrite -[index_iota _ _]/(iota 0 v).
pose k := 0.
rewrite -![0 as X in foldr _ X]/k.
have : all (fun i => i < v) (iota 0 v).
  apply/allP => i.
  elim: v {2 4}v (leqnn v) => // u IH v uLv.
  rewrite -addn1 iotaD mem_cat => /orP[/IH->//|]; first by apply: ltnW.
  by rewrite /= inE => /eqP->.
elim: iota k => //= a l IH k /andP[aLd Ha].
by rewrite IH // inordK.
Qed.

Lemma cper0mn n i : cpermn 0 n i = n.
Proof.
rewrite cpermnE /ndigits /=.
by rewrite trunc_log0n big_ord1 modn1 muln1 /digitn modn0 divn1.
Qed.

Lemma cper1mn n i : cpermn 1 n i = 0.
Proof.
rewrite cpermnE /ndigits /=.
by rewrite trunc_log1n big_ord1 exp1n muln1 /digitn modn1.
Qed.

Lemma cperm0n b i : cpermn b 0 i = 0.
Proof. by rewrite cpermnE big1 // => /=  j _; rewrite digit0n mul0n. Qed.

Lemma cpermn0 b n : 1 < b -> cpermn b n 0 = n.
Proof.
move=> b_gt1; rewrite cpermnE [RHS](digitnE_ndigits _ b_gt1).
by apply: eq_bigr => /= i _; rewrite addn0 modn_small.
Qed.

Lemma cpermnE' b n p : 
    let v := ndigits b n in 
    cpermn b n p = \sum_(i < v) digitn b n ((v - p %% v + i) %% v) * b ^ i.
Proof.
move=> v; rewrite cpermnE -/v.
pose f i := (v - (p %%v) + i) %% v.
have fP i : f i < v by apply: ltn_mod.
pose fO (i : 'I_v) := Ordinal (fP i).
have fO_inj : injective fO.
  move=> [i Hi] [j Hj] /val_eqP /=.
  rewrite /f /= eqn_modDl !modn_small => // iE.
  by apply/val_eqP.
rewrite [LHS](reindex_inj fO_inj).
apply: eq_bigr => /= i _; congr (digitn _ _ _ * _ ^ _).
rewrite /f modnDml addnC addnA -modnDml -[(p + _)%% _]modnDml.
rewrite [p %% v + _]addnC subnK; last by rewrite ltnW ?ltn_mod.
by rewrite modnn modn_small // ltn_ord.
Qed.

Lemma digitn_cpermn b n i j (v := ndigits b n) :
  1 < b -> j < v -> 
  digitn b (cpermn b n i) j = digitn b n ((v - i %% v + j) %% v).
Proof.
move=> b_gt1 jLv; rewrite cpermnE' -/v.
apply: (@digitn_sum b v (fun j => digitn b n ((v - i %% v + j) %% v))) => //.
by move=> k _; apply: ltn_digitn; rewrite ltnW.
Qed.

Lemma ndigits_cpermn b p i : ndigits b (cpermn b p i) <= ndigits b p.
Proof.
case: b => [|[|b]]; first by rewrite /ndigits !trunc_log0n.
 by rewrite /ndigits !trunc_log1n.
have -> : ndigits b.+2 p = ndigits b.+2 (b.+2 ^ (ndigits b.+2 p)).-1.
  by rewrite ndigits_predX.
apply: leq_ndigits.
rewrite predX_sum cpermnE'.
apply: leq_sum => /= [] [j Hj] /= _.
by rewrite leq_mul2r -ltnS ltn_digitn ?orbT.
Qed.

Definition cprime b p := 
  all prime [seq cpermn b p i | i <- iota 0 (ndigits b p)].

Lemma cprime_prime b p : 1 < b -> cprime b p -> prime p.
Proof.
move=> b_gt1 /allP->//.
rewrite -[X in X \in _](cpermn0 _ b_gt1).
by apply: map_f.
Qed.

Lemma cprime_digit_gcd b p i k : 
  1 < b -> 1 < k -> 1 < gcdn k b -> cprime b p -> digitn b p i = k -> p = k.
Proof.
move=> b_gt1 k_pos g_gt1 pCP dE.
have b_gt0 : 0 < b by apply: ltnW.
have gD1 : gcdn k b != 1 by case: gcdn g_gt1 => // [] [].
have pP : prime p by apply: cprime_prime pCP.
have [nLi|iLn] := leqP (ndigits b p) i.
  rewrite digitn_eq0 // in dE.
  by rewrite -dE in k_pos.
have [i_eq0|i_neq0] := (i =P 0).
  have kDm : gcdn k b %| p.
    rewrite (divn_eq p b) dvdn_add //.
      by rewrite dvdn_mull // dvdn_gcdr.
    by rewrite -digitn0 -i_eq0 dE dvdn_gcdl.
  have /primeP[_ /(_ _ kDm)] := pP.
  rewrite (negPf gD1) => /eqP gEp.
  rewrite -dE i_eq0 -gEp digitn0.
  have : gcdn k b <= b by rewrite dvdn_leq // dvdn_gcdr.
  case: ltngtP => // [H|/gcdn_idPr bDk]; first by rewrite modn_small.
  have : b <= k by apply: dvdn_leq => //; rewrite ltnW.
  by rewrite leqNgt -dE ltn_digitn. 
have i_pos : 0 < i by case: (i) i_neq0.
pose m := cpermn b p (ndigits b p - i).
have mP : prime m.
  have /allP->// := pCP.
  suff /map_f-> : (ndigits b p - i) \in iota 0 (ndigits b p) by [].
  by rewrite mem_iota andTb add0n ltn_subrL i_pos ndigits_gt0.
have kDm : gcdn k b %| m.
  rewrite [m](digitnE_ndigits _ b_gt1).
  case: ndigits => [|v]; first by rewrite big_ord0 dvdn0.
  rewrite big_ord_recl /= dvdn_add // -dE.
    rewrite dvdn_mulr // digitn_cpermn // addn0.
    rewrite [(_ - i) %% _]modn_small; last by rewrite ltn_psubCl ?subnn.
    by rewrite subKn ?modn_small ?dvdn_gcdl // ltnW.
  rewrite dE; apply: dvdn_trans (dvdn_gcdr _ _) _.
  under eq_bigr do rewrite expnD expn1 mulnCA .
  have <- : (b * \sum_(i0 < v)  digitn b m (bump 0 i0) * b ^ i0) = 
              \sum_(i0 < v)  b * (digitn b m (bump 0 i0) * b ^ i0).
    by apply: big_distrr.
  by rewrite dvdn_mulr.
case/primeP : (mP) => _ /(_ _ kDm).
rewrite (negPf gD1) eq_sym /= => /eqP mEg.
have mLb : m < b.
  have : m <= b by rewrite mEg dvdn_leq // dvdn_gcdr.
  case: ltngtP => // mEb _.
  have : m <= k by rewrite mEg dvdn_leq 1?ltnW // dvdn_gcdl.
  by rewrite mEb leqNgt -dE ltn_digitn.
have d_eq0 : digitn b p 0 = 0.
  suff : digitn b m ((ndigits b p - i) %% ndigits b p) = 0.
    rewrite digitn_cpermn ?ltn_mod //.
    by rewrite subnK ?modnn// ltnW // ltn_mod.
  rewrite digitn_eq0 // ndigits_small //.
  by rewrite modn_small ?subn_gt0 // ltn_subrL i_pos.
have bDk : b %| p.
  by rewrite (divn_eq p b) dvdn_add ?dvdn_mull // -digitn0 d_eq0 dvdn0.
have /primeP[_ /(_ _ bDk)] := pP.
case/orP=>[|/eqP bE]; first by case: (b) b_gt1 => // [] [].
rewrite bE (digitn_exp 1) in dE; last by rewrite -bE.
rewrite -dE in k_pos.
by case: eqP k_pos.
Qed.

Lemma cprime_digit0 b p i : 
  1 < b -> cprime b p -> digitn b p i = 0 -> (ndigits b p <= i) || (p == b).
Proof.
move=> b_gt1 pCP dpE0.
set v := ndigits _ _.
have b_neq1 : b != 1 by case: (b) b_gt1 => [] // [].
have pP : prime p.
  have /allP->// := pCP.
  rewrite -[X in X \in _](cpermn0 _ b_gt1).
  by apply: map_f.
have [dE0|dNE0] := digitn b p 0 =P 0.
  have bDp : b %| p.
    by rewrite (divn_eq p b) dvdn_add ?dvdn_mull // -digitn0 dE0 dvdn0.
  have /primeP[_ /(_ _ bDp)] := pP.
  by rewrite (negPf b_neq1) => /eqP->; rewrite eqxx orbT.
have [i_eq0|i_neq0] := (i =P 0); first by case: dNE0; rewrite -[in LHS]i_eq0.
have i_pos : 0 < i by case: (i) i_neq0.
have [//|iLv] := leqP v i.
pose m := cpermn b p (v - i).
have mP : prime m.
  have /allP->// := pCP.
  suff /map_f-> : (v - i) \in iota 0 v by [].
  by rewrite mem_iota andTb add0n ltn_subrL i_pos ndigits_gt0.
have dmE0 : digitn b m 0 = 0.
  rewrite digitn_cpermn -/v // addn0.
  rewrite [(_ - i) %% _]modn_small; last by rewrite ltn_psubCl ?subnn.
  by rewrite subKn ?modn_small // ltnW.
have bDk : b %| m.
  by rewrite (divn_eq m b) dvdn_add ?dvdn_mull // -digitn0 dmE0 dvdn0.
have bEm : b = m.
  have /primeP[_ /(_ _ bDk)] := mP.
  by case/orP=>[|/eqP //]; case: (b) b_gt1 => // [] [].
have F k : digitn b m k = (k == 1).
  by rewrite -bEm -{2}[b]expn1 digitn_exp // eq_sym.
move: bEm.
rewrite [m]cpermnE'.
have FO : v - i < v by rewrite ltn_subrL i_pos ndigits_gt0.
pose o := (Ordinal FO).
rewrite (bigD1 o) //= (modn_small FO) subKn 1?ltnW //.
rewrite [i + _]addnC subnK 1?ltnW // modnn -/v => He.
have [Hd|Hd] := digitn b p 0 =P 0.
  have bDp : b %| p.
    by rewrite (divn_eq p b) dvdn_add ?dvdn_mull // -digitn0 dmE0 dvdn0.
  suff -> : b = p by [].
  have /primeP[_ /(_ _ bDp)] := pP.
  by case/orP=>[|/eqP //]; case: (b) b_gt1 => // [] [].
have : 0 < v - i by rewrite subn_gt0.
rewrite leq_eqVlt => /orP[/eqP nE1|nL]; last first.
  suff : b < b by rewrite ltnn.
  rewrite [X in _ < X]He.
  apply: leq_trans (leq_addr _ _).
  apply: leq_trans (_ : 1 * b ^ (v - i) <= _).
    by rewrite mul1n -[X in X < _]expn1 ltn_exp2l.
  by rewrite leq_mul2r orbC; case: digitn Hd.
have : 0 < digitn b p 0 by case: digitn Hd.
rewrite -nE1 expn1 in He.
rewrite leq_eqVlt => /orP[/eqP nE2|nL]; last first.
  suff : b < b by rewrite ltnn.
  rewrite [X in _ < X]He.
  apply: leq_trans (leq_addr _ _).
  by rewrite -[X in X < _]mul1n ltn_mul2r ltnW.
rewrite -nE2 mul1n in He.
move/eqP : He; rewrite -[X in X == _](addn0 b) eqn_add2l eq_sym.
rewrite sum_nat_seq_eq0 => /allP/= Hi.
suff pE1 : p == 1 by rewrite (eqP pE1) in pP.
pose o1 := Ordinal (ltn_trans i_pos iLv).
rewrite [p](digitnE_ndigits _ b_gt1) -/v (bigD1 o1) //=.
rewrite -nE2 muln1 -[X in _ == X]addn0 eqn_add2l sum_nat_seq_eq0.
apply/allP => /= [] [k Hk] /= _.
apply/implyP => /eqP/val_eqP /= k_neq0 //.
have FO3 : k.+1 %% v < v by rewrite ltn_mod.
have : digitn b p ((i + k.+1 %% v) %% v) * b ^ (k.+1 %% v) == 0.
  have /= := Hi (Ordinal FO3).
  rewrite mem_index_enum => /(_ isT)/implyP->//.
  apply/eqP/val_eqP=> /=.
  rewrite -nE1.
  move: Hk; rewrite leq_eqVlt => /orP[/eqP->|kLv]; first by rewrite modnn.
  by rewrite modn_small //; case: (k) k_neq0.
suff -> : ((i + k.+1 %% v) %% v) = k.
  rewrite muln_eq0; case: eqP => [->|] //.
  have: 0 < b ^ (k.+1 %% v) by rewrite expn_gt0 // ltnW.
  by case: (_ ^ _).
rewrite modnDmr -add1n addnA [_ + 1]addnC nE1 subnK 1?ltnW //.
by rewrite -modnDml modnn add0n modn_small.
Qed.

(* Some facts about circular numbers in base 10 *)


Let v11939 := Eval compute in N.to_nat 11939.
Let v19937 := Eval compute in N.to_nat 19937.
Let v193939 := N.to_nat 193939.
Let v199933 := N.to_nat 199933.

(* the first circular primes in base 10 *)
Lemma first_ten_cprimes : 
  all (cprime 10) [:: 2; 3; 5; 7; 11; 13; 17; 37; 79; 113; 197; 199; 337; 
                 1193; 3779; v11939; v19937; v193939; v199933].
Proof.
by vm_cast_no_check (refl_equal true).
Time Qed.

(* there is no zero digit *)
Lemma cprime10_digit0 p i : 
  cprime 10 p -> digitn 10 p i = 0 -> (ndigits 10 p <= i).
Proof.
move=> pCP /(cprime_digit0 (isT : 1 < 10) pCP)/orP[//|/eqP p10].
by rewrite p10 in pCP.
Qed.

(* 2 is the only circular prime that has 2 as a digit *)
Lemma cprime10_digit2 p i :  cprime 10 p -> digitn 10 p i = 2 -> p = 2.
Proof. by apply: cprime_digit_gcd. Qed.

(* a circular prime has no 4 as a digit *)
Lemma cprime10_digit4 p i : cprime 10 p -> digitn 10 p i != 4.
Proof.
move=> cP; apply/eqP => d4.
have [//|/negP[]] := boolP (prime 4).
by rewrite -(cprime_digit_gcd _ _ _ cP d4) // (cprime_prime _ cP).
Qed.

(* 5 is the only circular prime that has 5 as a digit *)
Lemma cprime10_digit5 p i : cprime 10 p -> digitn 10 p i = 5 -> p = 5.
Proof. by apply: cprime_digit_gcd. Qed.

(* a circular prime has no 6 as a digit *)
Lemma cprime10_digit6 p i : cprime 10 p -> digitn 10 p i != 6.
Proof.
move=> cP; apply/eqP => d6.
have [//|/negP[]] := boolP (prime 6).
by rewrite -(cprime_digit_gcd _ _ _ cP d6) // (cprime_prime _ cP).
Qed.

(* a circular prime has no 8 as a digit *)
Lemma cprime10_digit8 p i : cprime 10 p -> digitn 10 p i != 8.
Proof.
move=> cP; apply/eqP => d8.
have [//|/negP[]] := boolP (prime 8).
by rewrite -(cprime_digit_gcd _ _ _ cP d8) // (cprime_prime _ cP).
Qed.

Lemma cprime10_digits p i : 
  cprime 10 p -> 5 < p -> i < ndigits 10 p -> digitn 10 p i \in [:: 1; 3; 7; 9].
Proof.
move=> pCP fLp iLn.
have : digitn 10 p i < 10 by rewrite ltn_digitn.
rewrite leq_eqVlt eqSS => /orP[/eqP->|]; first by rewrite inE.
rewrite ltnS leq_eqVlt eqSS => /orP[|].
  by rewrite (negPf (cprime10_digit8 _ _)).
rewrite ltnS leq_eqVlt eqSS => /orP[/eqP->|]; first by rewrite inE.
rewrite ltnS leq_eqVlt eqSS => /orP[|].
  by rewrite (negPf (cprime10_digit6 _ _)).
rewrite ltnS leq_eqVlt eqSS => /orP[/eqP|].
  by move=> /(cprime10_digit5 pCP) pE5; rewrite pE5 in fLp.
rewrite ltnS leq_eqVlt eqSS => /orP[|].
  by rewrite (negPf (cprime10_digit4 _ _)).
rewrite ltnS leq_eqVlt eqSS => /orP[/eqP->|]; first by rewrite inE.
rewrite ltnS leq_eqVlt eqSS => /orP[/eqP|].
  by move=> /(cprime10_digit2 pCP) pE2; rewrite pE2 in fLp.
rewrite ltnS leq_eqVlt eqSS => /orP[/eqP->|]; first by rewrite inE.
rewrite ltnS leq_eqVlt eqSS => /orP[/eqP dE0|//].
move: iLn; rewrite ltnNge => /negP[].
by apply: cprime10_digit0.
Qed.

End Cprime.

Check first_ten_cprimes.
