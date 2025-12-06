From mathcomp Require Import all_boot.
Require Import nicomachus.

(******************************************************************************)
(*            Liouville theorem about number's divisors                       *) 
(*          The proof uses a corollary of  Nicomachus Theorem                 *)
(*                                                                            *)
(* is_nmul F     : F is multiplicative F (m * n) = F m * F n for m n coprimes *)
(* ndivisors n   : the number of divisors of n, ndivisors 10 = 4              *)
(*                                                                            *)
(******************************************************************************)


Definition is_nmul F := forall m n, coprime m n -> F (m * n) = F m * F n.

Lemma is_nmul_eq F1 F2 : F1 =1 F2 -> is_nmul F1 -> is_nmul F2.
Proof. by move=> FE H1 m n mCn; rewrite -!FE H1. Qed.

Lemma is_nmulM F G : is_nmul F -> is_nmul G -> is_nmul (fun n => F n * G n).
Proof.
move=> HF HG m n mCn.
by rewrite HF // HG // !mulnA; congr (_ * _); rewrite mulnAC.
Qed.

Lemma is_nmulX F n : is_nmul F -> is_nmul (fun m => (F m) ^ n).
Proof.
move=> HF; elim: n => // n IH.
apply: (is_nmul_eq (fun m => F m * F m ^ n)); first by move=> m; rewrite expnS.
by apply: is_nmulM.
Qed.

Lemma coprime_gcdnM i m n :
  coprime m n -> i %| m * n -> i = gcdn i m * gcdn i n.
Proof.
have [j jLi] := ubnP i.
elim: j i jLi m n => [[_ m n mCn|//]|j IH i jLi m n mCn].
  by rewrite dvd0n muln_eq0 => /orP[]/eqP->; rewrite gcdnn ?muln0.
have [|//|<-] := ltngtP 0 i; last by rewrite !gcd0n dvd0n => /eqP.
have [i_gt1|//|<-] := ltngtP 1 i; last by rewrite !gcd1n.
have /pdivP[p pP /dvdnP[i' i'E]] := i_gt1.
rewrite {}i'E ?ltnS in jLi i_gt1 * => _ i'pDmn.
have : p %| m * n by apply: dvdn_trans (dvdn_mull _ (dvdnn _)) i'pDmn.
wlog : m n mCn i'pDmn / p %| m => [H pDmn|/dvdnP[k kE] _].
  have := pDmn; rewrite Euclid_dvdM // => /orP[] pDm; first by apply: H.
  rewrite [RHS]mulnC.
  by apply: H; rewrite 1?[n * _]mulnC // coprime_sym.
rewrite {}kE in mCn i'pDmn *.
rewrite -muln_gcdl mulnAC; congr (_ * _).
rewrite [X in _ * X]gcdnC Gauss_gcdl 1?[X in _ * X]gcdnC; last first.
  by have := mCn; rewrite coprimeMl => /andP[_]; rewrite coprime_sym.
apply: IH => //.
- apply: leq_trans jLi.
  by rewrite -[X in X < _]muln1 ltn_mul2l prime_gt1 //; case: (i') i_gt1.
- by have := mCn; rewrite coprimeMl; case/andP.
by rewrite -(dvdn_pmul2l (prime_gt0 pP)) mulnC mulnCA mulnA.
Qed.

Lemma divisors_prime_eq p : prime p = (divisors p == [::1 ; p]).
Proof.
case: p => // [] [//|p]; apply/primeP/eqP => Hp; last first.
  by split => // d; rewrite dvdn_divisors // Hp !inE.
apply: sorted_eq (sorted_divisors_ltn _) _ _ => //; first by apply: ltn_trans.
  by move=> i j /=; case: (ltngtP i j).
have {Hp}[_ Hp] := Hp.
apply: uniq_perm (divisors_uniq _) _ _ => // i.
rewrite -dvdn_divisors // !inE.
by apply/idP/idP=> [/Hp//|]; case/orP => /eqP->; rewrite ?dvd1n ?dvdnn.
Qed.


Lemma divisors_primeX p n :
  prime p -> divisors (p ^ n) = [seq p ^ i | i <- iota 0 n.+1].
Proof.
move=> pP.
have p_gt1 := prime_gt1 pP.
apply: sorted_eq (sorted_divisors_ltn _) _ _ => //; first by apply: ltn_trans.
- by move=> i j /=; case: (ltngtP i j).
- apply/(sortedP 0) => [] [//|i]; rewrite size_map size_iota ltnS => iLn /=.
    by case: n iLn.
  have i1Ln : i < n by apply: leq_ltn_trans iLn.
  by rewrite !(nth_map 0) ?size_iota // !nth_iota // !add1n ltn_exp2l.
apply: uniq_perm (divisors_uniq _) _ _ => [|i].
  rewrite map_inj_uniq ?iota_uniq // => i j /eqP.
  by rewrite eqn_exp2l // => /eqP.
rewrite -dvdn_divisors ?expn_gt0 ?prime_gt0 //.
apply/(dvdn_pfactor _ _ pP)/idP => [[m mLn ->]|/mapP[m Hm ->]].
  by apply: map_f; rewrite mem_iota.
by exists m => //; rewrite mem_iota in Hm.
Qed.

Lemma divisorsM m n : 
  coprime m n ->
  divisors (m * n) = sort leq [seq x * y  | x <- divisors m,  y <- divisors n].
Proof.
move=> mCn.
have [mE0|/eqP m_gt0] := m =P 0.
  by rewrite mE0 /= in mCn *; rewrite /coprime gcd0n in mCn; rewrite (eqP mCn).
have [nE0|/eqP n_gt0] := n =P 0.
  by rewrite nE0 /= in mCn *; rewrite /coprime gcdn0 in mCn; rewrite (eqP mCn).
rewrite -!lt0n in m_gt0 n_gt0.
set u := [seq _ | _ <- _, _ <- _].
have uU : uniq u.
  apply: allpairs_uniq; try apply: divisors_uniq.
  move=> /= [i1 j1] [i2 j2] /= /allpairsP [[/= m1 n1 [m1D n1D [-> ->]]]] 
            /allpairsP [[/= m2 n2 [m2D n2D [-> ->]]]] m1n1Em2n2.
  have m1Cn2 : coprime m1 n2.
    rewrite -!dvdn_divisors // in  m1D m2D n1D n2D.
    by apply: coprime_dvdl m1D _; apply: coprime_dvdr n2D _.
  have m2Cn1 : coprime m2 n1.
    rewrite -!dvdn_divisors // in  m1D m2D n1D n2D.
    by apply: coprime_dvdl m2D _; apply: coprime_dvdr n1D _.
  apply/eqP/andP; split; rewrite /= eqn_dvd.
    rewrite -(Gauss_dvdl _ m1Cn2) -m1n1Em2n2 dvdn_mulr ?divnn //=.
    by rewrite -(Gauss_dvdl _ m2Cn1) m1n1Em2n2 dvdn_mulr ?divnn.
  rewrite -(@Gauss_dvdr _ m2) 1?coprime_sym // -m1n1Em2n2 dvdn_mull ?divnn //=.
  by rewrite -(@Gauss_dvdr _ m1) 1?coprime_sym // m1n1Em2n2 dvdn_mull ?divnn.
apply: (sorted_eq leq_trans).
- by move=> x y; case: ltngtP.
- by apply: sorted_divisors.
- by apply: sort_sorted; move=> x y; case: ltngtP.
apply: uniq_perm => //; first by apply: divisors_uniq.
  by rewrite sort_uniq.
move=> /= i; rewrite -dvdn_divisors ?muln_gt0 ?m_gt0 // mem_sort.
apply/idP/allpairsP=> [iDmn|[[i1 j1] [] /=]]; last first.
  rewrite -!dvdn_divisors // => i1Dm j1Dn ->.
  by apply: dvdn_mul.
exists (gcdn i m, gcdn i n); rewrite -!dvdn_divisors ?dvdn_gcdl ?dvdn_gcdr //=.
by rewrite -coprime_gcdnM.
Qed.

Lemma big_sort R (op : SemiGroup.com_law R) (x : R) (I : eqType) 
                   (r : seq I) (s : rel I) (P : pred I) (F : I -> R) : 
  \big[op/x]_(i <- sort s r | P i)  F i = \big[op/x]_(i <- r | P i)  F i.
Proof. by apply: perm_big; rewrite  ?perm_sort. Qed.

Lemma big_divisors  R (x : R) (op : SemiGroup.com_law R) (F : nat -> R) n : 
  0 < n -> 
 \big[op/x]_(i <- divisors n)  F i = \big[op/x]_(i < n.+1 | i %| n)  F i.
Proof.
move=> n_gt0.
rewrite -(@big_mkord _ _ _ _ (fun i => i %| n)) -[RHS]big_filter.
apply/perm_big/uniq_perm => [||i]; first by apply: divisors_uniq.
  by apply/filter_uniq/iota_uniq.
rewrite -dvdn_divisors // mem_filter /index_iota mem_iota subn0 ltnS leq0n.
by case: (_ %| _) (@dvdn_leq i _ n_gt0) => // ->.
Qed.

Definition ndivisors n := size (divisors n).

Lemma ndivisors_prime p : prime p -> ndivisors p = 2.
Proof. by rewrite /ndivisors divisors_prime_eq // => /eqP->. Qed.

Lemma ndivisors_primeX p n : prime p -> ndivisors (p ^ n) = n.+1.
Proof.
by move=> pP; rewrite /ndivisors divisors_primeX // size_map size_iota.
Qed.

Lemma ndivisors_is_nmul : is_nmul ndivisors.
Proof.
move=> m n mCn.
by rewrite [in LHS]/ndivisors divisorsM // size_sort size_allpairs.
Qed.

Lemma big_divisorM F m n : 
 coprime m n -> is_nmul F ->
 \sum_(i <- divisors (m * n)) F i = 
 \sum_(i <- divisors m) \sum_(j <- divisors n) F (i * j).
Proof.
by move=> Hcm HF; rewrite divisorsM // big_sort /= big_allpairs_dep_idem //=.
Qed.

Lemma is_nmul_sum F :
  is_nmul F -> is_nmul (fun n => \sum_(i <- divisors n) F i).
Proof.
move=> HF m n mCn.
rewrite big_divisorM // big_distrl /= [LHS]big_seq_cond [RHS]big_seq_cond.
apply: eq_bigr => i; rewrite andbT => Hi.
rewrite big_distrr [LHS]big_seq_cond [RHS]big_seq_cond.
apply: eq_bigr => j; rewrite andbT => Hj.
apply: HF.
case: m mCn Hi Hj => [|m].
  by rewrite /coprime gcd0n => /eqP->; rewrite !inE => /eqP-> /eqP->.
case: n => [|n mCn].
  by rewrite /coprime gcdn0 => /eqP->; rewrite !inE => /eqP-> /eqP->.
rewrite -!dvdn_divisors // => Hi Hj.
by apply: coprime_dvdr Hj (coprime_dvdl Hi _).
Qed.

Lemma liouville_divisors n : 
 \sum_(i <- divisors n) (ndivisors i) ^ 3 = 
 (\sum_(i <- divisors n) (ndivisors i)) ^ 2.
Proof.
pose F n := \sum_(i <- divisors n)  ndivisors i ^ 3; rewrite -/(F n).
have HF : is_nmul F by apply/is_nmul_sum/is_nmulX/ndivisors_is_nmul.
pose G n := (\sum_(i <- divisors n)  ndivisors i) ^ 2; rewrite -/(G n).
have HG : is_nmul G by apply/is_nmulX/is_nmul_sum/ndivisors_is_nmul.
have [m nLm] := ubnP n.
elim: m n nLm => // n IH [|[|m nLm]].
- by rewrite /F /G !big_cons !big_nil.
- by rewrite /F /G !big_cons !big_nil.
have [p pP pDm] := pdivP (isT : 1 < m.+2).
have [k kCm kE] := pfactor_coprime pP (isT : 0 < m.+2).
have kCp1 : coprime k (p ^ logn p m.+2) by apply/coprimeXr; rewrite coprime_sym.
have kLn : k < n.
  rewrite -ltnS (leq_ltn_trans _ nLm) // kE -[X in X < _]muln1 ltn_mul2l.
  case: (k) (kE) => //= _ _.
  by rewrite -[1](expn0 p) ltn_exp2l ?prime_gt1 // -pfactor_dvdn.
rewrite kE HF // HG // IH //; congr (_ * _).
rewrite /F /G divisors_primeX // !big_map.
set u := _.+1.
under eq_bigr do rewrite ndivisors_primeX //.
under [in RHS]eq_bigr do rewrite ndivisors_primeX //.
rewrite -[u]subn0 -[iota _ _]/(index_iota 0 u) !big_mkord.
have := nicomachus u.+1.
by rewrite big_ord_recl [X in _ = X ^ 2 -> _]big_ord_recl !add0n.
Qed.
