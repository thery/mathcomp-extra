From mathcomp Require Import all_boot.

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

Definition ndivisors n := size (divisors n).

Lemma ndivisorsM m n :
  coprime m n -> ndivisors (m * n) = ndivisors m * ndivisors n.
Proof.
by move=> mCn; rewrite [in LHS]/ndivisors divisorsM // size_sort size_allpairs.
Qed.
