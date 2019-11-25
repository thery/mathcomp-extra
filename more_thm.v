(* Theorems to be added to the mathcomp library  *)
From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* in ssrnat *)

Definition sqrtn n := 
  let fix loop (m2 dm1 m k : nat) {struct k} : nat :=
  if k is k1.+1 then
    let m2' := m2 + dm1 in
    if n < m2' then m else 
    loop m2' dm1.+2 m.+1 k1
  else m in loop 0 1 0 n.

Fixpoint divloop (m2 dm1 m k : nat) {struct k} : nat :=
   if k is k1.+1 then
     if m + k < m2 + dm1 then m else divloop (m2 + dm1) dm1.+2 m.+1 k1
   else m.

Lemma divloopE n : sqrtn n = divloop 0 1 0 n.
Proof.
rewrite /sqrtn; move: {1 4}0 => m2; move: 1 => dm1.
rewrite -{1}[n]add0n; move: 0 => m.
elim: n m2 dm1 m => //= n IH m2 dm1 m.
by case: leqP => // _; rewrite -IH addSnnS.
Qed.

Lemma divloop_leq m2 dm1 m k : m <= divloop m2 dm1 m k.
Proof.
elim: k m2 dm1 m => //= k IH m2 dm1 m.
by case: leqP => // _; apply: leq_trans (IH _ _ _).
Qed.

Lemma sqrtSn m : m.+1 ^ 2 = m ^ 2 + m.*2.+1.
Proof. by rewrite -[m.+1]addn1 sqrnD muln1 mul2n -addnA. Qed.

Lemma sqrn_leq_eq1 m : (m ^ 2 <= m) = (m <= 1).
Proof.
case: m => [|[|m]] //=.
by rewrite leqNgt expnS expn1 mulSn -addSnnS leq_addr.
Qed.

Lemma sqrtn_bound n : (sqrtn n) ^ 2 <= n < ((sqrtn n).+1) ^ 2.
Proof.
suff : 
   forall k m, m ^ 2 <= m + k ->
      (divloop (m ^ 2) (m.*2.+1) m k) ^ 2 <= m + k < 
      (divloop (m ^ 2) (m.*2.+1) m k).+1 ^ 2.
  by move/(_ n 0); rewrite divloopE; apply.
elim=> [m -> /=|k IH m /= m2Lmk].
  by rewrite addn0 expnS expn1 mulnS leq_addr.
case: leqP => [m2m21Lmk1|mk1Lm2m21].
  rewrite -[m + k.+1]addSnnS -sqrtSn.
  by apply: IH; rewrite sqrtSn addSnnS.
by rewrite m2Lmk sqrtSn.
Qed.

Lemma sqrtn_leq n x : x ^ 2 <= n -> x <= sqrtn n.
Proof.
suff : 
   forall k m, m <= x -> m ^ 2 <= m + k -> x ^ 2 <= m + k ->
      x <= divloop (m ^ 2) (m.*2.+1) m k.
  by move/(_ n 0); rewrite divloopE; apply.
elim=> [m /=|k IH m /= mLx m2Lmk1 x2Lmk1].
  rewrite addn0 sqrn_leq_eq1.
  by case: m => [|[|]] //; case: x => [|[|]].
(case: leqP; rewrite -sqrtSn)=> [JJ|]; last first.
  by move=> /(leq_ltn_trans x2Lmk1); rewrite ltn_sqr ltnS.
move: mLx; rewrite leq_eqVlt => /orP[/eqP<-|mLx].
  by apply: leq_trans (divloop_leq _ _ _ _).
by apply: IH; rewrite ?addSnnS.
Qed.

Lemma sqrtn_lt n x : n < x.+1 ^ 2 -> sqrtn n <= x.
Proof.
suff : 
   forall k m, m ^ 2 <= m + k ->
      m + k < x.+1 ^ 2 ->
      divloop (m ^ 2) (m.*2.+1) m k <= x.
  by move/(_ n 0); rewrite divloopE; apply.
elim=> /= [m m2Lmk1 mk2Lx12| k IH m m2Lmk1 mk2Lx12].
  by rewrite -ltnS -ltn_sqr (leq_ltn_trans m2Lmk1).
case: leqP; rewrite // -sqrtSn => H.
  by apply: IH; rewrite ?addSnnS.
by rewrite -ltnS -ltn_sqr (leq_ltn_trans m2Lmk1).
Qed.

Lemma sqrtnE n x : x ^ 2 <= n < x.+1^2 -> sqrtn n = x.
Proof.
move=> /andP[/sqrtn_leq xLsn /sqrtn_lt snLx].
by apply/esym/eqP; rewrite eqn_leq xLsn.
Qed.

Lemma leq_sqrtn m n : m <= n -> sqrtn m <= sqrtn n.
Proof.
move=> mLn.
apply: sqrtn_lt.
by have /andP[_ /(leq_ltn_trans _)->//]:= sqrtn_bound n.
Qed.

Lemma sqrnK n : sqrtn (n ^ 2) = n.
Proof. by apply: sqrtnE; rewrite leqnn ltn_sqr // leqnn. Qed.

Definition log2n n := 
  let v := trunc_log 2 n in if n <= 2 ^ v then v else v.+1.

Lemma log2n9 : log2n 0 = 0.
Proof. by []. Qed.

Lemma log2n1 : log2n 1 = 0.
Proof. by []. Qed.

Lemma log2n_eq0 n : (log2n n == 0) = (n <= 1).
Proof.
case: n => [|[|n]]; rewrite /log2n //.
have /= := trunc_log_bounds (isT : 1 < 2) (isT : 0 < n.+2).
by case: (leqP (2 ^ trunc_log 2 n.+2) n.+1).
Qed.

Lemma log2n_gt0 n : (0 < log2n n) = (1 < n).
Proof. by rewrite ltnNge leqn0 log2n_eq0 ltnNge. Qed.

Lemma log2n_bounds n :
   1 < n -> let k := log2n n in 2 ^ k.-1 < n <= 2 ^ k.
Proof.
move=> /= n_gt1.
have n_gt0 : 0 < n by apply: leq_trans n_gt1.
rewrite /log2n.
have /= := trunc_log_bounds (isT : 1 < 2) n_gt0.
case: (leqP n (2 ^ trunc_log 2 n)) => [] H1 /andP[H2 H3].
  rewrite H1 (leq_trans _ H2) // ltn_exp2l // prednK ?leqnn //.
  by case: trunc_log (leq_trans n_gt1 H1).
by rewrite H1 ltnW.
Qed.

Lemma log2nP n : n <= 2 ^ log2n n.
Proof.
case: n => [|[|n]] //.
by have /andP[] := log2n_bounds (isT: 1 < n.+2).
Qed.

Lemma log2n_ltn n : 1 < n ->  2 ^ (log2n n).-1 < n.
Proof.
case: n => [|[|n]] _ //.
by have /andP[] := log2n_bounds (isT: 1 < n.+2).
Qed.

Lemma log2n_max k j : k <= 2 ^ j -> log2n k <= j.
Proof.
case: k => [|[|k]] // kLj.
rewrite -[log2n _]prednK ?log2n_gt0 // -(@ltn_exp2l 2) //.
by apply: leq_trans (log2n_ltn (isT : 1 < k.+2)) _.
Qed.

Lemma leq_log2n m n : m <= n -> log2n m <= log2n n.
Proof. by move=> mLn; apply/log2n_max/(leq_trans _ (log2nP _)). Qed.

Lemma exp2nK n : log2n (2 ^ n) = n.
Proof.
apply/eqP; rewrite eqn_leq.
by rewrite log2n_max //= -(@leq_exp2l 2) log2nP.
Qed.

Import GRing.Theory.
Import Pdiv.CommonRing.
Import Pdiv.RingMonic.

Local Open Scope ring_scope.

(* More on comp_compy *)
Section Rcomp_poly.

Variable R : ringType.

Lemma comp_polyXn n (p : {poly R}) : 'X^n \Po p = p ^+ n.
Proof.
rewrite comp_polyE size_polyXn.
rewrite (bigD1 ord_max) //= coefXn eqxx scale1r big1 ?addr0 //.
by move=> i /eqP/val_eqP /= iDn; rewrite coefXn (negPf iDn) scale0r.
Qed.

Lemma comp_polyXsub1 n : 
  ('X - 1) \Po 'X^n = 'X^n - 1 :> {poly R}.
Proof. by rewrite comp_polyB comp_polyC comp_polyX. Qed.

End Rcomp_poly.

Section Ccomp_poly.

Variable R : comRingType.

Lemma comp_poly_exp n (p q : {poly R}) : (p \Po q) ^+ n = (p ^+ n) \Po q.
Proof.
elim: n => [|n IH]; first by rewrite !expr0 comp_polyC.
by rewrite !exprS IH comp_polyM.
Qed.

End Ccomp_poly.

(* poly *)

Section Poly.

Variable R : ringType.

Lemma size_exp_monic (p: {poly R}) n :
  p \is monic -> size (p ^+ n) = ((size p).-1 * n).+1.
Proof.
move=> pM; elim: n => // [|n IH].
  by rewrite !expr0 muln0 size_polyC oner_eq0.
rewrite exprS size_proper_mul ?IH; last first.
  by rewrite (eqP pM) (eqP (monic_exp n pM)) mul1r oner_neq0.
have : (0 < size p)%nat.
  by have := monic_neq0 pM; rewrite -size_poly_eq0; case: size.
by case: size => // k _; rewrite addSn addnS -mulnS.
Qed.

Lemma monic_comp_poly (p q : {poly R}) :
  p \is monic -> q \is monic -> q != 1 -> p \Po q \is monic.
Proof.
move=> pM qM qD1.
have cp0q : (p \Po q)`_((size p).-1 * (size q).-1) == 1.
  rewrite comp_polyE coef_sum.
  have := (pM); rewrite monicE /lead_coef.
  have : (0 < size p)%nat.
    by have := monic_neq0 pM; rewrite -size_poly_eq0; case: size.
  case: size => //= k _ pkE.
  rewrite big_ord_recr /= (eqP pkE) scale1r big1 ?add0r.
    have := monic_exp k qM.
    by rewrite qualifE /lead_coef size_exp_monic //= mulnC.
  move=> i _; rewrite coefZ [_`_(k * _)]nth_default ?mulr0 //.
  rewrite size_exp_monic // mulnC.
  suff : (1 < size q)%nat.
    by case: size => // [] [|v] //_ ; rewrite ltn_mul2r ltn_ord.
  case E : size => [|[|v]] //.
    have /eqP := E; rewrite size_poly_eq0 => /eqP qE0.
    by move: qM; rewrite qualifE qE0 lead_coefC eq_sym oner_eq0.
  have /eqP/size_poly1P[c cD0 qE] := E.
  by case/eqP: qD1; move: qM; rewrite qE qualifE lead_coefC => /eqP->.
have := size_comp_poly_leq p q.
rewrite qualifE /lead_coef leq_eqVlt => /orP[/eqP-> //|].
rewrite ltnS => sLp; move: cp0q.
by rewrite nth_default // eq_sym oner_eq0.
Qed.

End Poly.

(* rdvdp *)

Section rdvdp.

Variable R : ringType.

Lemma rdvdp_trans (p q r : {poly R}) : 
  p \is monic -> q \is monic -> rdvdp p q -> rdvdp q r -> rdvdp p r.
Proof.
move=> pM qM /rdvdpP => /(_ pM) [qq1 qq1E] /rdvdpP => /(_ qM) [qq2 qq2E].
by apply/rdvdpP => //; exists (qq2 * qq1); rewrite qq2E qq1E mulrA.
Qed.

End rdvdp.

Section Crdvdp.

Variable R : comRingType.

Lemma rdvdp_comp_poly (r p q : {poly R}) : 
 p \is monic -> r \is monic -> r != 1 -> rdvdp p q -> rdvdp (p \Po r) (q \Po r).
Proof.
move=> pM rM rD1 /rdvdpP => /(_ pM) [qq qqE].
apply/rdvdpP; first by apply: monic_comp_poly.
by exists (qq \Po r); rewrite qqE comp_polyM.
Qed.

End Crdvdp.

(* irreducible *)

Section Firreducible.

Variable F : finFieldType.

Definition irreducibleb (p : {poly F}) :=
  (1 < size p)%N && 
  [forall q : (size p).-1.-tuple F, (Poly q %| p) ==> (size (Poly q) <= 1)%N].

Lemma irreducibleP (p : {poly F}) : 
  reflect (irreducible_poly p) (irreducibleb p).
Proof.
rewrite /irreducibleb /irreducible_poly.
apply: (iffP idP) => [/andP[Sp /forallP Fp]|[Sp Fpoly]].
  split => // q SqD1 qDp.
  rewrite -dvdp_size_eqp //.
  have pD0 : p != 0 by rewrite -size_poly_eq0; case: size Sp.
  have: (size q <= size p)%N by apply: dvdp_leq.
  rewrite leq_eqVlt => /orP[//|SqLp].
  have xF : size (q ++ nseq ((size p).-1 - size q) 0) == (size p).-1.
    by rewrite size_cat size_nseq addnC subnK //;  case: size Sp SqLp.
  have /implyP/= := Fp (Tuple xF).
  rewrite (_ : Poly _ = q) // => [/(_ qDp)|].
    case E : size SqD1 qDp => [|[|k]] //.
    have /eqP  := E. 
    rewrite size_poly_eq0 => /eqP-> _; rewrite dvd0p => /eqP->.
    by rewrite size_polyC eqxx.
  apply/polyP => i; rewrite coef_Poly nth_cat.
  by case: leqP => qLi //; first by rewrite nth_nseq if_same nth_default.
rewrite Sp /=; apply/forallP => q; apply/implyP=> qDp.
have [/eqP->//|/Fpoly/(_ qDp)/eqp_size ES] := boolP (size (Poly q) == 1%N).
have := size_Poly q; rewrite ES size_tuple.
by case: size Sp => // k; rewrite ltnn.
Qed.

Lemma irreducible_dvdp (p : {poly F}) :
  (1 < size p)%N -> exists2 q, irreducible_poly q & q %| p.
Proof.
elim: {p}_.+1 {-2}p  (ltnSn (size p)) => // k IH p SpLk Sp_gt1.
have [/irreducibleP pI|] := boolP (irreducibleb p); first by exists p.
rewrite /irreducibleb Sp_gt1 negb_forall => /existsP[q].
rewrite negb_imply -ltnNge => /andP[qDp Sq_gt1].
case: (IH _ _ Sq_gt1) => [|r rI rDq].
  apply: leq_ltn_trans (size_Poly _) _.
  by rewrite size_tuple; case: size SpLk Sp_gt1.
exists r => //.
by apply: dvdp_trans qDp.
Qed.

Section irreducible.

Variable R : idomainType.

Lemma irreducible_exp n (p q : {poly R}) :
  irreducible_poly p -> (0 < n)%N -> p %| q ^+ n = (p %| q).
Proof.
move=> pI.
elim: n => // [] [|n] // /(_ isT) IH _.
apply/idP/idP; rewrite exprS; last first.
  by move=> /dvdp_trans; apply; apply: dvdp_mulr.
have [pCq|pNCq] := boolP (coprimep p q); first by rewrite Gauss_dvdpr // IH.
have /(irredp_XsubCP pI)[pCq|/andP[_ pDg] _] : gcdp p q %| p.
- by rewrite dvdp_gcdl.
- by case/negP: pNCq; rewrite /coprimep size_poly_eq1.
by apply: dvdp_trans pDg (dvdp_gcdr _ _).
Qed. 

End irreducible.

End Firreducible.

(* Separable *)

Section separable.

Lemma separable_exp (F : finFieldType) n (p q : {poly F}) :
  separable_poly p -> (0 < n)%N -> p %| q ^+ n = (p %| q).
Proof.
case: n => // n pS _.
apply/idP/idP; last first.
  by rewrite exprS => /dvdp_trans; apply; apply: dvdp_mulr.
elim: {p}_.+1 {-2}p (ltnSn (size p)) pS => // k IH p SpLk pS pDqn.
have [|Sp_gt1] := leqP (size p) 1.
  rewrite leq_eqVlt => /orP[].
    rewrite size_poly_eq1 => /andP[/dvdp_trans-> //].
    by apply: dvd1p.
  rewrite ltnS leqn0 size_poly_eq0 => /eqP pZ.
  by move: pDqn; rewrite pZ dvd0p expf_eq0 //= => /eqP->.
have [r rI rDq] := irreducible_dvdp Sp_gt1.
have /dvdpP[s pE] := rDq.
have sDp : s %| p by rewrite pE dvdp_mulr.
have rCs : coprimep s r by apply: separable_coprime  pS _; rewrite -pE.
rewrite pE Gauss_dvdp //; apply/andP; split; last first.
  by rewrite -(@irreducible_exp _ n.+1) // (dvdp_trans _ pDqn).
apply: IH; last 2 first.
- by apply: dvdp_separable pS; rewrite pE dvdp_mulr.
- by rewrite (dvdp_trans _ pDqn).
rewrite -(ltn_add2r (size r)) -[(_ + size _)%N]prednK; last first.
  by case: rI; case: size => // k1; rewrite addnS.
rewrite -size_mul; last by apply: irredp_neq0.
  rewrite -pE (leq_trans _ (_ : (k + 2 <= _)%N)) //.
    by rewrite !addnS addn0 ltnS.
  by rewrite leq_add2l; case: rI.
apply: separable_poly_neq0.
by apply: dvdp_separable pS; rewrite pE dvdp_mulr.
Qed.

Lemma separable_polyXnsub1 (R : fieldType) n :
 n%:R != 0 :> R -> separable_poly ('X^n - 1 : {poly R}).
Proof.
move=> nC.
have n_gt0 : (0 < n)%N by case: n nC => //; rewrite eqxx.
rewrite /separable_poly !derivE subr0.
suff ->: 'X^n - 1 = (n%:R^-1 *: 'X) * ('X^n.-1 *+ n) + (-1) :> {poly R}.
  rewrite coprimep_sym coprimep_addl_mul.
  by rewrite -scaleN1r coprimep_scaler ?coprimep1 // oppr_eq0 oner_eq0.
rewrite -scaler_nat scalerCA scalerA mulVf //.
by rewrite scale1r -exprS prednK.
Qed.

End separable.

(*  About rmodp and monic *)

Section Rmodp.

Variable R : ringType.

Lemma rmodp_mod (d p : {poly R}) :
  d \is monic -> rmodp (rmodp p d) d = rmodp p d.
Proof.
by move=> dM; rewrite rmodp_small // ltn_rmodpN0 // monic_neq0.
Qed.

Lemma rmodp_opp (d p : {poly R}) : d \is monic -> rmodp (- p) d = - rmodp p d.
Proof.
move=> dM.
rewrite {1}(rdivp_eq dM p) opprD // -mulNr rmodp_addl_mul_small //.
by rewrite size_opp ltn_rmodp //monic_neq0.
Qed.

Lemma rmodp_sub (d p q : {poly R}) : 
  d \is monic -> rmodp (p - q) d = (rmodp p d - rmodp q d)%R.
Proof. by move=> dM; rewrite rmodp_add // rmodp_opp. Qed.

Lemma rmodp_scale (d : {poly R}) a p :
  d \is monic -> rmodp (a *: p) d = a *: (rmodp p d).
move=> dM. 
case: (altP (a =P 0%R)) => [-> | cn0]; first by rewrite !scale0r rmod0p.
have -> : ((a *: p) = (a *: (rdivp p d)) * d + a *: (rmodp p d))%R.
  by rewrite -scalerAl -scalerDr -rdivp_eq.
rewrite  rmodp_addl_mul_small //.
rewrite -mul_polyC; apply: leq_ltn_trans (size_mul_leq _ _) _.
  rewrite size_polyC cn0 addSn add0n /= ltn_rmodp.
by apply: monic_neq0.
Qed.

Lemma rmodp_sum (I : Type) (r : seq I) (P : pred I) (F : I -> {poly R}) d :
   d \is monic ->
   rmodp (\sum_(i <- r | P i) F i) d = (\sum_(i <- r | P i) (rmodp (F i) d)).
Proof.
move=> dM.
by elim/big_rec2: _ => [|i p q _ <-]; rewrite ?(rmod0p, rmodp_add).
Qed.

Lemma coef_comp_poly (p q : {poly R}) n :
  (p \Po q)`_n = \sum_(i < size p) p`_i * (q ^+ i)`_n.
Proof. by rewrite comp_polyE coef_sum; apply: eq_bigr => i; rewrite coefZ. Qed.

End Rmodp.

Section CRmodp.

Variable R : comRingType.

Lemma rmodp_mulml (p q r : {poly R}) :
  r \is monic -> rmodp (rmodp p r * q) r = rmodp (p * q) r.
Proof. by move=> dM; rewrite [in LHS]mulrC [in RHS]mulrC rmodp_mulmr.
Qed.

Lemma rmodp_exp (p q : {poly R}) n :
  q \is monic -> rmodp ((rmodp p q) ^+ n) q = rmodp (p ^+ n) q.
Proof.
move=> qM; elim: n => [|n IH]; first by rewrite !expr0.
rewrite !exprS -rmodp_mulmr // IH rmodp_mulmr //.
by rewrite mulrC rmodp_mulmr // mulrC.
Qed.

Lemma rmodp_compr (p q d : {poly R}) :
  d \is monic -> rmodp (p \Po (rmodp q d)) d = (rmodp (p \Po q) d).
Proof.
move=> dM.
elim/poly_ind: p => [|p c IH].
  by rewrite !comp_polyC !rmod0p.
rewrite !comp_polyD !comp_polyM addrC rmodp_add //.
 rewrite mulrC -rmodp_mulmr // IH rmodp_mulmr //.
 rewrite !comp_polyX !comp_polyC.
by rewrite mulrC rmodp_mulmr // -rmodp_add // addrC.
Qed.

End CRmodp.

(* natmul *)
Section natmul.

Variable R : ringType.

Lemma poly_natmul p : p%:R%:P = p%:R :> {poly R}.
Proof. by elim: p => //= p IH; rewrite !mulrS -IH polyC_add. Qed.

End natmul.

(* charpoly *)
Section charpoly.

Variable R : ringType.

Lemma char_poly : [char {poly R}] =i [char R].
Proof.
move=> p; rewrite !inE; congr (_ && _).
apply/eqP/eqP=> [/(congr1 val) /=|]; last by rewrite -poly_natmul => ->.
by rewrite polyseq0 -poly_natmul polyseqC; case: eqP.
Qed.

End charpoly.

(* horner *)

Section horner.

Variable R : ringType.

Lemma hornerXn n (x : R) : ('X^n).[x] = x^+ n.
Proof.
elim: n=> [|n IH]; rewrite ?exprS ?expr0 ?hornerE //.
by rewrite  -commr_polyX hornerMX IH -exprSr exprS.
Qed.

End horner.

Section alreadyin.

Variable R : idomainType.
Implicit Type p : {poly R}.

Theorem max_poly_roots p rs :
  p != 0 -> all (root p) rs -> uniq rs -> (size rs < size p)%N.
Proof.
elim: rs p => [p pn0 _ _ | r rs ihrs p pn0] /=; first by rewrite size_poly_gt0.
case/andP => rpr arrs /andP [rnrs urs]; case/factor_theorem: rpr => q epq.
case: (altP (q =P 0)) => [q0 | ?]; first by move: pn0; rewrite epq q0 mul0r eqxx.
have -> : size p = (size q).+1.
   by rewrite epq size_Mmonic ?monicXsubC // size_XsubC addnC.
suff /eq_in_all h : {in rs, root q =1 root p} by apply: ihrs => //; rewrite h.
move=> x xrs; rewrite epq rootM root_XsubC orbC; case: (altP (x =P r)) => // exr.
by move: rnrs; rewrite -exr xrs.
Qed.

Lemma roots_geq_poly_eq0 p (rs : seq R) : all (root p) rs -> uniq rs ->
  (size rs >= size p)%N -> p = 0.
Proof. by move=> ??; apply: contraTeq => ?; rewrite leqNgt max_poly_roots. Qed.

End alreadyin.

Section FinField.

(* We extract a part of *)
Lemma Fp_splittingField p d : prime p -> (0 < d)%N ->
  {L: splittingFieldType 'F_p | #|FinFieldExtType L| = (p ^ d)%N}.
Proof.
move=> pP d_gt0.
pose m := (p ^ d)%N.
have m_gt1: (m > 1)%N by rewrite (ltn_exp2l 0) ?prime_gt1.
have m_gt0 := ltnW m_gt1; have m1_gt0: (m.-1 > 0)%N by rewrite -ltnS prednK.
pose q := 'X^m - 'X; have Dq R: q R = ('X^m.-1 - 1) * ('X - 0).
  by rewrite subr0 mulrBl mul1r -exprSr prednK.
have /FinSplittingFieldFor[/= L splitLq]: q [ringType of 'F_p] != 0.
  by rewrite Dq monic_neq0 ?rpredM ?monicXsubC ?monic_Xn_sub_1.
rewrite [map_poly _ _]rmorphB rmorphX /= map_polyX -/(q L) in splitLq.
exists L.
have charL: p \in [char L] by rewrite char_lalg char_Fp .
have /finField_galois_generator[/= a Ca Da]: (1 <= {:L})%VS by apply: sub1v.
pose Em := fixedSpace (a ^+ d)%g. rewrite //= dimv1 expn1 in Da.
have{splitLq} [zs DqL defL] := splitLq.
have Uzs: uniq zs.
  rewrite -separable_prod_XsubC -(eqp_separable DqL) Dq separable_root andbC.
  rewrite /root !hornerE subr_eq0 eq_sym hornerXn expr0n gtn_eqF ?oner_eq0 //.
  rewrite cyclotomic.separable_Xn_sub_1 // -subn1 natrB // subr_eq0.
  by rewrite natrX charf0 // expr0n gtn_eqF // eq_sym oner_eq0.
have in_zs: zs =i Em.
  move=> z; rewrite -root_prod_XsubC -(eqp_root DqL) (sameP fixedSpaceP eqP).
  rewrite /root !hornerE subr_eq0 /= hornerXn /m; congr (_ == z).
  elim: (d) => [|i IHi]; first by rewrite gal_id.
  by rewrite expgSr expnSr exprM IHi galM ?Da ?memvf ?card_Fp.
have defEm: Em = {:L}%VS.
  apply/eqP; rewrite eqEsubv subvf -defL -[Em]subfield_closed agenvS //.
  by rewrite subv_add sub1v; apply/span_subvP=> z; rewrite in_zs.
have/eq_card-> : FinFieldExtType L =i zs.
  by move=> z; rewrite in_zs defEm memvf.
apply: succn_inj.
rewrite (card_uniqP _) //= -(size_prod_XsubC _ id).
by rewrite -(eqp_size DqL) size_addl size_polyXn // size_opp size_polyX.
Qed.

Lemma PrimePowerField p k (m := (p ^ k)%N) :
  prime p -> (0 < k)%N -> {Fm : finFieldType | p \in [char Fm] & #|Fm| = m}.
Proof.
move=> pP k_gt0.
have [L LC] := Fp_splittingField pP k_gt0.
have charL: p \in [char L] by rewrite char_lalg char_Fp.
by exists (FinFieldExtType L).
Qed.

End FinField.