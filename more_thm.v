(* Theorems to be added to the mathcomp library  *)
From mathcomp Require Import all_ssreflect all_fingroup all_field.
From mathcomp Require Import ssralg finalg poly polydiv zmodp vector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GRing.Theory.
Import Pdiv.CommonRing.
Import Pdiv.RingMonic.

Local Open Scope ring_scope.

Lemma inZp0 p : inZp 0 = 0 :> 'Z_p.
Proof. by apply/val_eqP; rewrite /= mod0n. Qed.

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
Proof. by rewrite rmorphXn. Qed.

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
  (1 < size p) && 
  [forall q : (size p).-1.-tuple F, (Poly q %| p) ==> (size (Poly q) <= 1)].

Lemma irreducibleP (p : {poly F}) : 
  reflect (irreducible_poly p) (irreducibleb p).
Proof.
rewrite /irreducibleb /irreducible_poly.
apply: (iffP idP) => [/andP[Sp /forallP Fp]|[Sp Fpoly]].
  split => // q SqD1 qDp.
  rewrite -dvdp_size_eqp //.
  have pD0 : p != 0 by rewrite -size_poly_eq0; case: size Sp.
  have: size q <= size p by apply: dvdp_leq.
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
  1 < size p -> exists2 q, irreducible_poly q & q %| p.
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

End Firreducible.

Section irreducible.

Variable R : idomainType.

Lemma irreducible_exp n (p q : {poly R}) :
  irreducible_poly p -> 0 < n -> p %| q ^+ n = (p %| q).
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

(* Separable *)

Section separable.

Lemma separable_exp (F : finFieldType) n (p q : {poly F}) :
  separable_poly p -> 0 < n -> p %| q ^+ n = (p %| q).
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
  rewrite -pE (leq_trans _ (_ : (k + 2 <= _))) //.
    by rewrite !addnS addn0 ltnS.
  by rewrite leq_add2l; case: rI.
apply: separable_poly_neq0.
by apply: dvdp_separable pS; rewrite pE dvdp_mulr.
Qed.

Lemma separable_polyXnsub1 (R : fieldType) n :
 n%:R != 0 :> R -> separable_poly ('X^n - 1 : {poly R}).
Proof.
move=> nC.
have n_gt0 : 0 < n by case: n nC => //; rewrite eqxx.
rewrite /separable_poly !derivE subr0.
suff ->: 'X^n - 1 = (n%:R^-1 *: 'X) * ('X^n.-1 *+ n) + (-1) :> {poly R}.
  rewrite coprimep_sym coprimep_addl_mul.
  by rewrite -scaleN1r coprimepZr ?coprimep1 // oppr_eq0 oner_eq0.
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

Lemma rmodpB (d p q : {poly R}) : 
  d \is monic -> rmodp (p - q) d = (rmodp p d - rmodp q d)%R.
Proof. by move=> dM; rewrite rmodpD // rmodp_opp. Qed.

Lemma rmodpZ (d : {poly R}) a p :
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
by elim/big_rec2: _ => [|i p q _ <-]; rewrite ?(rmod0p, rmodpD).
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

Lemma rmodpX (p q : {poly R}) n :
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
rewrite !comp_polyD !comp_polyM addrC rmodpD //.
 rewrite mulrC -rmodp_mulmr // IH rmodp_mulmr //.
 rewrite !comp_polyX !comp_polyC.
by rewrite mulrC rmodp_mulmr // -rmodpD // addrC.
Qed.

End CRmodp.

(* natmul *)
Section natmul.

Variable R : ringType.

Lemma poly_natmul p : p%:R%:P = p%:R :> {poly R}.
Proof. by elim: p => //= p IH; rewrite !mulrS -IH polyCD. Qed.

Lemma scale_polyC a b : a *: b%:P = (a * b)%:P :> {poly R}.
Proof. by rewrite -mul_polyC polyCM. Qed.

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


Section alreadyin.

Variable R : idomainType.
Implicit Type p : {poly R}.

Theorem max_poly_roots p rs :
  p != 0 -> all (root p) rs -> uniq rs -> size rs < size p.
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
  size rs >= size p -> p = 0.
Proof. by move=> ??; apply: contraTeq => ?; rewrite leqNgt max_poly_roots. Qed.

End alreadyin.

Section FinField.

(* We extract a part of PrimePowerField *)
Lemma Fp_splittingField d p : prime p -> 0 < d ->
  {L: splittingFieldType 'F_p | #|FinFieldExtType L| = p ^ d}.
Proof.
move=> pP d_gt0.
have p_gt1 := prime_gt1 pP.
pose m := p ^ d.
have m_gt1: m > 1 by rewrite (ltn_exp2l 0) ?prime_gt1.
have m_gt0 := ltnW m_gt1; have m1_gt0: m.-1 > 0 by rewrite -ltnS prednK.
pose q := 'X^m - 'X; have Dq R: q R = ('X^m.-1 - 1) * ('X - 0).
  by rewrite subr0 mulrBl mul1r -exprSr prednK.
have /FinSplittingFieldFor[/= L splitLq]: q [ringType of 'F_p] != 0.
  by rewrite Dq monic_neq0 ?rpredM ?monicXsubC ?monic_Xn_sub_1.
rewrite [map_poly _ _]rmorphB rmorphXn /= map_polyX -/(q L) in splitLq.
exists L.
have charL: p \in [char L] by  rewrite char_lalg /= char_Fp.
have /finField_galois_generator[/= a Ca Da]: (1 <= {:L})%VS by apply: sub1v.
pose Em := fixedSpace (a ^+ d)%g. rewrite //= dimv1 expn1 in Da.
have{splitLq} [zs DqL defL] := splitLq.
have Uzs: uniq zs.
  rewrite -separable_prod_XsubC -(eqp_separable DqL) Dq separable_root andbC.
  rewrite /root !hornerE subr_eq0 eq_sym expr0n gtn_eqF ?oner_eq0 //.
  rewrite cyclotomic.separable_Xn_sub_1 // -subn1 natrB // subr_eq0.
  by rewrite natrX charf0 // expr0n gtn_eqF // eq_sym oner_eq0.
have in_zs: zs =i Em.
  move=> z; rewrite -root_prod_XsubC -(eqp_root DqL) (sameP fixedSpaceP eqP).
  rewrite /root !hornerE subr_eq0 /= /m; congr (_ == z).
  elim: (d) => [|i IHi]; first by rewrite gal_id.
  by rewrite expgSr expnSr exprM IHi galM ?Da ?memvf // card_Fp.
have defEm: Em = {:L}%VS.
  apply/eqP; rewrite eqEsubv subvf -defL -[Em]subfield_closed agenvS //.
  by rewrite subv_add sub1v; apply/span_subvP=> z; rewrite in_zs.
have/eq_card-> : FinFieldExtType L =i zs.
  by move=> z; rewrite in_zs defEm memvf.
apply: succn_inj.
rewrite (card_uniqP _) //= -(size_prod_XsubC _ id).
by rewrite -(eqp_size DqL) size_addl size_polyXn // size_opp size_polyX.
Qed.

Lemma PrimePowerField p k (m := (p ^ k)) :
  prime p -> 0 < k -> {Fm : finFieldType | p \in [char Fm] & #|Fm| = m}.
Proof.
move=> pP k_gt0.
have [L LC] := Fp_splittingField pP k_gt0.
have charL: p \in [char L] by rewrite char_lalg char_Fp.
by exists (FinFieldExtType L).
Qed.

End FinField.

Lemma fin_little_fermat (F : finFieldType) (n c : nat) :
  n \in [char F] -> c%:R ^+ n = c%:R :> F.
Proof.
move=> nC.
have Pp : prime n by apply: charf_prime nC.
have Cn : [char F].-nat n by rewrite pnatE.
elim: c => [|c IH]; first by rewrite -natrX exp0n ?prime_gt0.
by rewrite -addn1 natrD exprDn_char // IH -natrX exp1n.
Qed.

Lemma poly_geom (R : comRingType) n (p : {poly R}) : 
  p ^+ n.+1 - 1 = (p - 1) * \sum_(i < n.+1) p ^+ i.
Proof.
rewrite mulrBl mul1r {1}big_ord_recr big_ord_recl /=.
rewrite [_ + p^+_]addrC mulrDr -exprS expr0 addrAC opprD addrA mulr_sumr.
rewrite (eq_bigr (fun i : 'I_n => p * p ^+ i)) ?subrK // => i _.
by rewrite exprS.
Qed.

Lemma dvdp_geom (R : comRingType) n (p : {poly R}) :
  p - 1 \is monic -> rdvdp (p - 1) (p ^+ n.+1 - 1).
Proof. move=> pM; rewrite poly_geom mulrC rdvdp_mull //. Qed.

Lemma totient_leq n : totient n <= n.
Proof.
rewrite totient_count_coprime.
rewrite -{3}[n]muln1 -{3}[n]subn0 -sum_nat_const_nat.
by apply: leq_sum => i _; case: coprime.
Qed.

(* Definition of the order for Z_k *)
Fixpoint order_modn_rec m n r i k :=
  let r1 := ((r * n) %% m)%nat in
  if r1 == 1%N then i else 
  if k is k1.+1 then order_modn_rec m n r1 i.+1 k1 else i%nat.

Lemma order_modn_recP m n r i k :
  coprime n m ->
  1 < m ->
  0 < i ->
  (forall j, 0 < j < i -> (n ^ j != 1 %[mod m])%N) ->
  r = (n ^ i.-1 %% m)%nat -> m.+1 = (k + i)%nat -> 
  [/\ 0%N < order_modn_rec m n r i k,
  (n ^ order_modn_rec m n r i k = 1 %[mod m])%N &
  (forall j, 0 < j < order_modn_rec m n r i k -> (n ^ j != 1 %[mod m])%N)].
Proof.
move=> nCm m_gt1.
elim: k r i => /= [r i i_gt0 H rE mE| k IH r i i_gt0  H rE mE].
  have /H/eqP[] : 0 < totient m < i.
    by rewrite totient_gt0 ?(leq_trans _ m_gt1) // -[i]mE [_ < _]totient_leq.
  by apply: cyclic.Euler_exp_totient.
have niE : (n ^ i = r * n %[mod m])%N by rewrite rE modnMml -expnSr prednK.
case: eqP => [rnE|/eqP rnE].
  by rewrite niE {1}(modn_small m_gt1).
apply: IH => [|i1 /andP[i1_gt0]||] //.
  rewrite ltnS leq_eqVlt => /orP[/eqP->|i1Li].
    by rewrite niE {1}(modn_small m_gt1).
  by apply: H; rewrite i1_gt0.
by rewrite mE addnS.
Qed.

Definition order_modn m n := 
  if coprime n m && (1 < m) then order_modn_rec m n 1 1 m
  else 0%nat.

Lemma order_modnP m n :
  1 < m -> coprime m n ->
  [/\ 0 < order_modn m n,
  (n ^ order_modn m n = 1 %[mod m])%N &
  (forall j, 0 < j < order_modn m n -> n ^ j != 1 %[mod m])%N].
Proof.
move=> m_gt1 mCn.
rewrite /order_modn m_gt1 coprime_sym mCn /=.
apply: order_modn_recP => //; first by rewrite coprime_sym.
- by case.
- by rewrite modn_small.
by rewrite addn1.
Qed.

Lemma order_modn_gt1 k m : 1 < order_modn k m -> 1 < k.
Proof. by rewrite /order_modn andbC; case: (1 < k). Qed.

Lemma order_modn_coprime k m : 1 < order_modn k m -> coprime k m.
Proof. Proof. by rewrite /order_modn coprime_sym; case: coprime. Qed.

Lemma order_modn_dvd k m :
   1 < k -> coprime k m -> (k %| (m ^ order_modn k m).-1)%N.
Proof.
move=> k_gt1 kCm.
have /(order_modnP k_gt1)[o_gt0 /eqP] := kCm.
rewrite /dvdn [(1 %% _)%N]modn_small // => /eqP modE _.
by rewrite (divn_eq (_ ^ _) k) modE addn1 /= modnMl.
Qed.

Lemma order_modn_mod k m : 1 < k -> order_modn k (m %% k) = order_modn k m.
Proof.
move=> k_gt1.
have [kCm| kNCm]:= boolP (coprime k m); last first.
  have kNCmk : ~~ coprime k (m %% k) by rewrite coprime_modr.
  by rewrite /order_modn coprime_sym (negPf kNCmk) coprime_sym (negPf kNCm).
have kCmk : coprime k (m %% k) by rewrite coprime_modr.
have [m_gt0 Hm Hmn] := order_modnP k_gt1 kCm.
have [mk_gt0 Hmk Hmkn] := order_modnP k_gt1 kCmk.
case: (leqP (order_modn k (m %% k)%N) (order_modn k m)) => [|mLmk].
  rewrite leq_eqVlt => /orP[/eqP->//|mkLm].
  have /Hmn/eqP[] :  0 < order_modn k (m %% k) < order_modn k m.
    by rewrite mk_gt0.
  by rewrite -modnXm.
have /Hmkn/eqP[] :  0 < order_modn k m < order_modn k (m %% k).
  by rewrite m_gt0.
by rewrite modnXm.
Qed.

Lemma order_modnE n m :
  1 < m -> coprime m n ->
  order_modn m n =
  oapp (fingroup.order : {unit 'Z_m} -> nat) 0%N (insub n%:R).
Proof.
move=> m_gt1 mCn.
case: insubP; rewrite unitZpE ?mCn //= => u _ Hu.
have  [o_gt0 moE1 Hmon] := order_modnP m_gt1 mCn.
case: (leqP (order_modn m n) #[u]%g) => [|uLo].
  rewrite leq_eqVlt => /orP[/eqP //|].
  rewrite ltnNge => /negP[].
  apply: dvdn_leq => //.
  rewrite cyclic.order_dvdn.
  apply/eqP/val_eqP => /=.
  by rewrite FinRing.val_unitX /= Hu -natrX -Zp_nat_mod // moE1 modn_small.
have : n ^ #[u]%g != 1 %[mod m] by apply: Hmon; rewrite order_gt0.
have /val_eqP/= := expg_order u.
rewrite FinRing.val_unitX /= Hu -natrX -val_Zp_nat // => /eqP->.
by rewrite modn_small.
Qed.

(* k > 1 not necessary *)
Lemma order_modn_exp k m :
  1 < k -> coprime k m -> m ^ order_modn k m = 1 %[mod k].
Proof.
by move=> k_gt1 kCm; case: (order_modnP k_gt1 kCm).
Qed.

Lemma leq_order_totient k m : 0 < k -> order_modn k m <= totient k.
Proof.
move=> k_gt0.
case: (leqP k 1) => [|k_gt1].
  rewrite /order_modn.
  by case: k k_gt0 => [|[|]]; rewrite ?ltnn ?andbF.
have [kCm|kNCm] := boolP (coprime k m); last first.
  by rewrite /order_modn coprime_sym (negPf kNCm).
rewrite order_modnE //.
rewrite -card_units_Zp // /order_modn.
case: insubP => //= u uU uE.
by apply/subset_leq_card/subsetP=> i; rewrite inE.
Qed.


Lemma modn_prodm I r (P : pred I) F d :
  \prod_(i <- r | P i) (F i %% d) = \prod_(i <- r | P i) F i %[mod d].
Proof.
apply/eqP; elim/big_rec2: _ => // i m n _ /eqP nEm.
by rewrite modnMml -modnMmr nEm modnMmr.
Qed.

Lemma order_gt1_prime k n :
  1 < n -> 1 < order_modn k n ->
  exists p : nat, [/\ (p %| n), prime p & 1 < order_modn k p]%nat.
Proof.
move=> n_gt1 o_gt1.
have k_gt1 := order_modn_gt1 o_gt1.
have [/allP Ho|/allPn] := 
    boolP (all (fun i => order_modn k i <= 1) (primes n)); last first.
  case=> p; rewrite mem_primes -ltnNge => /and3P[pP _ pDn] pO.
  by exists p.
have B1 : 0 < 1 < order_modn k n by [].
have [_ _ /(_ _ B1)/eqP[]] := 
     order_modnP k_gt1 (order_modn_coprime o_gt1).
rewrite expn1 [n]prod_prime_decomp 1?ltnW // prime_decompE.
rewrite big_seq_cond -modn_prodm big1 // => [] [p r].
rewrite andbT => /mapP[q qP [-> ->]] /=.
have oL1 := Ho _ qP.
have kCq : coprime k q.
  apply: coprime_dvdr (order_modn_coprime o_gt1).
  by rewrite mem_primes in qP; case/and3P: qP.
have [H1 H2 _] := order_modnP k_gt1 kCq.
rewrite -modnXm -[q]expn1 -{1}(_ : order_modn k q = 1%nat).
  by rewrite H2 modnXm exp1n modn_small.
by apply/eqP; rewrite eqn_leq oL1.
Qed.

(* Definition of order for poly *)
Definition poly_order {R : ringType} (h p :  {poly R}) (n : nat) : nat := 
  if [pick i | rmodp (p^+ (i : 'I_n.+1).-1.+1) h == 1] is Some v then
      [arg min_(i < v | (rmodp (p^+ i.-1.+1) h == 1)) i].-1.+1 else 0.

Lemma poly_orderE (R : ringType) (h p : {poly R}) n m :
  0 < m <= n ->
  rmodp (p ^+ m) h = 1 ->
  (forall k, 0 < k -> rmodp (p^+ k) h = 1 -> m <= k) ->
  poly_order h p n = m.
Proof.
move=> /andP[m_gt0 mLn] /eqP mM HmM.
rewrite -ltnS in mLn.
rewrite /poly_order; case: pickP => [z zM|/(_ (Ordinal mLn))]; last first.
  by rewrite prednK //= (eqP mM) eqxx.
case: arg_minnP => //.
move=> i /eqP /HmM /= Hj /(_ (Ordinal mLn)).
rewrite prednK //= => /(_ mM) iLm.
apply/eqP; rewrite eqn_leq Hj // andbT.
by case: (i: nat) iLm.
Qed.

Lemma poly_order_leq (R : ringType) (h p : {poly R}) n :
  0 < n -> poly_order h p n <= n.
Proof.
by rewrite /poly_order; case: pickP => // x Hx; case: arg_minnP => // [] [[|m]].
Qed.

Lemma poly_order_gt0_rmodp (R : ringType) (h p : {poly R}) n :
  0 < poly_order h p n ->  rmodp (p^+ poly_order h p n) h == 1.
Proof.
by rewrite /poly_order; case: pickP => // x Hx _; case: arg_minnP.
Qed.

Lemma poly_order_eq0_rmodp (R : ringType) (h p : {poly R}) m n :
  poly_order h p n = 0%N -> 0 < m <= n -> rmodp (p^+ m) h != 1.
Proof.
rewrite -[_ <= n]ltnS /poly_order; case: pickP => // HM _ /andP[m_gt0 mLn].
by have /= := HM (Ordinal mLn); case: (m) m_gt0 => //= k _ /idP/negP.
Qed.

Lemma poly_order_lt (R : ringType) (h p : {poly R}) m n :
   0 < m < poly_order h p n -> rmodp (p^+ m) h != 1.
Proof.
rewrite /poly_order; case: pickP=> [x Hx|]; last by rewrite ltn0 andbF.
case: arg_minnP => // i Hi Hmin /andP[m_gt0 mLi].
have mLn : m < n.+1.
  by rewrite (leq_trans mLi) // (leq_trans _ (ltn_ord i)) //; case: (i : nat).
apply/negP; rewrite -[m]prednK // => /(Hmin (Ordinal mLn)) /=.
rewrite leqNgt; case: (i : nat) mLi  => [/=|j ->//].
by case: (m) m_gt0.
Qed.

(* To be a power of 2 *)
Definition is_2power n := n == 2 ^ (up_log 2 n).
Definition isnot_2power n := n != 2 ^ (up_log 2 n).

(* To be a power *)

Definition is_power p q := p == q ^ logn q p.

Lemma prime_is_power_exp p q n :
  prime p -> 1 < q -> 0 < n -> 
  is_power (q ^ n) p -> is_power q p.
Proof.
move=> pP q_gt1 n_gt0.
have q_gt0 : 0 < q by apply: ltnW.
by rewrite  /is_power lognX mulnC expnM eqn_exp2r.
Qed.

Lemma is_power_exp p n : prime p -> is_power (p ^ n) p.
Proof.
by move=> pP; rewrite /is_power eqn_exp2l ?prime_gt1 // pfactorK.
Qed.

Lemma is_power_id p : prime p -> is_power p p.
Proof. by move=> pP; rewrite -{1}(expn1 p) is_power_exp. Qed.
