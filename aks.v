From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section AKS.
Import Pdiv.CommonRing.
Import Pdiv.RingMonic.

Definition introspective {R : ringType} n k (p : {poly R}) :=
  rmodp (p ^+ n) ('X^k - 1)  == rmodp (p \Po 'X^n) ('X^k - 1).

Notation " n '⋈[' k ] p" := (introspective n k p) 
  (at level 40, format "n  '⋈[' k ]  p").

Lemma introspective1 (R : ringType) k (p : {poly R}) : 1 ⋈[k] p.
Proof. by rewrite /introspective expr1 comp_polyXr. Qed.

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

Lemma dvdp_geom (R : comRingType) n (p : {poly R}) : p - 1 \is monic -> rdvdp (p - 1) (p ^+ n.+1 - 1).
Proof. move=> pM; rewrite poly_geom mulrC rdvdp_mull //. Qed.

(* 98 *)
Lemma introspec_char (F : finFieldType) (k n c : nat) :
  n \in [char F] -> n ⋈[k] ('X + c%:R%:P : {poly F}).
Proof.
move=> nC; apply/eqP; congr (rmodp _  _).
have Pp : prime n by apply: charf_prime nC.
have Cn : [char F].-nat n by rewrite pnatE.
rewrite comp_polyD comp_polyC comp_polyX.
rewrite exprDn_char; first by rewrite -polyC_exp fin_little_fermat.
by rewrite pnatE // (rmorph_char (polyC_rmorphism _)).
Qed.

Lemma comp_poly_exp (R : comRingType) n (p q : {poly R}) : 
  (p \Po q) ^+ n = (p ^+ n) \Po q.
Proof.
elim: n => [|n IH]; first by rewrite !expr0 comp_polyC.
by rewrite !exprS IH comp_polyM.
Qed.

Lemma comp_polyXn (R : ringType) n (p : {poly R}) : 
  'X^n \Po p = p ^+ n.
Proof.
rewrite comp_polyE size_polyXn.
rewrite (bigD1 ord_max) //= coefXn eqxx scale1r big1 ?addr0 //.
by move=> i /eqP/val_eqP /= iDn; rewrite coefXn (negPf iDn) scale0r.
Qed.

Lemma comp_polyXsub1 (R : ringType) n : 
  ('X - 1) \Po 'X^n = 'X^n - 1 :> {poly R}.
Proof. by rewrite comp_polyB comp_polyC comp_polyX. Qed.

Lemma modp_exp (R : comRingType) n (p d : {poly R}) :
  d \is monic -> rmodp ((rmodp p d) ^+ n) d = (rmodp (p ^+ n) d).
Proof.
move=> lCd; elim: n => [|n IH]; first by rewrite !expr0.
rewrite !exprS.
by rewrite -rmodp_mulmr // IH rmodp_mulmr // mulrC rmodp_mulmr // mulrC.
Qed.

Lemma rmodp_sub (R : ringType) (d p q : {poly R}) : 
  d \is monic -> rmodp (p - q) d = rmodp p d - rmodp q d.
Proof.
move=> dM.
rewrite {1}(rdivp_eq dM p) {1}(rdivp_eq dM q).
rewrite opprD addrCA 2!addrA -mulNr -mulrDl (addrC (- rdivp q d)) -addrA.
rewrite rmodp_addl_mul_small //; apply: (leq_ltn_trans (size_add _ _)).
by rewrite gtn_max size_opp !ltn_rmodp // monic_neq0.
Qed.

Lemma rdvdp_trans (R : ringType) (p q r : {poly R}) : 
  p \is monic -> q \is monic -> rdvdp p q -> rdvdp q r -> rdvdp p r.
Proof.
move=> pM qM /rdvdpP => /(_ pM) [qq1 qq1E] /rdvdpP => /(_ qM) [qq2 qq2E].
by apply/rdvdpP => //; exists (qq2 * qq1); rewrite qq2E qq1E mulrA.
Qed.

Lemma coef_comp_poly {R : ringType} (p q : {poly R}) n :
  (p \Po q)`_n = \sum_(i < size p) p`_i * (q ^+ i)`_n.
Proof. by rewrite comp_polyE coef_sum; apply: eq_bigr => i; rewrite coefZ. Qed.

Lemma size_exp_monic (R : ringType) (p: {poly R}) n :
  p \is monic -> size (p ^+ n) = ((size p).-1 * n).+1.
Proof.
move=> pM; elim: n => // [|n IH]; first by rewrite !expr0 muln0 size_polyC oner_eq0.
rewrite exprS size_proper_mul ?IH; last first.
  by rewrite (eqP pM) (eqP (monic_exp n pM)) mul1r oner_neq0.
have : (0 < size p)%nat.
  by have := monic_neq0 pM; rewrite -size_poly_eq0; case: size.
by case: size => // k _; rewrite addSn addnS -mulnS.
Qed.

Lemma monic_comp_poly (R : ringType) (p q : {poly R}) :
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
  by have := monic_exp k qM; rewrite qualifE /lead_coef size_exp_monic //= mulnC.
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

Lemma rdvdp_comp_poly (R : comRingType) (r p q : {poly R}) : 
 p \is monic -> r \is monic -> r != 1 -> rdvdp p q -> rdvdp (p \Po r) (q \Po r).
Proof.
move=> pM rM rD1 /rdvdpP => /(_ pM) [qq qqE].
apply/rdvdpP; first by apply: monic_comp_poly.
by exists (qq \Po r); rewrite qqE comp_polyM.
Qed.
  
(* 99 *)
Lemma introspecMl (R : comRingType) (k m n : nat) (p : {poly R}) :
  m ⋈[k] p -> n ⋈[k] p -> m * n ⋈[k] p.
Proof.
case: m => // m.
have XmD1 : 'X^m.+1 != 1 :> {poly R}.
  apply/eqP => /(congr1 (size : {poly R} -> _)).
  by rewrite size_polyXn size_polyC oner_eq0.
case: k => [|k mIp nIp].
  rewrite /introspective !subrr !rmodp0 exprM => /eqP->.
  rewrite comp_poly_exp => /eqP->.
  by rewrite -comp_polyA comp_polyXn -exprM.
have XM : ('X^k.+1 - 1 : {poly R}) \is monic.
  rewrite qualifE lead_coefDl ?lead_coefXn ?unitr1 //.
  by rewrite size_polyXn size_opp size_polyC oner_neq0.
rewrite /introspective exprM -modp_exp // (eqP mIp) modp_exp //.
rewrite exprM -['X^m.+1 ^+_]comp_polyXn comp_poly_exp comp_polyA.
rewrite -subr_eq0 -rmodp_sub // -comp_polyB.
apply: rdvdp_trans (_ : rdvdp (('X^k.+1 -1) \Po 'X^m.+1) _) => //.
- by apply: monic_comp_poly => //; rewrite qualifE lead_coefXn.
- rewrite comp_polyB comp_polyXn comp_polyC -exprM mulnC exprM.
  by apply: dvdp_geom.
apply: rdvdp_comp_poly => //; first by rewrite qualifE lead_coefXn.
by rewrite /rdvdp rmodp_sub // subr_eq0.
Qed.

(* 100 *)
Lemma introspecMr (R : comRingType) (k n : nat) (p q : {poly R}) :
  n ⋈[k] p -> n ⋈[k] q -> n ⋈[k] (p * q).
Proof.
case: k => [|k nIp nIq].
  rewrite /introspective !subrr !rmodp0.
  by rewrite comp_polyM exprMn => /eqP-> /eqP->.
have Xlf := monic_Xn_sub_1 R (isT : (0 < k.+1)%N).
rewrite /introspective exprMn -rmodp_mulmr // (eqP nIq).
rewrite rmodp_mulmr // mulrC.
rewrite -rmodp_mulmr // (eqP nIp) rmodp_mulmr //.
by rewrite mulrC comp_polyM.
Qed.

Definition irreducibleb (F : finFieldType) (p : {poly F}) :=
  (1 < size p)%N && 
  [forall q : (size p).-1.-tuple F, (Poly q %| p) ==> (size (Poly q) <= 1)%N].

Lemma irreducibleP (F : finFieldType) (p : {poly F}) : 
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

Lemma irreducible_dvdp (F : finFieldType) (p : {poly F}) :
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

Lemma irreducible_exp (R : idomainType) n (p q : {poly R}) :
  irreducible_poly p -> (0 < n)%N -> p %| q ^+ n = (p %| q).
Proof.
move=> pI.
elim: n => // [] [|n] // /(_ isT) IH _.
apply/idP/idP; rewrite exprS; last first.
  by move=> /dvdp_trans; apply; apply: dvdp_mulr.
have [pCq|pNCq] := boolP (coprimep p q); first by rewrite Gauss_dvdpr // IH.
have /(irredp_XsubCP pI)[pCq|/andP[_ pDg] _] : gcdp p q %| p by rewrite dvdp_gcdl.
  case/negP: pNCq.
  by rewrite /coprimep size_poly_eq1.
by apply: dvdp_trans pDg (dvdp_gcdr _ _).
Qed. 

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

Lemma poly_natmul (R : ringType) n :
  n%:R%:P = n%:R :> {poly R}.
Proof.
elim: n => // n IH.
by rewrite -addn1 !natrD polyC_add IH.
Qed.

(* 102 *)
Lemma introspec_fin_div (F : finFieldType) k n p (c : nat) :
  coprime k n -> p \in [char F] -> (p %| n)%N ->
  n ⋈[k] ('X + c%:R%:P : {poly F}) -> (n %/ p) ⋈[k] ('X + c%:R%:P : {poly F}).
Proof.
move=> kCn pC pDn nIkX.
have pP : prime p by case/andP: pC.
have k_gt0 : (0 < k)%N.
  case: k {nIkX}kCn pDn pP => //.
  rewrite /coprime gcd0n => /eqP->.
  by rewrite dvdn1 => /eqP->.
  rewrite /introspective -!Pdiv.IdomainMonic.modpE ?monic_Xn_sub_1 //.
have kNZ : k%:R != 0 :> F.
  rewrite -(dvdn_charf pC); apply/negP => pDk.
  move: pP.
  have : (p %| 1)%N by rewrite -(eqP kCn) dvdn_gcd pDk.
  by rewrite dvdn1 => /eqP->.
have pCF : [char {poly F}].-nat p.
  rewrite /pnat prime_gt0 //=; apply/allP => q.
  rewrite primes_prime //= inE => /eqP->.
  rewrite inE pP -poly_natmul polyC_eq0 /=.
  by case/andP : pC.
rewrite -subr_eq0 -modp_opp -modp_add -[_ == 0]/(_ %| _).
rewrite -(separable_exp _ (separable_polyXnsub1 _) (prime_gt0 pP)) //.
rewrite exprDn_char // exprNn_char // -exprM divnK //.
rewrite comp_polyD comp_polyC [_ ^+ p]exprDn_char //.
rewrite comp_poly_exp comp_polyXn -exprM divnK //.
rewrite -polyC_exp fin_little_fermat //.
rewrite /dvdp modp_add modp_opp subr_eq0 //.
move: nIkX.
rewrite /introspective -!Pdiv.IdomainMonic.modpE ?monic_Xn_sub_1 //.
by rewrite comp_polyD comp_polyC comp_polyX.
Qed.

(* I've departed from Chan thesis as it is not easy 
   to build non-constructive sets in Coq. So I turn 
   them into properties. Trying to sort things out 
   went doing the proof by contradiction 
 *)

(* This 𝒩 as a predicate *)
Definition is_iexp (R : ringType) (k s m : nat) := 
   coprime m k /\ forall c, (0 < c <= s)%N -> m ⋈[k] ('X + c%:R%:P : {poly R}).

Lemma is_iexp1 (R : ringType) k s : is_iexp R k s 1%N.
Proof.
split=> [|c cR]; first by rewrite /coprime gcd1n.
by apply: introspective1.
Qed.

Lemma is_iexp_mul (R : comRingType) k s m1 m2 : 
  is_iexp R k s m1 -> is_iexp R k s m2 -> is_iexp R k s (m1 * m2)%N.
Proof.
move=> [m1Ck Hm1] [m2Ck Hm2]; split; first by rewrite coprime_mull m1Ck.
by move=> c Hc; apply: introspecMl; [apply: Hm1 | apply: Hm2].
Qed.

Lemma is_iexp_X (R : comRingType) k s m n : 
  is_iexp R k s m -> is_iexp R k s (m ^ n)%N.
Proof.
move=> mI; elim: n => [|n IH]; first by apply: is_iexp1.
by rewrite expnS; apply: is_iexp_mul.
Qed.

(* 103 *)
Lemma is_iexp_fin_char (F : finFieldType) k s p :  
  p \in [char F] -> coprime p k -> is_iexp F k s p.
Proof. by move=> pC pCk; split => // c _; apply:  introspec_char. Qed.

Lemma is_iexp_fin_div (F : finFieldType) k s n p :  
  p \in [char F] -> coprime p k -> (p %| n)%N -> 
  is_iexp F k s n -> is_iexp F k s (n %/ p).
Proof. 
move=> pC pCk pDn[nCk nI]; split => [|c cB].
  by have := nCk; rewrite -{1}(divnK pDn) coprime_mull => /andP[].
apply: introspec_fin_div => //; first by rewrite coprime_sym.
by apply: nI.
Qed.

(* This is 𝒫 *)
Definition is_ipoly (R : ringType) (k s m : nat) (p : {poly R}):= 
  forall m, is_iexp R k s m -> m ⋈[k] p.

(* This is 𝓜_k *)
Definition is_iexpm (R : ringType) (k s mk : nat) :=
   exists2 m, mk = (m %% k)%N & is_iexp R k s m.

Inductive is_iexpm_spec (R : ringType) (k k1 s : nat) (mk : 'I_k1) : bool -> Prop :=
   is_iexpm_spec_true : 
    forall (m : nat), (mk = m %% k :> nat)%N -> is_iexp R k s m -> @is_iexpm_spec R k k1 s mk true
 | is_iexpm_spec_false :
 (forall (m : nat), is_iexp R k s m -> (mk != m %% k :> nat)%N) -> @is_iexpm_spec R k k1 s mk false.

(* I've put Mk in {set 'Z_k} but its natural ambient is units_Zp! *)
Definition Mk_spec R s k (M : {set 'Z_k}) :=
  (forall x, @is_iexpm_spec R k ((Zp_trunc k).+2) s x (x \in M)).

(* There should be a shorter proof *)
Lemma Mk_Cexists R k s : (1 < k)%N -> classically (exists M : {set 'Z_k}, Mk_spec R s M).
Proof.
move=> k_gt1; rewrite /Mk_spec Zp_cast // => {k_gt1}[].
rewrite /Mk_spec; elim:  {-6}k => [|k1 IH].
  by apply/classicP => [] []; exists set0 => [] [].
apply: classic_bind IH => [] [M HM].
pose M1 := [set (fintype.lift ord_max i) | i in M].
have /classic_bind := @classic_pick nat
 (fun m => ((ord_max : 'I_k1.+1) = m %% k :> nat)%N /\ is_iexp R k s m).
apply => [] [[x [xE xI]]|oE].
  apply/classicP => [] []; exists (ord_max |: M1) => y.
  rewrite !inE; case: eqP=> [->/=|/eqP yDo/=].
    by apply: is_iexpm_spec_true xI.
  have [/imsetP [z]|yNIM1] := boolP (y \in _).
    case: HM => // m zE mI _ yE.
    apply: is_iexpm_spec_true mI.
    by rewrite yE /= /bump /= leqNgt ltn_ord zE.
  constructor => m mI; apply/eqP=> yE.
  case/negP: yNIM1; apply/imsetP.
  case: (unliftP ord_max y) => [z zE| zE1]; last by case/eqP: yDo.
  exists z => //; case: HM => // /(_ m mI) /eqP[].
  by rewrite -yE zE /= /bump leqNgt ltn_ord.
apply/classicP => [] []; exists M1 => x.
have [/eqP xEo| xDo] := boolP (x == ord_max).
  rewrite (_ : _ \in _ = false).
    constructor => m mI; apply/negP => /eqP xEm.
    by case: (oE m); rewrite -xEo.
  apply/idP=> /imsetP[y]; case: HM => // m yE  _ _ /val_eqP /=.
  by rewrite xEo /= (negPf (neq_bump _ _)).
have [/imsetP [y]|xNIM1] := boolP (x \in _).
  case: HM => // m yE mI _ xE.
  apply: is_iexpm_spec_true mI.
  by rewrite xE /= /bump /= leqNgt ltn_ord yE.
constructor => m mI; apply/eqP=> xE.
case/negP: xNIM1; apply/imsetP.
case: (unliftP ord_max x) => [y yE| xE1]; last by case/eqP: xDo.
exists y => //; case: HM => // /(_ m mI) /eqP[].
by rewrite -xE yE /= /bump leqNgt ltn_ord.
Qed.

Lemma is_iexpm1 (R : comRingType) k s (M : {set 'Z_k}) : 
  (1 < k)%N -> Mk_spec R s M -> 1 \in M.
Proof.
move=> k_gt1 MS; case: MS => // /(_ 1%N (is_iexp1 _ _ _)).
by rewrite modn_small ?eqxx.
Qed.

Lemma is_iexpm_mul (R : comRingType) k s (M : {set 'Z_k}) x y : 
  (1 < k)%N -> Mk_spec R s M -> x \in M -> y \in M -> (x * y) \in M. 
Proof.
move=> k_gt1 MS.
(do 3 case: (MS) => //) => Hm m1 yE m1I m xE mI _ _.
have /eqP[] := Hm _ (is_iexp_mul mI m1I).
by rewrite -modnMml -xE -modnMmr -yE /= {3}Zp_cast.
Qed.

Lemma is_iexpm_X (R : comRingType) k s (M : {set 'Z_k}) x n : 
  (1 < k)%N -> Mk_spec R s M -> x \in M -> (x ^+ n) \in M. 
Proof.
move=> k_gt1 MS xM.
elim: n => [|n IH]; first by apply: is_iexpm1.
by rewrite exprS; apply: is_iexpm_mul.
Qed.

(* 104 *)
Lemma is_iexpm_totient R k s (M : {set 'Z_k}) :
  (1 < k)%N -> Mk_spec R s M -> (#|M| <= totient k)%N.
Proof.
move=> k_gt1; move: M; rewrite /Mk_spec Zp_cast // => {k_gt1}[].
case: k => [M _|k M HM].
  apply: leq_trans (_ : (#|(setT : {set 'I_0})| <= _)%N).
    by apply/subset_leq_card/subsetT.
  by rewrite cardsT card_ord.
suff <-: #|[set i in 'I_k.+1 | coprime i k.+1]| = totient k.+1.
  apply/subset_leq_card/subsetP=> x; rewrite !inE; case: HM => // m -> [].
  by rewrite coprime_modl.
rewrite -sum1_card big_mkcond /=.
rewrite totient_count_coprime big_mkord.
by apply: eq_bigr => i _; rewrite inE coprime_sym.
Qed.

Lemma mk_Zp_unit_proof k m : 
  (if (1 < k)%N && (coprime k m) then (m%:R : 'Z_k) else 1) \is a GRing.unit.
Proof.
case: leqP =>  [_|k_gt1]; first by apply: unitr1.
by case: coprime (unitZpE m k_gt1) => [//|_]; apply: unitr1.
Qed.

Definition mk_Zp_unit (k m : nat) :=
  FinRing.unit 'Z_k (mk_Zp_unit_proof k m).

Lemma val_mk_Zp_unit k m :
  (1 < k)%N -> coprime k m -> val (mk_Zp_unit k m) = (m %% k)%N :> nat.
Proof.
by move=> k_gt1 kCm; rewrite /= k_gt1 kCm val_Zp_nat.
Qed.

Lemma val_mk_Zp_unit_Zp k (m : 'Z_k) :
  (1 < k)%N -> coprime k m -> val (mk_Zp_unit k m) = m.
Proof.
move=> k_gt1 kCm; apply/val_eqP/eqP; rewrite /= k_gt1 kCm val_Zp_nat //=.
by rewrite modn_small //; move: (m); rewrite Zp_cast.
Qed.

Definition ordern k m := 
  if (1 < k)%N && (coprime k m) then #[mk_Zp_unit k m]%g else 0%N.

(* k > 1 not necessary *)
Lemma ordern_exp k m :
  (1 < k)%N -> coprime k m -> m ^ ordern k m = 1 %[mod k].
Proof.
move=> k_gt1 kCm.
have /(congr1 val) /(congr1 val) := expg_order (mk_Zp_unit k m).
by rewrite FinRing.val_unitX /ordern /= k_gt1 kCm /= -natrX val_Zp_nat // Zp_cast.
Qed.

(* 104 *)
Lemma is_iexpm_order (R : comRingType) k s (M : {set 'Z_k}) x :
  (1 < k)%N -> Mk_spec R s M -> x \in M -> (ordern k x <= #|M|)%N.
Proof.
move=> k_gt1 HM xIM.
have kCx : coprime k x.
  by move: xIM; case: HM => // m -> []; rewrite coprime_modr coprime_sym.
suff <-: #|[set val x | x in <[mk_Zp_unit k x]>%g]| = ordern k x.
  apply/subset_leq_card/subsetP => y /imsetP[z /cycleP[i ->] ->].
  by rewrite FinRing.val_unitX val_mk_Zp_unit_Zp //; apply: is_iexpm_X.
rewrite /ordern k_gt1 kCx.
by apply/eqP/imset_injP=> y z H1 H2 U; apply/val_eqP/eqP.
Qed.

End AKS.

Notation " n '⋈[' k ] p" := (introspective n k p) 
  (at level 40, format "n  '⋈[' k ]  p").
  
