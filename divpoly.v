From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
Require Import more_thm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Pdiv.CommonRing.
Import Pdiv.RingMonic.

Local Open Scope ring_scope.
Local Open Scope nat_scope.


Section PType.

Section DivPolySub.

Variable A : ringType.
Variable p : {poly A}.
Implicit Types p q : {poly A}.

Inductive divpoly : predArgType := DivPoly q of (size q < size p)%N.

Coercion poly_of_divpoly r := let: DivPoly q _ := r in q.

Canonical divpoly_subType := [subType for poly_of_divpoly].
Definition divpoly_eqMixin := Eval hnf in [eqMixin of divpoly by <:].
Canonical divpoly_eqType := Eval hnf in EqType divpoly divpoly_eqMixin.
Definition divpoly_choiceMixin := [choiceMixin of divpoly by <:].
Canonical divpoly_choiceType :=
  Eval hnf in ChoiceType divpoly divpoly_choiceMixin.

Lemma size_divpoly (i : divpoly) : size i < size p.
Proof. exact: valP i. Qed.

Lemma divpoly_inj : injective poly_of_divpoly. 
Proof. exact: val_inj. Qed.

End DivPolySub.

Hint Resolve size_divpoly.

Section Zmod.

Variable A : ringType.
Variable h : {poly A}.

Definition divpoly_quotient := 
  if (1 < size h) && (h \is monic) then h else 'X.

Notation hQ :=  divpoly_quotient.

Lemma monic_divpoly_quotient : hQ \is monic.
Proof.
rewrite /hQ; case: leqP=> [_|/=]; first by apply: monicX.
by case E : (h \is monic) => [->//|] => _; apply: monicX.
Qed. 

Lemma size_divpoly_quotient_gt1 : 1 < size hQ.
Proof. 
by rewrite /hQ !fun_if size_polyX; case: leqP => //=; rewrite if_same.
Qed. 

Lemma divpoly_quotient_neq0 : hQ != 0%R.
Proof.
by rewrite /hQ; case: leqP; try case: (_ \is _) => /= H;
   rewrite -size_poly_gt0 ?size_polyX // ltnW.
Qed.

(* standard inject *)
Lemma inDivPoly_mod p : size (rmodp p hQ) < size hQ.
Proof. by apply: ltn_rmodpN0 divpoly_quotient_neq0. Qed.

Lemma PolDiv_const_proof c : size (c%:P : {poly A}) < size hQ.
Proof.
by rewrite size_polyC (leq_trans _ size_divpoly_quotient_gt1) //; case eqP. 
Qed. 

Definition DivPoly_const k := DivPoly (PolDiv_const_proof k).

Definition DivPoly0 := DivPoly_const 0.

Definition DivPoly1 := DivPoly_const 1.

Definition inDivPoly p := DivPoly (inDivPoly_mod p).

Lemma inDivPolyE p : 
  (1 < size h)%N -> h \is monic -> inDivPoly p = rmodp p h :> {poly A}.
Proof. by rewrite /= /hQ => -> ->. Qed.

Definition DivPoly_opp (p : divpoly hQ) := inDivPoly (hQ - (p : {poly A})).
Definition DivPoly_add (p q : divpoly hQ) := 
  inDivPoly ((p : {poly A}) + (q : {poly A})).
Definition DivPoly_mul (p q : divpoly hQ) :=
  inDivPoly ((p : {poly A}) * (q : {poly A})).

(* Additive group structure. *)

Lemma DivPoly_add0z : left_id DivPoly0 DivPoly_add.
Proof.
move=> p. apply/val_eqP; rewrite /= add0r rmodp_small // size_divpoly.
Qed.

Lemma DivPoly_addNz : left_inverse DivPoly0 DivPoly_opp DivPoly_add.
Proof.
have hQM := monic_divpoly_quotient.
move=> p; apply/val_eqP.
rewrite /DivPoly_add /DivPoly_opp /inDivPoly /=.
by rewrite !(rmodp_sub, rmodp_add, rmodp_mod, rmodpp) // subrK.
Qed.

Lemma DivPoly_addA : associative DivPoly_add.
Proof.
have hQM := monic_divpoly_quotient.
by move=> p q r; apply/val_eqP; rewrite /= !(rmodp_add, rmodp_mod) // addrA.
Qed.

Lemma DivPoly_addC : commutative DivPoly_add.
Proof. by move=> p q; apply/val_eqP; rewrite /= addrC. Qed.

Definition DivPoly_zmodMixin :=
   ZmodMixin DivPoly_addA DivPoly_addC DivPoly_add0z DivPoly_addNz.
Canonical DivPoly_zmodType :=
   Eval hnf in ZmodType (divpoly hQ) DivPoly_zmodMixin.

Lemma DivPoly_mul1z : left_id DivPoly1 DivPoly_mul.
Proof. by move=> x; apply: val_inj; rewrite /= mul1r rmodp_small. Qed.

Lemma DivPoly_mulz1 : right_id DivPoly1 DivPoly_mul.
Proof. by move=> x; apply/val_inj => /=; rewrite mulr1 rmodp_small. Qed.

Lemma DivPoly_nontrivial : DivPoly1 != DivPoly0.
Proof. by apply/eqP/val_eqP; exact: oner_neq0. Qed.

End Zmod.

Notation "{ 'divpoly'  h }" := (divpoly (divpoly_quotient h))
  (format "{ 'divpoly'  h }").

Section Fmod.

Variable A : finRingType.
Variable h : {poly A}.

Definition divpoly_countMixin : Countable.mixin_of (divpoly h) :=
   @sub_countMixin (CountType {poly A} (poly_countMixin [countRingType of A])) 
                   _ (divpoly_subType h).
Canonical divpoly_countType :=
  Eval hnf in CountType (divpoly h) divpoly_countMixin.
Canonical fpoly_subCountType := [subCountType of divpoly h].

End Fmod.

Section Ring.

Variable A : comRingType.
Variable h : {poly A}.

(* Ring operations *)

Lemma DivPoly_mulC : commutative (@DivPoly_mul A h).
Proof.
have rPM := monic_divpoly_quotient.
by move=> p q; apply: val_inj; rewrite /= mulrC.
Qed.

Lemma DivPoly_mulA : associative (@DivPoly_mul A h).
Proof.
have rPM := monic_divpoly_quotient.
by move=> p q r; apply: val_inj; rewrite /= rmodp_mulmr // rmodp_mulml // mulrA.
Qed.

Lemma DivPoly_mul_addr :
  right_distributive (@DivPoly_mul A h) (@DivPoly_add _ h).
Proof.
have rPM := monic_divpoly_quotient.
move=> p q r; apply: val_inj.
by rewrite /= !(rmodp_mulmr, rmodp_add, rmodp_mod, mulrDr).
Qed.

Lemma DivPoly_mul_addl :
  left_distributive (@DivPoly_mul A h) (@DivPoly_add _ h).
Proof. by move=> p q r; rewrite -!(DivPoly_mulC r) DivPoly_mul_addr. Qed.

Definition DivPoly_ringMixin :=
  ComRingMixin DivPoly_mulA DivPoly_mulC (@DivPoly_mul1z _ h) DivPoly_mul_addl
               (@DivPoly_nontrivial _ h).

Notation hQ := (divpoly_quotient h).

Canonical DivPoly_ringType := 
  Eval hnf in RingType (divpoly hQ) DivPoly_ringMixin.
Canonical DivPoly_comRingType :=
  Eval hnf in ComRingType (divpoly hQ) DivPoly_mulC.

Lemma poly_of_divpolyD (p q : {divpoly h}) : 
  (p + q = (poly_of_divpoly p) + q :> {poly A})%R.
Proof.
apply/val_eqP=> //=; rewrite !rmodp_small //.
apply: leq_ltn_trans (size_add p q) _.
by rewrite gtn_max !size_divpoly.
Qed.

Lemma poly_of_divpoly_sum I (r : seq I) (P1 : pred I) (F : I -> {divpoly h}) :
  (poly_of_divpoly (\sum_(i <- r | P1 i) F i) =
    \sum_(p <- r | P1 p) (poly_of_divpoly (F p)))%R.
Proof.
by elim/big_rec2: _ => // i p q IH <-; rewrite poly_of_divpolyD.
Qed.

Lemma DivPoly_natmul p : poly_of_divpoly (p%:R)= p%:R :> {poly A}.
Proof.
by elim: p => //= p IH; rewrite !mulrS poly_of_divpolyD IH.
Qed.

Lemma char_DivPoly : [char {divpoly h}] =i [char A].
Proof.
move=> p; rewrite !inE; congr (_ && _).
apply/eqP/eqP=> [/(congr1 val) /=|pE]; last first.
  by apply: val_inj => /=; rewrite DivPoly_natmul -poly_natmul pE.
rewrite !DivPoly_natmul -!poly_natmul=> /(congr1 val) /=.
by rewrite polyseqC polyseq0; case: eqP.
Qed.

Lemma poly_of_divpolyM (p q : {divpoly h}) : 
  poly_of_divpoly (p * q)%R = rmodp (poly_of_divpoly p * poly_of_divpoly q) hQ.
Proof. by []. Qed.

Lemma poly_of_divpolyX (p : {divpoly h}) n : 
  poly_of_divpoly (p ^+ n) = rmodp ((poly_of_divpoly p) ^+ n) hQ.
Proof.
have HhQ := monic_divpoly_quotient h.
elim: n => //= [|n IH].
  by rewrite expr0 rmodp_small ?size_polyC ?oner_eq0 ?size_divpoly_quotient_gt1.
by rewrite exprS /= IH // rmodp_mulmr // -exprS.
Qed.

Lemma DivPoly_constN (a : A) : 
  DivPoly_const h (- a) = -(DivPoly_const h a).
Proof.
have HhQ := monic_divpoly_quotient h.
apply: val_inj.
rewrite /= rmodp_sub // rmodpp // sub0r rmodp_small //.
  by rewrite raddfN.
by apply: PolDiv_const_proof.
Qed.

Lemma DivPoly_constD : {morph (DivPoly_const h) : a b / a + b >-> a + b}%R.
Proof.
move=> a b; apply/val_eqP/eqP=> /=.
by rewrite -!raddfD rmodp_small // PolDiv_const_proof.
Qed.

Lemma DivPoly_constM : {morph (DivPoly_const h) : a b / a * b >-> a * b}%R.
Proof.
move=> a b; apply/val_eqP/eqP=> /=.
by rewrite -polyC_mul rmodp_small // PolDiv_const_proof.
Qed.

Lemma DivPoly_const_is_rmorphism : rmorphism (DivPoly_const h).
Proof.
do ?split; move=> // x y /=.
  by rewrite DivPoly_constD DivPoly_constN.
by rewrite DivPoly_constM.
Qed.

Canonical DivPoly_const_rmorphism := RMorphism DivPoly_const_is_rmorphism.

Definition DivPoly_scale k (p : divpoly hQ) := ((DivPoly_const h k) * p)%R.

Fact DivPoly_scaleA a b p :
  DivPoly_scale a (DivPoly_scale b p) = DivPoly_scale (a * b) p.
Proof. 
have hQM := monic_divpoly_quotient.
by apply/val_eqP; rewrite /= rmodp_mulmr // mulrA polyC_mul.
Qed.

Fact DivPoly_scale1l : left_id 1%R DivPoly_scale.
Proof. 
have hQM := monic_divpoly_quotient.
by move=> p; apply/val_eqP; rewrite /= mul1r rmodp_small.
Qed.

Fact DivPoly_scaleDr a : {morph DivPoly_scale a : p q / (p + q)%R}.
Proof.
have hQM := monic_divpoly_quotient.
move=> p q; apply/val_eqP; 
rewrite /= -rmodp_add // rmodp_mulmr // -mulrDr.
rewrite [rmodp (rmodp _ _) _]rmodp_small //.
by apply: inDivPoly_mod.
Qed.

Fact DivPoly_scaleDl p : {morph DivPoly_scale^~ p : a b / a + b}%R.
Proof.
have hQM := monic_divpoly_quotient.
move=> a b; apply/val_eqP.
rewrite /= -rmodp_add // -mulrDl -polyC_add [rmodp (rmodp _ _) _]rmodp_small //.
by apply: inDivPoly_mod.
Qed.

Fact DivPoly_scaleAl a p q :
  DivPoly_scale a (p * q)%R = (DivPoly_scale a p * q)%R.
Proof.
have hQM := monic_divpoly_quotient.
apply/val_eqP.
by rewrite /= rmodp_mulmr // rmodp_mulml // mulrA.
Qed.

Fact DivPoly_scaleAr a p q :
  DivPoly_scale a (p * q)%R = (p * (DivPoly_scale a q))%R.
Proof.
have hQM := monic_divpoly_quotient.
apply/val_eqP.
by rewrite /= !rmodp_mulmr // mulrCA.
Qed.

Definition DivPoly_lmodMixin :=
  LmodMixin DivPoly_scaleA DivPoly_scale1l DivPoly_scaleDr DivPoly_scaleDl.

Canonical DivPoly_lmodType :=
  Eval hnf in LmodType A {divpoly h} DivPoly_lmodMixin.
Canonical DivPoly_lalgType :=
  Eval hnf in LalgType A ({divpoly h}) DivPoly_scaleAl.
Canonical DivPoly_algType := AlgType A {divpoly h} DivPoly_scaleAr.

Lemma poly_of_divpolyZ (p : {divpoly h}) a :
       (a *: p = rmodp (a *: p) (divpoly_quotient h) :> {poly A})%R.
Proof.
have hQM := monic_divpoly_quotient.
by apply/val_eqP; rewrite rmodp_mod.
Qed.

End Ring.


Section Field.

Variable A : fieldType.
Variable h : {poly A}.

Notation hQ := (divpoly_quotient h).

Definition DivPoly_inv (p : {divpoly h}) := 
  if coprimep hQ p then let v : {divpoly h} := inDivPoly h (egcdp hQ p).2 in 
                        ((lead_coef (v * p)) ^-1 *: v) else p.

(* Ugly *)
Lemma DivPoly_mulVz (p : {divpoly h}) :
  coprimep hQ p -> (DivPoly_inv p * p = 1)%R.
Proof.
have hQM := monic_divpoly_quotient h.
move=> hCp; apply: val_inj; rewrite /DivPoly_inv /inDivPoly hCp /=.
have p_neq0 : p != 0%R.
  apply/eqP=> pZ; move: hCp; rewrite pZ.
  rewrite coprimep0 -size_poly_eq1.
  by case: size (size_divpoly_quotient_gt1 h) => [|[]].
have F : (egcdp hQ p).1 * hQ + (egcdp hQ p).2 * p %= 1.
  apply: eqp_trans _ (_ : gcdp hQ p %= _).
    rewrite eqp_sym.
    by case: (egcdpP (divpoly_quotient_neq0 h) p_neq0).
  by rewrite -size_poly_eq1.
rewrite rmodp_mulml // -mulrA -rmodp_mulmr // rmodp_mulml //.
rewrite -[rmodp]/Pdiv.Ring.rmodp -!Pdiv.IdomainMonic.modpE //.
have := eqp_modpl hQ F.
rewrite modp_add // modp_mull add0r // .
rewrite [(1 %% _)%R]modp_small => // [egcdE|]; last first.
  by rewrite size_polyC oner_eq0 size_divpoly_quotient_gt1.
rewrite {2}(eqpfP egcdE) lead_coefC divr1 alg_polyC -polyC_mul mulVf //.
  by rewrite modp_small // size_polyC  oner_eq0 size_divpoly_quotient_gt1.
rewrite lead_coef_eq0.
apply/eqP => egcdZ.
by move: egcdE; rewrite -size_poly_eq1 egcdZ size_polyC eq_sym  eqxx.
Qed.

Lemma DivPoly_mulzV (p : {divpoly h}) :
  coprimep hQ p -> (p * (DivPoly_inv p) = 1)%R.
Proof. by move=> hCp; rewrite /= mulrC DivPoly_mulVz. Qed.

Lemma DivPoly_intro_unit (p q : {divpoly h}) : (q * p = 1)%R -> coprimep hQ p.
Proof.
have hQM := monic_divpoly_quotient h.
case; rewrite -[rmodp]/Pdiv.Ring.rmodp -!Pdiv.IdomainMonic.modpE // => qp1.
have:= coprimep1 hQ.
rewrite -coprimep_modr -[1%R]qp1 !coprimep_modr coprimep_mulr; by case/andP.
Qed.

Lemma DivPoly_inv_out (p : {divpoly h}) : ~~ coprimep hQ p -> DivPoly_inv p = p.
Proof. by rewrite /DivPoly_inv => /negPf->. Qed.

Definition DivPoly_unitRingMixin :=
  ComUnitRingMixin DivPoly_mulVz DivPoly_intro_unit DivPoly_inv_out.
Canonical DivPoly_unitRingType :=
  Eval hnf in UnitRingType {divpoly h} DivPoly_unitRingMixin.
Canonical DivPoly_comUnitRingType :=
  Eval hnf in [comUnitRingType of {divpoly h}].

Definition monic_irreducible_poly (A : idomainType) (p : {poly A}) := 
  ((irreducible_poly p) * (p \is monic))%type.

Hypothesis hI : monic_irreducible_poly h.

Lemma irr_divpoly_quotientE : divpoly_quotient h = h.
Proof. by rewrite /divpoly_quotient !hI. Qed.

Lemma irreducible_poly_coprime (R : idomainType) (p q : {poly R}) :
  irreducible_poly p -> coprimep p q = ~~(p %| q)%R.
Proof.
case => H1 H2; apply/coprimepP/negP.
  move=> sPq H.
  by have := sPq p (dvdpp _) H; rewrite -size_poly_eq1; case: size H1 => [|[]].
move=> pNDq d dDp dPq.
rewrite -size_poly_eq1; case: eqP => // /eqP /(H2 _) => /(_ dDp) dEp.
by case: pNDq; rewrite -(eqp_dvdl _ dEp).
Qed.

Lemma coprimep_unit (p : {divpoly h}) : p != 0%R -> coprimep hQ p.
Proof.
move=> pNZ.
rewrite irreducible_poly_coprime //; last first.
  by case: hI; rewrite irr_divpoly_quotientE.
apply: contra pNZ => H; case: eqP => // /eqP /dvdp_leq /(_ H).
by rewrite leqNgt size_divpoly.
Qed.

Lemma DivPoly_mulVp (p : {divpoly h}) : p != 0%R -> (DivPoly_inv p * p = 1)%R.
Proof. by move=> pNZ; apply/DivPoly_mulVz/coprimep_unit. Qed.

Lemma DivPoly_inv0 : DivPoly_inv 0%R = 0%R :> {divpoly h}.
Proof.
rewrite /DivPoly_inv /= coprimep0 -size_poly_eq1 {2}irr_divpoly_quotientE.
by have [[]] := hI; case: size => [|[]].
Qed.

Definition DivPoly_fieldUnitMixin := FieldUnitMixin DivPoly_mulVp DivPoly_inv0.

Lemma DivPoly_fieldMixin : GRing.Field.mixin_of [unitRingType of {divpoly h}].
Proof. by apply: coprimep_unit. Qed.

Definition DivPoly_fieldIdomainMixin := FieldIdomainMixin DivPoly_fieldMixin.

Canonical DivPoly_idomainType :=
  Eval hnf in IdomainType {divpoly h} DivPoly_fieldIdomainMixin.
Canonical DivPoly_fieldType :=
  Eval hnf in FieldType {divpoly h} DivPoly_fieldMixin.

End Field.


Section Vector.

Variable A : fieldType.
Variable h : {poly A}.
Notation hQ := (divpoly_quotient h).

Definition DivPoly_X i : {divpoly h} := inDivPoly h 'X^i.

Let F0 : 0 < size hQ.
Proof. by apply: leq_trans (size_divpoly_quotient_gt1 h). Qed.

Let F1 : 1 < size hQ.
Proof. by apply: size_divpoly_quotient_gt1. Qed.

Lemma DivPoly_XE (p : {divpoly h}) :
   p = (\sum_(i < (size hQ).-1) p`_i *: DivPoly_X i)%R.
Proof.
have hQM := monic_divpoly_quotient h.
apply/val_eqP/eqP=> /=.
rewrite -[X in X = _]coefK poly_def poly_of_divpoly_sum.
have F : (size p <= (size hQ).-1)%N by rewrite -ltnS prednK ?size_divpoly.
rewrite (big_ord_widen _ (fun i => p`_i *: 'X^i) F).
rewrite [X in _ = X](@bigID {poly A} 0%R _ _
                     (index_enum (ordinal_finType (size hQ).-1))
                      (fun i => i < size p)%N xpredT) /=.
rewrite [X in _ = (_ + X)%R]big1 ?addr0 => [|i Li].
  apply: eq_bigr => i Li.
  rewrite -[rmodp]/Pdiv.Ring.rmodp -!Pdiv.IdomainMonic.modpE //.
  rewrite mul_polyC !modp_scalel // modp_mod modp_small //.
  by rewrite size_polyXn -[X in (_ < X)%N](prednK F0) ltnS.
rewrite -[rmodp]/Pdiv.Ring.rmodp -!Pdiv.IdomainMonic.modpE //.
rewrite mul_polyC !modp_scalel modp_mod modp_small //.
  by rewrite -[poly_of_divpoly p]coefK coef_poly (negPf Li) scale0r.
by rewrite size_polyXn -[X in (_ < X)%N](prednK F0) ltnS.
Qed.

Lemma DivPoly_vect_axiom : Vector.axiom (size hQ).-1 {divpoly h}.
Proof.
have hQM := monic_divpoly_quotient h.
pose f (p : {divpoly h}) := (\row_(j < (size hQ).-1) p`_j)%R.
have Lf : linear f.
  move=> a /= p1 p2; apply/rowP=> i.
  rewrite /f /= !mxE.
  rewrite -[rmodp]/Pdiv.Ring.rmodp -!Pdiv.IdomainMonic.modpE //.
  rewrite   modp_add mul_polyC !modp_scalel modp_mod.
  by rewrite !modp_small ?size_divpoly // coefD coefZ.
exists f => //.
pose g (r : 'rV_(size hQ).-1) : {divpoly h} := 
   (\sum_(i < (size hQ).-1) (r ord0 i) *: DivPoly_X i)%R.
exists g => Q; rewrite /f /g /=.
rewrite [X in _ = X]DivPoly_XE; apply: eq_bigr => i.
  by rewrite mxE.
apply/rowP => k.
  rewrite !mxE /=  poly_of_divpoly_sum  coef_sum /=.
  rewrite (bigD1 k) //= big1 => [|k1 k1Dk]; last first.
  rewrite -[rmodp]/Pdiv.Ring.rmodp -!Pdiv.IdomainMonic.modpE //.
  rewrite mul_polyC !modp_scalel modp_mod modp_small.
    rewrite coefZ coefXn.
    move/eqP/val_eqP : k1Dk; rewrite /= eq_sym => /negPf->.
    by rewrite mulr0.
  by rewrite size_polyXn -{2}(prednK F0) ltnS.
rewrite -[rmodp]/Pdiv.Ring.rmodp -!Pdiv.IdomainMonic.modpE //.
rewrite addr0 mul_polyC !modp_scalel modp_mod modp_small.
  by rewrite coefZ coefXn eqxx mulr1.
by rewrite size_polyXn /=  -{2}(prednK F0) ltnS.
Qed.

Definition DivPoly_vectMixin := VectMixin DivPoly_vect_axiom.

Canonical DivPoly_vectType := VectType A {divpoly h} DivPoly_vectMixin.

End Vector.
End PType.

Notation "{ 'divpoly'  h }" := (divpoly (divpoly_quotient h))
  (format "{ 'divpoly'  h }").

Section inPoly.

Variable A : comRingType.
Variable h : {poly A}.

Lemma inDivPoly_comp_horner (p q : {poly A}) :
 inDivPoly h (p \Po q) =
     (map_poly (DivPoly_const h) p).[inDivPoly h q].
Proof.
have hQM := monic_divpoly_quotient h.
rewrite comp_polyE /map_poly poly_def horner_sum /=.
apply: val_inj.
rewrite /= rmodp_sum // poly_of_divpoly_sum.
apply: eq_bigr => i  _.
rewrite !hornerE hornerXn /inDivPoly /=.
rewrite mul_polyC // !rmodp_scale //=.
by rewrite poly_of_divpolyX /= rmodp_exp // rmodp_mod.
Qed.

Lemma map_poly_div_inj : injective (map_poly (DivPoly_const h)).
Proof.
by apply: map_inj_poly => // x y /val_eqP /eqP /polyC_inj.
Qed.

End inPoly.