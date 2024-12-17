From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section UPoly.

Variable R : ringType.

Fixpoint addzPoly (l1 l2 : seq int) := 
  if l1 is a :: l1 then 
    if l2 is b :: l2 then (a + b) :: addzPoly l1 l2 else a :: l1
  else l2.

Definition int2Poly (l : seq int) : {poly R} :=  Poly [seq i%:~R | i <- l].

Lemma int2Poly_nil : int2Poly [::] = 0.
Proof. by []. Qed.

Lemma int2Poly_cons a l : int2Poly (a :: l) = a%:~R + 'X * int2Poly l.
Proof.
rewrite /int2Poly /= cons_poly_def addrC commr_polyX.
congr (_ + _ * _).
apply/polyP => i; rewrite coefMrz !coefC //=.
by case: i => //= i; rewrite mul0rz.
Qed.

Lemma int2Poly_polyC a : int2Poly [::a] = a%:~R.
Proof. by rewrite int2Poly_cons int2Poly_nil mulr0 addr0. Qed.

Lemma int2Poly_polyX : int2Poly [::0;1] = 'X.
Proof. by rewrite !int2Poly_cons int2Poly_nil mulr0 addr0 mulr1 add0r. Qed.

Lemma int2Poly_polyXn n : int2Poly (rcons (nseq n 0) 1) = 'X^n.
Proof.
elim: n => /= [|n IH].
  by rewrite !int2Poly_cons int2Poly_nil mulr0 addr0.
by rewrite int2Poly_cons IH add0r exprS.
Qed.

Lemma addzPoly_correct l1 l2 : 
  int2Poly (addzPoly l1 l2) = int2Poly l1 + int2Poly l2.
Proof.
elim: l1 l2 => /= [l2 | a l1 IH [|b l2]]; first by rewrite add0r.
  by rewrite addr0.
rewrite !int2Poly_cons IH  rmorphD /= mulrDr.
by rewrite -!addrA; congr (_ + _); rewrite addrCA.
Qed.

Fixpoint oppzPoly (l : seq int) := 
  if l is a :: l then (- a) :: oppzPoly l else [::].

Lemma oppZPoly_correct (l : seq int) : 
  int2Poly (oppzPoly l) = - int2Poly l.
Proof.
elim: l => /= [|a l IH]; first by rewrite !int2Poly_nil oppr0.
by rewrite !int2Poly_cons IH !rmorphN /= opprD -mulrN.
Qed.

Fixpoint mulzPoly (l1 l2 : seq int) := 
  if l1 is a :: l1 then 
    if l2 is b :: l2 then
      (a * b) :: addzPoly (addzPoly [seq i * b | i <- l1] [seq a * i | i <- l2])
                          (0 :: mulzPoly l1 l2) else [::]
  else [::].

Lemma intseqlPoly_correct (a : int) (l : seq int) : 
  int2Poly [seq a * i | i <- l] = a%:~R * int2Poly l.
Proof.
elim: l => /= [|b l IH]; first by rewrite !int2Poly_nil mulr0.
rewrite !int2Poly_cons IH !rmorphM /= mulrDr; congr (_ + _).
by rewrite  -commr_polyX -mulrA; congr (_ * _); rewrite commr_polyX.
Qed.

Lemma intseqrPoly_correct (a : int) (l : seq int) : 
  int2Poly [seq i * a | i <- l] = int2Poly l * a%:~R.
Proof.
elim: l => /= [|b l IH]; first by rewrite !int2Poly_nil mul0r.
rewrite !int2Poly_cons IH !rmorphM /= mulrDl; congr (_ + _).
by rewrite mulrA.
Qed.

Lemma mulzPoly_correct l1 l2 : 
  int2Poly (mulzPoly l1 l2) = int2Poly l1 * int2Poly l2.
Proof.
elim: l1 l2 => /= [l2 | a l1 IH [|b l2]]; first by rewrite mul0r.
  by rewrite mulr0.
rewrite !(IH, int2Poly_cons, addzPoly_correct,
          intseqlPoly_correct, intseqrPoly_correct).
rewrite rmorphM /= !(mulrDr, mulrDl) mulr0 add0r.
rewrite -!addrA; congr (_ + (_ + (_ + _))); first by rewrite mulrA.
  by rewrite -commr_polyX -mulrA; congr (_ * _); rewrite commr_polyX.
rewrite -mulrA; congr (_ * _).
by rewrite -commr_polyX -mulrA; congr (_ * _); rewrite commr_polyX.
Qed.

Lemma int_natmul (R1 : ringType) n : n %:R %:~R = n%:R :> R1.
Proof. by elim: n => //= n IH; rewrite -!natr1 rmorphD /= IH. Qed.

Definition isZPoly (p : {poly R}) := exists l : seq int, p = int2Poly l.

Lemma isZPoly_Poly_consr a l : isZPoly (Poly (a :: l)) -> isZPoly (Poly l).
Proof.
case => l1 /polyP Hl; exists (behead l1).
apply/polyP => i; have := Hl i.+1; rewrite !coefE /=.
by case: (l1) => [|b l2]; rewrite //= nth_nil.
Qed.

Definition isZ (a : R) := exists b : int, a = b%:~R.

Lemma isZ0 : isZ 0.
Proof. by exists 0. Qed.

Lemma isZ_int z : isZ (z%:~R).
Proof. by exists z. Qed.

Lemma isZPoly_Poly_consl a l : isZPoly (Poly (a :: l)) -> isZ a.
Proof.
case => l1 /polyP /(_ 0); rewrite !coefE /=.
case: l1 => [->//=|b l1 -> /=]; first by exact: isZ0.
by apply: isZ_int.
Qed.

Lemma polyC_intr (R1 : ringType) (z : int) : (z%:~R)%:P = z%:~R :> {poly R1}.
Proof. by rewrite rmorph_int. Qed.

Lemma isZPoly_Poly_cons a l : 
  isZ a -> isZPoly (Poly l) -> isZPoly (Poly (a :: l)).
Proof.
case => b -> [l1 /polyP Hl1]; exists (b :: l1).
apply/polyP => [] [|i]; first by rewrite !coefE.
by have := Hl1 i; rewrite int2Poly_cons -polyC_intr !coefE /= add0r.
Qed.

Lemma isZPoly_polyC a : isZPoly a%:R.
Proof. by exists [::a%:R]; have := int2Poly_polyC a%:R; rewrite int_natmul. Qed.

Lemma isZPoly_polyX : isZPoly 'X.
Proof. by exists [::0; 1]; have := int2Poly_polyX. Qed.

Lemma isZPoly_polyXn n : isZPoly 'X^n.
Proof.
by exists ((rcons (nseq n 0) 1) : seq int); have := int2Poly_polyXn n.
Qed.

Lemma isZPolyN p : isZPoly p -> isZPoly (- p).
Proof.
case => l ->.
by exists (oppzPoly l); have := oppZPoly_correct l.
Qed.

Lemma isZPolyD p1 p2 : isZPoly p1 -> isZPoly p2 -> isZPoly (p1 + p2).
Proof.
case => l1 -> [l2 ->].
by exists (addzPoly l1 l2); have := addzPoly_correct l1 l2.
Qed.

Lemma isZPolyM p1 p2 : isZPoly p1 -> isZPoly p2 -> isZPoly (p1 * p2).
Proof.
case => l1 -> [l2 ->].
by exists (mulzPoly l1 l2); have := mulzPoly_correct l1 l2.
Qed.

Inductive pexpr := 
| Pcons (a : nat) | Pxn (n : nat) | Px 
| Popp (p : pexpr) | Padd (p1 p2 : pexpr) | Pmult (p1 p2 : pexpr).

Fixpoint pexpr2poly (e : pexpr) : {poly R} :=
match e with
| Pcons a => a%:R
| Pxn n => 'X^n 
| Px => 'X
| Popp p => - (pexpr2poly p)
| Padd p1 p2 => pexpr2poly p1 + pexpr2poly p2
| Pmult p1 p2 => pexpr2poly p1 * pexpr2poly p2
end.

Lemma isZPoly_pexpr2poly e : isZPoly (pexpr2poly e).
Proof.
elim: e => /= [a|n||p Zp|p1 Zp1 p2 Zp2|p1 Zp1 p2 Zp2].
- by apply: isZPoly_polyC.
- by apply: isZPoly_polyXn.
- by apply: isZPoly_polyX.
- by apply: isZPolyN.
- by apply: isZPolyD.
by apply: isZPolyM.
Qed.

End UPoly.

Section U2Poly.
(* toto *)
Variable R T : ringType.

Hypothesis R_char : forall m n, m%:R = n%:R :> R -> m = n.

Lemma Rt_char z1 z2 : z1%:~R = z2%:~R :> R -> z1 = z2.
Proof.
wlog Hz : z1 z2 / (z1 <= z2) => [Hz|Hz1].
  case: (Num.Theory.lerP z1 z2); first by apply: Hz.
  by move=> Hz1 Hz2; apply/sym_equal/Hz; first by apply: Order.POrderTheory.ltW.
suff Hz2 : z2 - z1 = 0 by rewrite -(subrK z1 z2) Hz2 add0r.
have : 0 <= z2 - z1 by rewrite Num.Theory.subr_ge0.
have : (z2 - z1)%:~R = 0 :> R by rewrite rmorphB /= Hz1 subrr.
by rewrite /intmul; case: (_ - _) => //= n /(@R_char n 0) ->.
Qed.

Lemma nth_map_f (T1 T2 : Type) x (f : T1 -> T2) n s :
   nth (f x) [seq f i  | i <- s] n = f (nth x s n).
Proof. by elim: n s => [|? ?] []. Qed.

Lemma X_lreg (R1 : ringType) : GRing.lreg ('X : {poly R1}).
Proof. by apply/monic_lreg/monicX. Qed.

Lemma ptransferC l a : int2Poly R l = a%:R -> int2Poly T l = a%:R.
Proof.
elim: l a => [|b l IH] /= a.
  rewrite !int2Poly_nil => Ha.
  suff -> : a = 0 by [].
  apply: (@R_char _ 0%R).
  have /polyP/(_ 0) := Ha.
  by rewrite !(coefMrz, coefE) eqxx.
rewrite !int2Poly_cons => Hb.
have bE : b = a.
  apply: Rt_char.
  have /polyP/(_ 0) := Hb.
  by rewrite !(coefMrz, coefE) eqxx addr0.
rewrite -[a%:R]addr0 bE; congr (_ + _).
rewrite (IH 0) ?mulr0 //.
apply: X_lreg; rewrite mulr0.
by rewrite -[LHS](addKr b%:~R) Hb bE addrC subrr.
Qed.

Lemma coef_int2Poly (R1 : ringType) l i : (int2Poly R1 l)`_i = (l`_i)%:~R.
Proof.
elim: l i => [i|a l IH [|i]/=].
- by rewrite int2Poly_nil !coefE; case: i.
- by rewrite int2Poly_cons !coefE /= addr0 coefMrz !coefE eqxx.
rewrite int2Poly_cons !(coefMrz, coefE) /= mul0rz add0r.
by rewrite -IH /int2Poly coefE.
Qed.

Lemma ptransferX l : int2Poly R l = 'X -> int2Poly T l = 'X.
Proof.
move=> /polyP Hp; apply/polyP => i.
have := Hp i; rewrite !(coef_int2Poly, coefE) /=.
case: eqP => _ Hq.
  suff->: l`_i = 1 by [].
  by apply: Rt_char.
suff->: l`_i = 0 by [].
by apply: Rt_char.
Qed.

Lemma ptransferXn l n : int2Poly R l = 'X^n -> int2Poly T l = 'X^n.
Proof.
move=> /polyP Hp; apply/polyP => i.
have := Hp i; rewrite !(coef_int2Poly, coefE) /=.
case: eqP => _ Hq.
  suff->: l`_i = 1 by [].
  by apply: Rt_char.
suff->: l`_i = 0 by [].
by apply: Rt_char.
Qed.

Lemma ptransferN l1 l2 : 
  - int2Poly R l1 = int2Poly R l2 -> - int2Poly T l1 = int2Poly T l2.
Proof.
move/polyP => Hi; apply/polyP=> i; move: (Hi i).
rewrite /int2Poly !coefE.
rewrite -[(0 : R)]/(0%:~R) -[(0 : T)]/(0%:~R) !nth_map_f -!rmorphN /=.
by move=> /Rt_char->.
Qed.

Lemma ptransferD l1 l2 l3 : 
  int2Poly R l1 + int2Poly R l2 = int2Poly R l3 ->
  int2Poly T l1 + int2Poly T l2 = int2Poly T l3.
Proof.
move/polyP => Hi; apply/polyP=> i; move: (Hi i).
rewrite /int2Poly !coefE.
rewrite -[(0 : R)]/(0%:~R) -[(0 : T)]/(0%:~R) !nth_map_f -!rmorphD /=.
by move=> /Rt_char->.
Qed.

Lemma ptransferM l1 l2 l3 : 
  int2Poly R l1 * int2Poly R l2 = int2Poly R l3 ->
  int2Poly T l1 * int2Poly T l2 = int2Poly T l3.
Proof.
move/polyP => Hi; apply/polyP=> i; move: (Hi i).
rewrite /int2Poly !coefE !coefM.
rewrite -[(0 : R)]/(0%:~R) -[(0 : T)]/(0%:~R) !nth_map_f .
under eq_bigr do rewrite !coefE -[(0 : R)]/(0%:~R) !nth_map_f -rmorphM /=.
rewrite -rmorph_sum /= => /Rt_char <-; rewrite rmorph_sum /=.
apply: eq_bigr => j _.
by rewrite rmorphM /= !coefE -[(0 : T)]/(0%:~R) !nth_map_f.
Qed.

Lemma int2PolyN R1 l : 
  int2Poly R1 [seq - i | i <- l] = - int2Poly R1 l.
Proof.
apply/polyP=> i.
by rewrite !(coef_int2Poly, coefE) /= -[0]oppr0 nth_map_f oppr0 rmorphN.
Qed. 

Lemma ptransferI l1 l2 : 
  int2Poly R l1 = int2Poly R l2 -> int2Poly T l1 = int2Poly T l2.
Proof.
move=> /polyP Hp; apply/polyP => i.
by have := Hp i; rewrite !coef_int2Poly => /Rt_char->.
Qed.

Fixpoint Ladd (l1 l2 : seq int) := 
  if l1 is a :: l1 then 
    if l2 is b :: l2 then (a + b) :: (Ladd l1 l2) else a :: l1 else l2.

Fixpoint Lmul (l1 l2 : seq int) := 
  if l1 is a :: l1 then
    Ladd ([seq a * i | i <- l2]) (0 :: Lmul l1 l2) else [::]. 

Lemma Ladd_correct (R1 : ringType) l1 l2 :
  int2Poly R1 (Ladd l1 l2) = int2Poly R1 l1 + int2Poly R1 l2.
Proof.
elim: l1 l2 => /= [l2|a l1 IH [|b l2]]; first by rewrite int2Poly_nil add0r.
  by rewrite int2Poly_cons int2Poly_nil addr0.
rewrite !int2Poly_cons rmorphD /= IH -!addrA mulrDr; congr (_ + _).
by rewrite addrCA.
Qed.

Lemma int2Poly_scal R1 a l : 
  int2Poly R1 [seq a * i  | i <- l] = a%:~R * int2Poly R1 l.
Proof.
elim: l => /= [|b l IH]; first by rewrite !int2Poly_nil mulr0.
rewrite !int2Poly_cons mulrDr -rmorphM /= IH; congr (_ + _).
by rewrite -commr_polyX -!mulrA commr_polyX.
Qed.

Lemma Lmul_correct  (R1 : ringType) l1 l2 :
  int2Poly R1 (Lmul l1 l2) = int2Poly R1 l1 * int2Poly R1 l2.
Proof.
elim: l1 l2 => /= [l2|a l1 IH l2]; first by rewrite int2Poly_nil mul0r.
rewrite /= int2Poly_cons Ladd_correct int2Poly_scal.
by rewrite int2Poly_cons add0r IH mulrDl mulrA.
Qed.

Lemma ptransferE e l : 
 pexpr2poly R e = int2Poly R l -> pexpr2poly T e = int2Poly T l.
Proof.
elim: e l => /= [a l Ha|n l Hl|l Hl|p Hp l H|e1 He1 e2 He2 l Hl
                 |e1 He1 e2 He2 l Hl].
- by apply/sym_equal/ptransferC.
- by apply/sym_equal/ptransferXn.
- by apply/sym_equal/ptransferX.
- rewrite -[RHS]opprK -int2PolyN (Hp [seq - i  | i <- l]) //.
  by rewrite int2PolyN -H opprK.
- case: (isZPoly_pexpr2poly R e1) => l1 H1l1.
  have -> := He1 _ H1l1.
  case: (isZPoly_pexpr2poly R e2) => l2 H1l2.
  have -> := He2 _ H1l2.
  rewrite -Ladd_correct.
  apply: ptransferI.
  rewrite Ladd_correct.
  by rewrite -H1l1 -H1l2.
case: (isZPoly_pexpr2poly R e1) => l1 H1l1.
have -> := He1 _ H1l1.
case: (isZPoly_pexpr2poly R e2) => l2 H1l2.
have -> := He2 _ H1l2.
rewrite -Lmul_correct.
apply: ptransferI.
rewrite Lmul_correct.
by rewrite -H1l1 -H1l2.
Qed.

End U2Poly.