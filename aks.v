From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
Require Import more_thm divpoly.

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

Lemma dvdp_geom (R : comRingType) n (p : {poly R}) :
  p - 1 \is monic -> rdvdp (p - 1) (p ^+ n.+1 - 1).
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
rewrite /introspective exprM -rmodp_exp // (eqP mIp) rmodp_exp //.
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
Definition is_ipoly (R : ringType) (k s : nat) (p : {poly R}):= 
  forall m, is_iexp R k s m -> m ⋈[k] p.

(* This is 𝓜_k *)
Definition is_iexpm (R : ringType) (k s mk : nat) :=
   exists2 m, mk = (m %% k)%N & is_iexp R k s m.

Inductive is_iexpm_spec 
     (R : ringType) (k k1 s : nat) (mk : 'I_k1) : bool -> Prop :=
   is_iexpm_spec_true : 
    forall (m : nat),  (mk = m %% k :> nat)%N -> is_iexp R k s m -> 
      @is_iexpm_spec R k k1 s mk true
 | is_iexpm_spec_false :
    (forall (m : nat), is_iexp R k s m -> (mk != m %% k :> nat)%N) -> 
      @is_iexpm_spec R k k1 s mk false.

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

(* 105 *)
Lemma rmodn_trans {R : ringType} (p q h z : {poly R}) :
  h \is monic -> z \is monic -> rdvdp h z -> rmodp p z = rmodp q z -> rmodp p h  = rmodp q h.
Proof.
move=> hM zM /(rdvdp_trans hM zM) => /(_ (p - q)).
rewrite /rdvdp !rmodp_sub // !subr_eq0 => H /eqP H1; apply/eqP.
by apply: H.
Qed.


Definition poly_order {R : ringType} (h p :  {poly R}) (n : nat) : nat := 
  if [pick i | rmodp (p^+ (i : 'I_n.+1).-1.+1) h == 1] is Some v then
      [arg min_(i < v | (rmodp (p^+ i.-1.+1) h == 1)) i].-1.+1 else 0%N.

Lemma poly_order_leq (R : ringType) (h p : {poly R}) n :
  (0 < n -> poly_order h p n <= n)%N.
Proof.
by rewrite /poly_order; case: pickP => // x Hx; case: arg_minP => // [] [[|m]].
Qed.

Lemma poly_order_gt0_rmodp (R : ringType) (h p : {poly R}) n :
  (0 < poly_order h p n)%N ->  rmodp (p^+ poly_order h p n) h == 1.
Proof.
by rewrite /poly_order; case: pickP => // x Hx _; case: arg_minP.
Qed.

Lemma poly_order_eq0_rmodp (R : ringType) (h p : {poly R}) m n :
  (poly_order h p n = 0)%N -> (0 < m <= n)%N -> rmodp (p^+ m) h != 1.
Proof.
rewrite -[(_ <= n)%N]ltnS /poly_order; case: pickP => // HM _ /andP[m_gt0 mLn].
by have /= := HM (Ordinal mLn); case: (m) m_gt0 => //= k _ /idP/negP.
Qed.

Lemma poly_order_lt (R : ringType) (h p : {poly R}) m n :
  (0 < m < poly_order h p n)%N -> rmodp (p^+ m) h != 1.
Proof.
rewrite /poly_order; case: pickP=> [x Hx|]; last by rewrite ltn0 andbF.
case: arg_minP => // i Hi Hmin /andP[m_gt0 mLi].
have mLn : (m < n.+1)%N.
  by rewrite (leq_trans mLi) // (leq_trans _ (ltn_ord i)) //; case: (i : nat).
apply/negP; rewrite -[m]prednK // => /(Hmin (Ordinal mLn)) /=.
rewrite leqNgt; case: (i : nat) mLi  => [/=|j ->//].
by case: (m) m_gt0.
Qed.

(* 106  we reformulate it because we can't have order for poly directly *)
Lemma poly_order_rmod_inj (R : ringType) (h : {poly R}) k m n :
  h \is monic -> (1 < size h)%N -> (0 < k)%N -> rdvdp h ('X^k - 1) -> 
  (m < poly_order h 'X k)%N -> (n < poly_order h 'X k)%N ->
  rmodp 'X^m h = rmodp 'X^n h-> m = n.
Proof.
move=> hM hS k_gt0 hDxk.
wlog : m n / (m <= n)%N => [Hw |mLn] mLp nLp xmExn.
  case: (leqP m n) => [/Hw|nLm]; first by apply.
  by apply/sym_equal/Hw => //; apply: ltnW.
move: mLn; rewrite leq_eqVlt => /orP[/eqP//|mLn].
have xkE1 :  rmodp 'X^k h = 1.
  move: hDxk; rewrite /rdvdp rmodp_sub // [rmodp 1 _]rmodp_small.
    by rewrite subr_eq0 => /eqP.
  by rewrite size_polyC oner_neq0.
have [|o_gt0] := leqP (poly_order h 'X k) 0.
  have kB : (0 < k <= k)%N by rewrite k_gt0 leqnn.
  by rewrite leqn0 => /eqP/poly_order_eq0_rmodp /(_ kB) /eqP[].
pose v := (poly_order h 'X k - n + m)%N.
have /poly_order_lt/eqP[] : (0 < poly_order h 'X k - n + m < poly_order h 'X k )%nat.
  rewrite (leq_trans _ (_ : 0 + m < _)%N) //; last first.
    by rewrite ltn_add2r subn_gt0.
  rewrite -{2}[poly_order _ _ _](@subnK m); last by apply: ltnW.
  by rewrite ltn_add2r ltn_sub2l //.
rewrite exprD -rmodp_mulmr // xmExn rmodp_mulmr // -exprD subnK //.
  by apply/eqP/poly_order_gt0_rmodp.
by apply/ltnW.
Qed.

(* 107 *)
Lemma Mk_root_Mk (R : comRingType) (h : {poly R}) k s 
         (M : {set 'Z_k})  (p q : {poly R}) n  :
  Mk_spec R s M ->
  h \is monic -> (1 < size h)%N -> (0 < k)%N -> rdvdp h ('X^k - 1) -> 
  is_ipoly k s p -> is_ipoly k s q -> rmodp p h = rmodp q h ->
  n \in M -> rmodp ((p - q) \Po 'X^n) h = 0.
Proof.
move=> HM hM hS k_gt0 hDxk pI qI phEqh nIM; apply/eqP.
case: HM nIM => // m nE mI _.
have xkM := monic_Xn_sub_1 R k_gt0.
have F : rmodp 'X^n ('X^k - 1) = rmodp 'X^m ('X^k - 1) :> {poly R}.
  have F1 : rmodp 'X^k ('X^k - 1) = 1 :> {poly R}.
    rewrite -{1}['X^k](subrK (1 : {poly R})) addrC rmodp_add // rmodpp //.
    by rewrite addr0 rmodp_small // size_polyC oner_eq0 /= size_Xn_sub_1.
    rewrite (divn_eq m k) exprD mulnC exprM.
    rewrite mulrC -rmodp_mulmr // -[in RHS]rmodp_exp // F1 expr1n.
    by rewrite rmodp_mulmr // mulr1 nE.
rewrite comp_polyB rmodp_sub // subr_eq0; apply/eqP.
apply: etrans (_ : rmodp (p^+m) h = _).
  apply: rmodn_trans hDxk _ => //.
  rewrite -rmodp_compr // F rmodp_compr //.
  by apply/esym/eqP/pI.
apply: etrans (_ : rmodp (q^+m) h = _).
  by rewrite -rmodp_exp // phEqh rmodp_exp.
apply: esym.
apply: rmodn_trans hDxk _ => //.
rewrite -rmodp_compr // F rmodp_compr //.
by apply/esym/eqP/qI.
Qed.

(*108*)
Lemma Mk_rmodp_inj (R : fieldType) (h : {poly R}) k s 
         (M : {set 'Z_k})  (p q : {poly R})  :
  Mk_spec R s M ->
  monic_irreducible_poly h -> (0 < k)%N -> rdvdp h ('X^k - 1) -> 
  poly_order h 'X k = k -> (size p <= #|M|)%N -> (size q <= #|M|)%N ->
  is_ipoly k s p -> is_ipoly k s q -> rmodp p h = rmodp q h -> p = q.
Proof.
have [|M_gt0] := leqP #|M| 0%N.
  rewrite leqn0 => /eqP->; rewrite !leqn0 !size_poly_eq0.
  by move=> ? ? ? ? ? /eqP-> /eqP->.
move=> HMk hMI k_gt0 hDxk XoE pS qS pI qI /eqP.
have hS : (1 < size h)%N by case: hMI; case.
have hI : irreducible_poly h by case: hMI.
have hM : h \is monic by case: hMI.
have hQE : divpoly_quotient h = h by rewrite /divpoly_quotient hS hM.
pose l := map (fun i : 'I_ _ => (inDivPoly h 'X^i)) (enum M).
have Ul : uniq l.
  apply/(uniqP 0) => i j; rewrite !inE size_map -cardE => Hi1 Hj1.
  rewrite  !(nth_map ord0) -?cardE // => /val_eqP /eqP /= HH.
  suff : nth ord0 (enum M) i = nth ord0 (enum M) j.
    by have /(uniqP ord0) := enum_uniq (pred_of_set M); apply=> //; 
       rewrite inE -cardE.
  apply/val_inj => /=; move: HH.
  apply: (poly_order_rmod_inj _ _ k_gt0); rewrite hQE ?XoE //.
  - have: nth ord0 (enum M) i \in M by rewrite -mem_enum mem_nth // -cardE.
    by case: HMk => // m -> _; rewrite ltn_mod //.
  have: nth ord0 (enum M) j \in M by rewrite -mem_enum mem_nth // -cardE.
  by case: HMk => // m -> _; rewrite ltn_mod.
rewrite -subr_eq0 -rmodp_sub // => /eqP => u.
apply/eqP; rewrite -subr_eq0; apply/eqP/(@map_poly_div_inj _ h).
rewrite map_poly0.
apply (@roots_geq_poly_eq0 (DivPoly_idomainType hMI) _ l) => //; last first.
  rewrite (@size_map_poly _ _ (DivPoly_const_rmorphism h)) /=.
  rewrite size_map (leq_trans (size_add _ _)) //=  size_opp.
  by rewrite geq_max -cardE pS.
apply/allP=> i /mapP[j jI ->]; apply/eqP.
rewrite -inDivPoly_comp_horner //.
apply/val_inj => /=.
rewrite polyC0 hQE //.
apply: Mk_root_Mk => //.
  by apply/eqP; rewrite -subr_eq0 -rmodp_sub //; apply/eqP.
by rewrite -mem_enum.
Qed.

End AKS.

Notation " n '⋈[' k ] p" := (introspective n k p) 
  (at level 40, format "n  '⋈[' k ]  p").
