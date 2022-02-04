From mathcomp Require Import all_ssreflect perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  Definition of the Knuth exchange sorting algorithm                        *)
(*                                                                            *)
(*      knuth_merge == the connector that links i to i.+1 for i odd           *)
(*  knuth_merge_rec == the recursive connect that calls itself on             *)
(*                       the even and odd parts and then apply Batcher_merge  *)
(*   knuth_exchange == the recursive connect that calls itself on             *)
(*                       the even and odd parts and then apply Batcher_merge  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Knuth.

Variable d : unit.
Variable A : orderType d.

Definition clink_eswap m : {ffun 'I_m -> 'I_m} :=
  [ffun i : 'I_ _ => if odd i then ipred i else inext i].

Lemma clink_eswap_proof m : 
  [forall i : 'I_m, clink_eswap _ (clink_eswap _ i) == i].
Proof.
apply/forallP => i /=; apply/eqP/val_eqP; rewrite !ffunE.
have m_gt0 : 0 < m by apply: leq_ltn_trans (ltn_ord i).
have [/= iO|iE] := boolP (odd i); rewrite ?(val_inext, val_ipred) /=.
  case: (ltngtP i 0) => // [o_gt0 | iE]; last by rewrite iE in iO.
  rewrite -[odd _]negbK -oddS prednK // iO val_inext val_ipred.
  rewrite -[i.-1 == _]eqSS !prednK //.
  by rewrite [(i : nat) == m]eqn_leq [m <= _]leqNgt ltn_ord andbF.
have [iE1 | /eqP iD] := (i : nat) =P m.-1.
  by rewrite (negPf iE) !val_inext /= iE1 !eqxx.
by rewrite oddS (negPf iE) /= /= val_ipred /= val_inext /= (negPf iD).
Qed.
  
Definition ceswap {m} := connector_of (clink_eswap_proof m).

Lemma cfun_eswap n (t : n.-tuple A) : 
  cfun ceswap t = 
  [tuple
    if odd i then max (tnth t i) (tnth t (ipred i))
    else min (tnth t i) (tnth t (inext i)) | i < n].
Proof.
apply: eq_from_tnth => i /=.
rewrite /ceswap /cfun /=.
rewrite !tnth_map /= !tnth_ord_tuple ffunE.
have [iO|iE] := boolP (odd i); last by rewrite ifT // val_inext; case: eqP.
case: leqP => [iLip|] //.
suff -> : ipred i = i by rewrite maxxx minxx.
apply/val_eqP =>> /=; move: iLip; rewrite !val_ipred /=.
by case: (i : nat) => //= i1; rewrite ltnn.
Qed.

Lemma tcast_eswap m1 m2 (m2Em1 : m2 = m1) (t : m2.-tuple A) :
  cfun ceswap (tcast m2Em1 t) = tcast m2Em1 (cfun ceswap t).
Proof.
case: (ltngtP m2 0) => // [m2_gt0|m2E]; last first.
  apply/val_eqP/eqP.
  set u := LHS; set v := RHS.
  have : size u = 0 by rewrite -m2E size_tuple.
  have : size v = 0 by rewrite -m2E size_tuple.
  by case: u; case: v.
pose i2 := Ordinal m2_gt0; have m1_gt0 : 0 < m1 by rewrite -m2Em1.
pose i1 := Ordinal m1_gt0; pose a := tnth t i2.
apply/val_eqP/eqP/(@eq_from_nth _ a) => [|i Hi].
  rewrite /= val_tcast /= !size_map /=.
  by do 2 rewrite -fintype.enumT -enum_ord size_enum_ord.
rewrite /= size_map -enum_ord size_enum_ord in Hi.
rewrite /= (nth_map i1); last by rewrite -enum_ord size_enum_ord.
rewrite -enum_ord nth_enum_ord // val_tcast /= (nth_map i2); last first.
   by rewrite -enum_ord size_enum_ord m2Em1.
rewrite -[fintype.enum 'I_m2]enum_ord  nth_enum_ord ?m2Em1 //.
suff ci2iEci1i : clink ceswap (nth i2 (enum 'I_m2) i) = 
                 clink ceswap (nth i1 (enum 'I_m1) i) :> nat.
  congr (if _ then min _ _ else max _ _); first by rewrite ci2iEci1i.
  - by rewrite !(tnth_nth a) val_tcast !nth_enum_ord // m2Em1.
  - by rewrite !(tnth_nth a) val_tcast /= ci2iEci1i.
  - by rewrite !(tnth_nth a) val_tcast !nth_enum_ord // m2Em1.
  by rewrite !(tnth_nth a) val_tcast /= ci2iEci1i.
rewrite !ffunE.
have im2Eim1 : nth i2 (enum 'I_m2) i = nth i1 (enum 'I_m1) i :> nat.
  by rewrite !nth_enum_ord // m2Em1.
rewrite im2Eim1; case: odd; first by rewrite !val_ipred im2Eim1.
by rewrite !val_inext im2Eim1 [X in X.-1]m2Em1.
Qed.

Definition clink_knuth_jump m k : {ffun 'I_m -> 'I_m} :=
  if odd k then 
    [ffun i : 'I_ _ => if odd i then iadd k i else isub k i]
  else [ffun i => i].

Lemma clink_knuth_jump_proof m k : 
  [forall i : 'I_m, clink_knuth_jump _ k (clink_knuth_jump _ k i) == i].
Proof.
rewrite /clink_knuth_jump.
have [/= kO|kI] := boolP (odd k);
     apply/forallP => i /=; apply/eqP/val_eqP; rewrite !ffunE //.
have m_gt0 : 0 < m by apply: leq_ltn_trans (ltn_ord i).
have [/= iO|iE] := boolP (odd i); rewrite ?(val_iadd, val_isub) /=.
  case: ltnP => [kiLm|mLki]; last first.
    by rewrite iO !val_iadd [k + i < m]ltnNge mLki /= [k + i < m]ltnNge mLki.
  by rewrite oddD iO kO /= ?(val_iadd, val_isub) /= kiLm leq_addr addnC addnK.
case: leqP => [kLi|iLk]; last first.
  by rewrite (negPf iE) !val_isub [k <= i]leqNgt iLk /= [k <= i]leqNgt iLk.
rewrite oddB // (negPf iE) kO /= ?(val_iadd, val_isub) /= kLi.
by rewrite addnC subnK // ifT.
Qed.
  
Definition knuth_jump {m} k := connector_of (clink_knuth_jump_proof m k).

Lemma cfun_knuth_jump n k (t : n.-tuple A) : 
  odd k ->
  cfun (knuth_jump k) t = 
  [tuple
    if odd i then min (tnth t i) (tnth t (iadd k i))
    else max (tnth t i) (tnth t (isub k i)) | i < n].
Proof.
move=> kO; apply: eq_from_tnth => i /=.
rewrite /knuth_jump /cfun /=.
rewrite !tnth_map /= !tnth_ord_tuple.
rewrite /clink_knuth_jump kO ffunE.
have [iO|iE] := boolP (odd i).
  by rewrite ifT // val_iadd; case: ltnP => // *; apply: leq_addl.
rewrite val_isub; case: (leqP k) => [kLi|iLk]; last first.
  suff -> : isub k i = i by rewrite minxx maxxx if_same.
  by apply/val_eqP; rewrite /= val_isub leqNgt iLk.
rewrite ifN // -ltnNge ltn_subLR //.
by case: (k) kO => // k1 _; rewrite addSn ltnS leq_addl.
Qed.

Lemma tcast_knuth_jump m1 m2 k (m2Em1 : m2 = m1) (t : m2.-tuple A) :
  cfun (knuth_jump k) (tcast m2Em1 t) = tcast m2Em1 (cfun (knuth_jump k) t).
Proof.
case: (ltngtP m2 0) => // [m2_gt0|m2E]; last first.
  apply/val_eqP/eqP.
  set u := LHS; set v := RHS.
  have : size u = 0 by rewrite -m2E size_tuple.
  have : size v = 0 by rewrite -m2E size_tuple.
  by case: u; case: v.
pose i2 := Ordinal m2_gt0; have m1_gt0 : 0 < m1 by rewrite -m2Em1.
pose i1 := Ordinal m1_gt0; pose a := tnth t i2.
apply/val_eqP/eqP/(@eq_from_nth _ a) => [|i Hi].
  rewrite /= val_tcast /= !size_map /=.
  by do 2 rewrite -fintype.enumT -enum_ord size_enum_ord.
rewrite /= size_map -enum_ord size_enum_ord in Hi.
rewrite /= (nth_map i1); last by rewrite -enum_ord size_enum_ord.
rewrite -enum_ord nth_enum_ord // val_tcast /= (nth_map i2); last first.
   by rewrite -enum_ord size_enum_ord m2Em1.
rewrite -[fintype.enum 'I_m2]enum_ord  nth_enum_ord ?m2Em1 //.
suff ci2iEci1i : clink (knuth_jump k) (nth i2 (enum 'I_m2) i) = 
                 clink (knuth_jump k) (nth i1 (enum 'I_m1) i) :> nat.
  congr (if _ then min _ _ else max _ _); first by rewrite ci2iEci1i.
  - by rewrite !(tnth_nth a) val_tcast !nth_enum_ord // m2Em1.
  - by rewrite !(tnth_nth a) val_tcast /= ci2iEci1i.
  - by rewrite !(tnth_nth a) val_tcast !nth_enum_ord // m2Em1.
  by rewrite !(tnth_nth a) val_tcast /= ci2iEci1i.
have im2Eim1 : nth i2 (enum 'I_m2) i = nth i1 (enum 'I_m1) i :> nat.
  by rewrite !nth_enum_ord // m2Em1.
by rewrite /knuth_jump /= /clink_knuth_jump; 
    case: (boolP (odd _)) => [kO|kE]; rewrite !ffunE im2Eim1; case: odd => //;
    rewrite ?(val_iadd, val_isub) ?im2Eim1 ?m2Em1.
Qed.

Fixpoint knuth_jump_rec m k r : network m :=
  if k is k1.+1 then (@knuth_jump m r) :: knuth_jump_rec m k1 (uphalf r).-1
  else [::].

Fixpoint knuth_exchange m : network (`2^ m) :=
  if m is m1.+1 then
    neodup (knuth_exchange m1) ++ ceswap :: knuth_jump_rec _ m1 ((`2^ m1).-1)
  else [::].

End Knuth.

Lemma cfun_eswap_eocat_nseq a b c d :
  a + b = c + d ->
  cfun ceswap [tuple of eocat (nseq a false ++ nseq b true)
                              (nseq c false ++ nseq d true)] =
     eocat (nseq (maxn a c) false ++ nseq (minn b d) true)
           (nseq (minn a c) false ++ nseq (maxn b d) true) :> seq _.
Proof.
move=> abEcd.
have abEm1 : a + b = maxn a c + minn b d.
  case: (leqP a c) => [aLc | cLa].
    by rewrite (minn_idPr _) // -(leq_add2l a) abEcd leq_add2r.
  by rewrite (minn_idPl _) // -(leq_add2l a) abEcd leq_add2r ltnW.
have abEm2 : a + b = minn a c + maxn b d.
  case: (leqP a c) => [aLc | cLa].
    by rewrite (maxn_idPl _) // -(leq_add2l a) abEcd leq_add2r.
  by rewrite (maxn_idPr _) // -(leq_add2l a) abEcd leq_add2r ltnW.
apply: (@eq_from_nth _ true) => [|i].
  rewrite /= [LHS]size_tuple card_ord size_eocat size_cat !size_nseq.
  by rewrite -abEm1.
rewrite [X in _ < X -> _]size_tuple => iLab.
pose x := Ordinal iLab.
rewrite cfun_eswap /= (nth_map x) /= -[i]/(x : nat); last first.
  by rewrite -enum_ord size_enum_ord.
rewrite -enum_ord !nth_ord_enum.
rewrite nth_eocat; last by rewrite !size_cat !size_nseq // -abEm1.
rewrite !(tnth_nth true) !nth_eocat /=; last 3 first.
- by rewrite !size_tuple.
- by rewrite !size_tuple.
- by rewrite !size_cat !size_nseq.
have i2Lab : i./2 < a + b by rewrite ltn_halfl -addnn.
have [iO|iE] := boolP (odd _).
  have i_gt0 : 0 < i by case: (i) iO.
  have i1E : ~~ odd i.-1 by rewrite -oddS prednK.
  rewrite val_ipred /= (negPf i1E).
  have -> : i.-1./2 = i./2.
    by rewrite -[X in _ = X./2]prednK // -uphalfE uphalf_half (negPf i1E).
  by rewrite !nth_cat_seqT geq_min; do 2 case: leqP => ?.
rewrite val_inext; case: eqP =>/= [i1E| _].
  have := iE; rewrite i1E -oddS prednK ?(leq_ltn_trans _ iLab) //.
  by rewrite addnn odd_double.
rewrite (negPf iE) /= uphalf_half (negPf iE) /= add0n.
by rewrite !nth_cat_seqT geq_max; do 2 case: leqP => ?.
Qed.

Lemma cfun_knuth_jump_eocat_nseq a b i k :
  odd k -> let j := i - uphalf k in
  cfun (knuth_jump k) 
    [tuple of eocat (nseq (a + i) false ++ nseq b true)
                    (nseq a false ++ nseq (b + i) true)] =
     eocat (nseq (a + i - j) false ++ nseq (b + j) true)
           (nseq (a + j) false ++ nseq (b + i - j) true) :> seq _.
Proof.
move=> kO j.
have jLi : j <= i by apply: leq_subr.
have aibE : a + i + b = a + (b + i) by rewrite [b + _]addnC addnA.
apply: (@eq_from_nth _ true) => [|v].
  rewrite /= [LHS]size_tuple card_ord size_eocat size_cat !size_nseq.
  suff -> : a + i - j + (b + j) = a + i + b by [].
  by rewrite [b + j]addnC !addnA subnK // (leq_trans jLi (leq_addl _ _)).
rewrite [X in _ < X -> _]size_tuple => iLab.
pose x := Ordinal iLab.
rewrite cfun_knuth_jump //= (nth_map x) /= -[v]/(x : nat); last first.
  by rewrite -enum_ord size_enum_ord.
rewrite -enum_ord !nth_ord_enum.
rewrite nth_eocat; last first.
  rewrite !size_cat !size_nseq //; last first.
  rewrite -!addnBA // -!addnA; congr (_ + _).
  by rewrite [_ + j]addnC addnC -!addnA.
rewrite !(tnth_nth true) !nth_eocat /=; last 3 first.
- by rewrite !size_cat !size_nseq addnAC addnA.
- by rewrite !size_cat !size_nseq addnAC addnA.
- by rewrite !size_cat !size_nseq addnAC addnA.
have v2Lab : v./2 < a + i + b by rewrite ltn_halfl -addnn.
have [vO|vE] := boolP (odd _).
  rewrite !nth_cat_seqT.
  have i_gt0 : 0 < v by case: (v) vO.
  rewrite val_iadd /=.
  case: leqP => [kvLaib|aibLc].
    rewrite vO nth_cat_seqT minxx.
    case: leqP => [aLv2|v2La]; last first.
      by rewrite leqNgt (leq_trans v2La (leq_addr _ _)).
    rewrite geq_halfr -addnn.
    case: (leqP (uphalf k) i) => [k2Li|iLk2].
      have i2E : i.*2 = j.*2 + k.+1.
        rewrite doubleB - [X in _ + X]odd_double_half oddS kO subnK //.
        by rewrite leq_double.
      rewrite -(leq_add2l k.+1) addnn addnC doubleD -addnA -i2E -doubleD.
      rewrite (leq_trans (leq_addr b.*2 _)) // -doubleD -addnn.
      by rewrite (leq_trans kvLaib) // leq_add2r.
    have -> : j = 0 by apply/eqP; rewrite subn_eq0 ltnW.
    by rewrite addn0 addnn -geq_halfr.
  rewrite oddD kO vO /= nth_cat_seqT.
  case: leqP => [aLv2|v2La]; last first.
    by rewrite minFb leqNgt (leq_trans v2La (leq_addr _ _)).
  rewrite minTb.
  case: (leqP i (uphalf k)) => [iLk2|k2Li].
    have /eqP jE0 : j == 0 by rewrite subn_eq0.
    rewrite jE0 addn0 aLv2 /=.
    have -> : (k + v)./2 = (k.+1 + v)./2.
      by rewrite addSn -uphalfE uphalf_half oddD kO vO.
    by rewrite geq_halfr addnC doubleD leq_add // -geq_halfr.
  have j_gt0 : 0 < j by rewrite subn_gt0.
  case: leqP => H1.
    rewrite geq_halfr in H1.
      rewrite geq_halfr doubleD doubleB addnBA.
      rewrite leq_subLR -doubleD (leq_trans H1) // leq_add2r.
      by rewrite -ltnS -[X in X <= _]odd_double_half oddS kO.
    by rewrite leq_double ltnW // -subn_gt0.
  rewrite halfD kO vO addnA /= in H1.
  rewrite addnBA //; last by apply : ltnW.
  by rewrite leq_subLR uphalf_half kO leqNgt H1.
rewrite val_isub /=.
case: leqP => [kLv|vLk].
  rewrite oddB // (negPf vE) /= kO !nth_cat_seqT.
  case: (leqP i (uphalf k)) => [iLk2|k2Li].
    have /eqP jE0 : j == 0 by rewrite subn_eq0.
    rewrite jE0 subn0.
    case: leqP => [aiLv2|v2Lai]; first by rewrite maxTb.
    rewrite maxFb; apply/idP/negP; rewrite -ltnNge -(ltn_add2r i).
    rewrite (leq_ltn_trans _ v2Lai) //.
    rewrite -{2}(subnK kLv) halfD oddB // kO (negPf vE) /=.
    by rewrite addnCA leq_add2l -[1]/(true : nat) -kO -uphalf_half.
  have j_gt0 : 0 < j by rewrite subn_gt0.
  case: (leqP (a + i - j) v./2) => [aijLv2|v2Laij]; last first.
    rewrite leqNgt (leq_trans v2Laij (leq_subr _ _)) maxFb.
    rewrite leqNgt -(ltn_add2r (uphalf k)) {1}uphalf_half kO addnCA /=.
    rewrite -(subnK kLv) // halfD oddB // kO (negPf vE) /= in v2Laij.
    by rewrite (leq_trans v2Laij) // -addnBA // leq_add2l subKn // ltnW.
  rewrite -addnBA //subKn in aijLv2; last by apply: ltnW.
  rewrite -(subnK kLv) // halfD oddB // kO (negPf vE) /= in aijLv2.
  rewrite addnCA -[1]/(true : nat) -kO -uphalf_half leq_add2r in aijLv2.
  by rewrite aijLv2 maxbT.
rewrite (negPf vE) maxxx !nth_cat_seqT.
case: (leqP i (uphalf k)) => [iLk2|k2Li].
  have /eqP-> : j == 0 by rewrite subn_eq0.
  by rewrite subn0.
have j_gt0 : 0 < j by rewrite subn_gt0.
  rewrite -addnBA // subKn; last by apply: ltnW.
case: leqP => [aiLv2|v2Lai].
  by rewrite (leq_trans _ aiLv2) // leq_add2l ltnW.
rewrite leqNgt ltn_halfl (leq_trans vLk) // doubleD.
rewrite (leq_trans _ (leq_addl _ _)) //.
by rewrite -[X in X <= _]odd_double_half uphalf_half kO doubleD !addSn.
Qed.

Lemma cfun_knuth_jump_eocat_nseq_up a b i k :
  odd k -> let j := i - uphalf k in
  i <= (uphalf k).*2 ->
  cfun (knuth_jump k) 
    [tuple of eocat (nseq (a + i) false ++ nseq b true)
                    (nseq a false ++ nseq (b + i) true)] =
     eocat (nseq (a + j + (i - j.*2)) false ++ nseq (b + j) true)
           (nseq (a + j) false ++ nseq (b + j + (i - j.*2)) true) :> seq _.
Proof.
move=> kO j iLk2. 
have jLij : j <= i - j.
  rewrite /j leq_subRL ?leq_subr // addnn doubleB.
  by rewrite leq_subLR ?leq_subr // -addnn leq_add2r.
rewrite -addnn subnDA [a + j + _]addnAC [b + j + _]addnAC.
rewrite -![_ + (_ - _) + j]addnA subnK // ![_ + (i - j)]addnBA ?leq_subr //.
by apply: cfun_knuth_jump_eocat_nseq.
Qed.

Lemma cfun_knuth_jump_rec_eocat_nseq a b i m k (H : _ = _) :
  i <= `2^ k ->
  nfun (knuth_jump_rec m k (`2^ k).-1) 
    (tcast H [tuple of eocat (nseq (a + i) false ++ nseq b true)
                    (nseq a false ++ nseq (b + i) true)]) =
     eocat (nseq (a + uphalf i) false ++ nseq (b + i./2) true)
           (nseq (a + i./2) false ++ nseq (b + uphalf i) true) :> seq _.
Proof.
elim: k a i b H => [/=|k IH/=] a i b H iL.
  rewrite val_tcast /=.
  by case: i H iL => [|[|]] // H _; rewrite /= ?(addn0, addn1).
rewrite tcast_knuth_jump.
set u := cfun _ _; have := (refl_equal (val u)).
have e2nk1_gt0 := e2n_gt0 k.+1.
rewrite [RHS]cfun_knuth_jump_eocat_nseq_up //; last 2 first.
- by rewrite -[odd _]negbK -oddS prednK // addnn odd_double.
- by rewrite uphalfE prednK // addnn doubleK -addnn.
set v := eocat _ _ => vuE.
have iLk : i - `2^ k <= i by apply: leq_subr.
have i2kLii2k : i - `2^ k <= i - (i - `2^ k).
  by rewrite leq_subRL // addnn doubleB leq_subLR -!addnn leq_add2r.
have H1 : size v = m.
  rewrite size_tuple -H !addnn; congr (_.*2).
  rewrite uphalfE prednK; last by rewrite double_gt0 e2n_gt0.
  rewrite doubleK -addnn subnDA.
  rewrite [a + _ + _]addnAC -[a + _ + _]addnA subnK //.
  by rewrite addnCA -addnA subnK // addnC.
rewrite size_tuple /= in H1.
have <- : tcast H1 [tuple of v] = tcast H u.
  by apply/val_eqP/eqP => /=; rewrite !val_tcast.
rewrite [X in X.-1]uphalfE prednK // [X in X./2]addnn doubleK IH //; last first.
  rewrite uphalfE prednK // addnn doubleK.
  rewrite leq_subLR.
  rewrite -addnn -addnA.
  case: (leqP (`2^ k) i) => [k2Li|iLk2].
    by rewrite subnK // leq_addl.
  have := ltnW iLk2.
    rewrite -subn_eq0 => /eqP->.
    by rewrite ltnW. 
have F : i - `2^ k <= i./2.
    by rewrite geq_halfr doubleB leq_subLR -addnn leq_add2r -addnn.
have G1 : (i - (i - `2^ k).*2)./2 = i./2 - (i - `2^ k).
  case: (boolP (odd i)) => [iO|iE]; last first.
    rewrite -[X in X - _.*2]odd_double_half (negPf iE) add0n.
    by rewrite -doubleB doubleK.
  rewrite -[X in X - _.*2]odd_double_half iO add1n subSn ?leq_double //.
  by rewrite -uphalfE -doubleB uphalf_double.
have G2 : uphalf (i - (i - `2^ k).*2) = odd i + i./2 - (i - `2^ k).
  rewrite uphalf_half G1 oddB //.
    rewrite odd_double addbF addnBA //.
  by rewrite -geq_halfr.
congr (eocat (nseq _ _ ++ nseq _  _) (nseq _ _ ++ nseq _ _)); apply/eqP.
- rewrite uphalfE prednK // addnn doubleK G2.
  by rewrite uphalf_half -!addnA eqn_add2l addnC -addnBA // -addnA subnK.
- rewrite uphalfE prednK ?(e2n_gt0 k.+1) // addnn doubleK.
  by rewrite G1 addnAC -addnA subnK.
- rewrite uphalfE prednK ?(e2n_gt0 k.+1) // addnn doubleK.
  by rewrite G1 addnAC -addnA subnK.
rewrite uphalfE prednK ?(e2n_gt0 k.+1) // addnn doubleK G2.
by rewrite uphalf_half -!addnA eqn_add2l addnC -addnBA // -addnA subnK.
Qed.

Lemma sorted_nfun_knuth_jump_rec_eocat_nseq a b i m k (H : _ = _) :
  i <= `2^ k ->
  sorted <=%O
  (nfun (knuth_jump_rec m k (`2^ k).-1) 
    (tcast H [tuple of eocat (nseq (a + i) false ++ nseq b true)
                    (nseq a false ++ nseq (b + i) true)])).
Proof.
move=> iL2k.
rewrite cfun_knuth_jump_rec_eocat_nseq //.
rewrite uphalf_half [odd _ + _]addnC !addnA.
case: odd; rewrite ?(addn0, addn1).
  rewrite eocat_nseq_catDS.
  by apply/isorted_boolP; set x := _.+1; set y := _.+1; exists (x, y).
rewrite eocat_nseq_catD.
by apply/isorted_boolP; set x := _ + _; set y := _ + _; exists (x, y).
Qed.

Lemma sorted_nfun_knuth_exchange m (t : (`2^ m).-tuple bool) :
  sorted <=%O (nfun (knuth_exchange m) t).
Proof.
elim: m t => [t|m IH t] /=; first by apply: tsorted01.
rewrite nfun_cat /= nfun_eodup.
have /isorted_boolP[[a1 b1] teH] := IH (tetake t).
have /isorted_boolP[[a2 b2] toH] := IH (totake t).
have /(@sym_equal _ _ _)a1b1E := congr1 size teH.
rewrite [X in _= X]size_tuple size_cat !size_nseq in a1b1E.
have /(@sym_equal _ _ _)a2b2E := congr1 size toH.
rewrite [X in _= X]size_tuple size_cat !size_nseq in a2b2E.
set u := [tuple of _].
have /val_eqP/eqP := refl_equal u.
rewrite [X in _ = X]/= teH toH; set v := eocat _ _ => uE.
have := refl_equal (size u).
  rewrite [X in size X = _]uE 
          !(size_tuple, size_eocat, size_cat, size_nseq) => Hv.
have {u uE}-> : u = tcast Hv [tuple of v].
  by apply/val_eqP; rewrite uE /= val_tcast.
set u1 := cfun _ _.
have /val_eqP/eqP := refl_equal u1.
rewrite [X in _ = val X]tcast_eswap [X in _ = X]val_tcast.
rewrite cfun_eswap_eocat_nseq ?a2b2E //.
have m1K : minn a1 a2 <= maxn a1 a2 by case: (ltngtP a1 a2) => // /ltnW.
rewrite -(subnK m1K) addnC.
have m2K : minn b1 b2 <= maxn b1 b2 by case: (ltngtP b1 b2) => // /ltnW.
rewrite -(subnK m2K) [_ + minn _ _]addnC.
set a := minn a1 a2; set b := minn b1 b2.
set i := maxn a1 a2 - minn a1 a2.
have F1 : a1 + b1 = a2 + b2 by rewrite a2b2E.
have -> : (maxn b1 b2 - minn b1 b2) = i by lia.
set v1 := eocat _ _ => u1E.
have := refl_equal (size u1).
  rewrite [X in size X = _]u1E 
          !(size_tuple, size_eocat, size_cat, size_nseq)
           => Hv1.
have {u1 u1E}-> : u1 = tcast Hv1 [tuple of v1].
  by apply/val_eqP; rewrite u1E /= val_tcast.
apply: sorted_nfun_knuth_jump_rec_eocat_nseq.
by rewrite -leq_double -!addnn -Hv1 !addnn leq_double addnAC leq_addl.
Qed.
Lemma sorted_knuth_exchange m : knuth_exchange m \is sorting.
Proof. apply/forallP => x; apply: sorted_nfun_knuth_exchange. Qed.
