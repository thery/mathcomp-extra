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
    neodup (knuth_exchange m1) ++ ceswap :: knuth_jump_rec _ m1 (2^m1.-1)
  else [::].

End Knuth.

Lemma cfun_eswap_eacat_nseq a b c d :
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
  odd k -> i <= k + 1 -> let j := i - uphalf k in
  cfun (knuth_jump k) 
    [tuple of eocat (nseq (a + i) false ++ nseq b true)
                    (nseq a false ++ nseq (b + i) true)] =
     eocat (nseq (a + i - j) false ++ nseq (b + j) true)
           (nseq (a + j) false ++ nseq (b + i - j) true) :> seq _.
Proof.
move=> kO jLk1 j.
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
