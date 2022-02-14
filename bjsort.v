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
(*   iknuth_exchance_exchange == an iterative version of knuth that works     *)
(*                               directly on list                             *)
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

(** Iterative version *)

Fixpoint eotake (A : Type) d n (l : seq A) := 
 if d is d1.+1 then 
   if odd n then eotake d1 n./2 (otake l)
            else eotake d1 n./2 (etake l)
 else l.

Lemma eotake_mod (A : Type) d n (l : seq A) :
  eotake d (n %% `2^ d) l = eotake d n l.
Proof.
elim: d n l => //= d IH n l; rewrite odd_mod ?(odd_e2 d.+1) //.
case: (boolP (odd n)) => [nO|nE]; last first.
  rewrite -[in LHS](odd_double_half n) (negPf nE) add0n addnn.
  by rewrite -!muln2 -muln_modl muln2 doubleK IH.
rewrite -[in LHS](odd_double_half n) nO add1n modnS.
rewrite addnn -!muln2 -muln_modl !muln2 ifN.
  by rewrite -uphalfE uphalf_half odd_double doubleK IH.
apply/negP=> /dvdnP => [] [k H].
by move: (nO); rewrite -[n]odd_double_half nO addSn H -doubleMr odd_double.
Qed.

Lemma nth_eotake (A : Type) d n (l : seq A) a x :
  nth a (eotake d n l) x = nth a l ((n %% `2^ d) + `2^ d * x).
Proof.
elim: d n l a x => /= [n l a x|d IH n l a x]; first by rewrite modn1 mul1n.
case: (boolP (odd n)) => [nO|nE]; rewrite addnn; last first.
  rewrite IH nth_etake doubleD doubleMl.
  by rewrite -muln2 muln_modl !muln2 -[in RHS](odd_double_half n) (negPf nE).
rewrite IH nth_otake doubleD -addSn doubleMl.
rewrite -muln2 muln_modl !muln2.
rewrite -[in RHS](odd_double_half n) nO add1n modnS ifN //.
apply/negP=> /dvdnP => [] [k H].
by move: (nO); rewrite -[n]odd_double_half nO addSn H -doubleMr odd_double. 
Qed.

Lemma nth_eotake_div (A : Type) d (l : seq A) a n :
  nth a (eotake d n l) (n %/ `2^ d) = nth a l n.
Proof. by rewrite nth_eotake mulnC addnC -divn_eq. Qed.

Lemma eq_size_eotake (A:  Type) d n (l1 l2 : seq A) :
  size l1 = size l2 -> size (eotake d n l1) = size (eotake d n l2).
Proof.
elim: d n l1 l2 => //= d IH n l1 l2 sl1Esl2.
case: odd; apply: IH; first by apply: eq_size_otake.
by apply: eq_size_etake.
Qed.

Lemma gtn_size_eotake (A : Type) k p i (l : seq A) :
   i < `2^ p -> k < size (eotake p i l) -> i + `2^ p * k < size l.
Proof.
elim: p i k l => [[]// k l _|p IH i k l iLk kLs]; first by rewrite mul1n.
rewrite /= in kLs.
case: (boolP (odd _)) kLs => iO /IH; 
  rewrite ?(size_otake, size_etake) ltn_halfl -addnn -e2Sn => /(_ iLk) ikLs.
  rewrite -(odd_double_half i) iO -addSn -doubleS.
  rewrite e2Sn addnn -doubleMl -doubleD.
  rewrite -(odd_double_half (size l)).
  apply: leq_trans (leq_addl _ _).
  by rewrite leq_double addSn.
move: ikLs.
rewrite uphalf_half -[X in i + _ < X](odd_double_half (size l)).
rewrite -[i as X in (X + _ < _)]odd_double_half (negPf iO) add0n.
rewrite e2Sn addnn -doubleMl -doubleD.
case: odd => /=; first by rewrite !ltnS leq_double.
by rewrite ltn_double.
Qed.

Section IKnuthExchance.

Variables (d : unit) (A : orderType d).

Definition swap i j (l : seq A) :=
  if l is a :: l1 then
    let l1 := take i l in  
    let l2 := drop i l in
    let l3 := behead l2 in
    let l4 := take (j - i).-1 l3 in
    let l5 := drop (j - i).-1 l3 in
    let v1 := head a l2 in
    let v2 := head a l5 in
    l1 ++ min v1 v2 :: l4 ++ max v1 v2 :: behead l5
  else [::].

Fixpoint iter1_aux k n p i (l : seq A) :=
  if k is k1.+1 then
  if i + p < n then
     iter1_aux k1 n p i.+1 
       (if odd (i %/ p) then l else swap i (i + p) l)
  else l
  else l.

Definition iter1 p (l : seq A) := 
  iter1_aux (size l).+1 (size l) p 0 l.

Fixpoint iter2_aux k n p q i (l : seq A) :=
  if k is k1.+1 then
  if i + q < n then
     iter2_aux k1 n p q i.+1 
       (if odd (i %/ p) then l else swap (i + p) (i + q) l )
  else l
  else l.

Definition iter2 p q (l : seq A) := 
  iter2_aux (size l).+1 (size l) p q 0 l.

Fixpoint iter3_aux k p q (l : seq A) :=
  if k is k1.+1 then
  if q > p then
     iter3_aux k1 p q./2 (iter2 p q l)
  else l
  else l.

Definition iter3 top p (l : seq A) := iter3_aux (size l).+1 p top l.

Fixpoint iknuth_exchance_aux k top p (l : seq A) :=
  if k is k1.+1 then
  if p > 0 then
     let l1 := iter3 top p (iter1 p l) in
     iknuth_exchance_aux k1 top p./2 l1
  else l
  else l.

Definition iknuth_exchance (l : seq A) : seq A :=
  let top := `2^ ((up_log 2 (size l)).-1) in
  iknuth_exchance_aux (size l) top top l.

End IKnuthExchance.

Compute iknuth_exchance [::8; 7; 6; 5; 4; 3; 2; 1].
Compute iknuth_exchance [::true; true; true; true; false; false; false; false].

Section IKnuthExchangeProof.

Variables (d : unit) (A : orderType d).

(******************************************************************************)
(* Proof for swap                                                             *)
(******************************************************************************)

Lemma perm_swap (l : seq A) i j : 
   i < j < size l -> perm_eq (swap i j l) l.
Proof.
case: l => //= a l /andP[iLj jLs].
rewrite -[X in perm_eq _ X](cat_take_drop i).
rewrite perm_cat2l.
have := size_drop i (a :: l).
rewrite /= -[_ - _]prednK; last first.
  by rewrite subn_gt0 (ltn_trans iLj).
case: drop => //= a1 l1.
rewrite prednK; last by rewrite subn_gt0 (ltn_trans iLj).
move=> sl1E.
rewrite -[X in perm_eq _ (_ :: X)](cat_take_drop (j - i).-1).
move: (sl1E) => sl1E1.
have jBiL : j - i < (size l).+1 - i.
  rewrite -(ltn_add2r i) !subnK //; last by apply: ltnW.
  by apply: (leq_trans (ltnW iLj) (ltnW _)).
rewrite -[l1](cat_take_drop (j - i).-1) size_cat size_take ifT in sl1E;
      last by rewrite -ltnS sl1E1 prednK ?subn_gt0.
case: drop sl1E => [|b l2 _] /=.
  rewrite addn0 prednK ?subn_gt0 // => jBiE.
  by rewrite jBiE ltnn in jBiL.
case: (ltP a1 b) => _ //.
rewrite -!seq.cat_cons -!cat_rcons perm_cat2r /=.
set l4 := take _ _.
have <- := perm_rcons b (rcons l4 a1).
rewrite perm_sym.
have <- := perm_rcons a1 (rcons l4 b).
rewrite -[X in perm_eq X]cats0 !cat_rcons.
rewrite -[X in perm_eq _ X]cats0 !cat_rcons.
rewrite perm_cat2l.
by have <- := perm_rcons b [::a1].
Qed.

Lemma size_swap (l : seq A) i j :
  i < j < size l -> size (swap i j l) = size l.
Proof. by move=> jB; apply/perm_size/perm_swap. Qed.

Lemma nth_swap a i j (l : seq A) k : 
   i < j < size l -> nth a (swap i j l) k = 
    (if k == i then min (nth a l i) (nth a l j)
     else if k == j then max (nth a l i) (nth a l j)
     else nth a l k).
Proof.
case: l => [/andP[]|/= b l /andP[iLj jLs]]; first by case: j.
rewrite nth_cat size_take /= (ltn_trans iLj jLs).
case: (ltngtP k i) => [kLi|iLk|->]; first 2 last.
- rewrite subnn /=; congr min.
    rewrite -nth0 nth_drop addn0.
    by apply: set_nth_default; rewrite /= (ltn_trans iLj).
  rewrite -nth0 nth_drop addn0 nth_behead nth_drop prednK ?subn_gt0 //.
  by rewrite addnC subnK 1?ltnW //; apply: set_nth_default.
- by rewrite ?nth_take // ifN // neq_ltn (ltn_trans kLi).
rewrite -[k - i]prednK ?subn_gt0 //=.
rewrite nth_cat size_take size_behead size_drop /=.
rewrite !prednK ?subn_gt0 // subSn /=; last first.
  by rewrite -ltnS (leq_trans iLj (ltnW _)).
rewrite leq_sub2r // -ltnS prednK ?subn_gt0 //.
rewrite -(ltn_add2r i) !subnK //; try by rewrite ltnW.
case: (ltngtP k j) => [kLj|jLk|->]; first 2 last.
- rewrite subnn /= -!nth0 !(nth_drop, nth_behead) !addn0.
  rewrite prednK ?subn_gt0 // addnC subnK; last by rewrite ltnW.
  congr max; apply: set_nth_default => //.
  by rewrite (leq_trans iLj (ltnW _)).
- rewrite nth_take; last first.
    rewrite -ltnS !prednK ?subn_gt0 //.
    by rewrite -(ltn_add2r i) !subnK // ltnW.
- by rewrite nth_behead nth_drop prednK ?subn_gt0 // addnC subnK // ltnW.
rewrite -[_.-1 - _.-1]subSS !prednK ?subn_gt0 //.
rewrite subnBA 1?ltnW // subnK 1?ltnW // -[k - j]prednK ?subn_gt0 //=.
rewrite !(nth_behead, nth_drop) prednK ?subn_gt0 // -addSn prednK ?subn_gt0 //.
by rewrite addnCA addnA subnK 1?ltnW // addnC subnK 1?ltnW.
Qed.

(******************************************************************************)
(* Proof for iter1                                                             *)
(******************************************************************************)

Lemma nth_iter1_aux k n p i l l1 (a : A) :
  0 < p -> n = size l -> n = size l1 -> n <= k + i ->  
  (forall j,
  nth a l1 j = 
    if odd (j %/ p) then 
      if (j < i + p) then max (nth a l (j - p)) (nth a l j)
      else nth a l j
    else 
      if (j + p < n) && (j < i) then min (nth a l j) (nth a l (j + p))
      else nth a l j) -> 
  (forall j, j < n ->
  nth a (iter1_aux k n p i l1) j = 
    if odd (j %/ p) then max (nth a l (j - p)) (nth a l j)
    else 
      if j + p < n then min (nth a l j) (nth a l (j + p))
      else nth a l j).
Proof.
move=> p_gt0 nEl nEl1.
elim: k i l1 nEl1 => [i l1 nEl1 nLi /= Hc j jLn|
                      /= k IH i l1 nEl1 nLi Hc j jLn /=].
  have := Hc j.
  rewrite (leq_trans jLn nLi) andbT.
  suff -> : j < i + p by [].
  by rewrite (leq_trans (leq_trans jLn nLi) (leq_addr _ _)).
case: (ltnP (i + p)) => [ipLn|nLip]; last first.
  have := Hc j.
  have [jpO|jpE] := boolP (odd _).
    by rewrite ifT // (leq_trans jLn).
  case: (ltnP (j + p)) => [jpLn|nLjp]//=.
  by rewrite -(ltn_add2r p) (leq_trans jpLn).
have ipB : i < i + p < n.
  by rewrite -ltn_subLR // subnn p_gt0.
rewrite IH //.
- by case: odd; rewrite // size_swap // -nEl1.
- by rewrite -addSnnS.
move=> j1.
case: (boolP (odd _)) => [ipO|ipE].
  case: (boolP (odd _)) => [jpO|jpE].
    have j1Dip : j1 != i + p.
      rewrite -[odd _]negbK in jpO.
      apply: contra jpO => /eqP->.
      by rewrite -[X in _ + X]mul1n divnDMl // addn1 /= negbK.
    by rewrite Hc jpO addSn ltnS [j1 <= _]leq_eqVlt (negPf j1Dip).
  rewrite Hc (negPf jpE) /=.
  rewrite ltnS [j1 <= _]leq_eqVlt; case: eqP =>> //= j1Ei.
  by case/negP: jpE; rewrite j1Ei.
rewrite nth_swap -?nEl1 //.
case: eqP => [->|/eqP j1Di].
  rewrite (negPf ipE) ltnS ipLn leqnn //=.
  rewrite !Hc (negPf ipE) ipLn !ltnn /=.
  by rewrite -[X in _ + X]mul1n divnDMl // addn1 /= ipE mul1n.
case: eqP => [->|/eqP j1Dip].
  rewrite leqnn.
  rewrite -[X in _ + X]mul1n divnDMl // addn1 /= ipE mul1n addnK.
  rewrite !Hc (negPf ipE) ipLn !ltnn /=.
  by rewrite -[X in _ + X]mul1n divnDMl // addn1 /= ipE mul1n.
case: (boolP (odd _)) => [j1pO|j1pE].
  by rewrite Hc j1pO addSn ltnS [j1 <= _]leq_eqVlt (negPf j1Dip).
by rewrite Hc (negPf j1pE) ltnS [j1 <= _]leq_eqVlt (negPf j1Di).
Qed.

Lemma perm_iter1_aux k n p i (l : seq A) :
  0 < p -> n = size l -> perm_eq (iter1_aux k n p i l) l.
Proof.
move=> p_gt0.
elim: k i l => //= k1 IH i l nE.
case: ltnP => // ipLn.
have ipB : i < i + p < n by rewrite -ltn_subLR // subnn p_gt0.
apply: perm_trans (IH _ _ _) _.
  by case: odd => //=; rewrite size_swap // -nE.
by case: odd => //; apply: perm_swap; rewrite -nE.
Qed.

Lemma size_iter1_aux k n p i (l : seq A) :
  0 < p -> n = size l -> size (iter1_aux k n p i l) = size l.
Proof. by move=> p_gt0 nE; apply/perm_size/perm_iter1_aux. Qed.

Lemma iter1_auxS k n p i (l : seq A) :
  iter1_aux k.+1 n p i l =
  if i + p < n then
     iter1_aux k n p i.+1 
       (if odd (i %/ p) then l else swap i (i + p) l )
  else l.
Proof. by []. Qed.

Lemma perm_iter1 p (l : seq A) : 0 < p -> perm_eq (iter1 p l) l.
Proof. by move=> p_gt0; apply: perm_iter1_aux. Qed.

Lemma size_iter1 p (l : seq A) : 0 < p -> size (iter1 p l) = size l.
Proof. by move=> p_gt0; apply/perm_size/perm_iter1. Qed.

Lemma nth_iter1 p l (a : A) j :
  0 < p -> 
  nth a (iter1 p l) j = 
    if odd (j %/ p) then 
      if j < size l then max (nth a l (j - p)) (nth a l j)
      else nth a l j
    else 
      if j + p < size l then min (nth a l j) (nth a l (j + p))
      else nth a l j.
Proof.
move=> p_gt0.
case: (ltnP j (size l)) => jLs; last first.
  rewrite !nth_default ?minxx ?if_same ?size_iter1 //.
  by rewrite (leq_trans _ (leq_addr _ _)).
apply: nth_iter1_aux; rewrite ?(addn0, add0n) // => j1.
rewrite ltn0 andbF.
case: (boolP (odd _)) => [j1pO|]//.
rewrite ifN // -leqNgt.
by rewrite -divn_gt0; case: (_ %/ _) j1pO.
Qed.
  
(******************************************************************************)
(* Proof for iter2                                                            *)
(******************************************************************************)

Lemma iter2_auxS k n p q i (l : seq A) :
iter2_aux k.+1 n p q i (l : seq A) =
  if i + q < n then
     iter2_aux k n p q i.+1 
       (if odd (i %/ p) then l else swap (i + p) (i + q) l )
  else l.
Proof. by []. Qed.

Lemma iter2_aux_nth k n p q i l l1 (a : A) :
  0 < p -> 0 < q -> p %| q -> ~~ odd (q %/ p) ->
  n = size l -> n = size l1 -> n <= k + i ->  
  (forall j,
  nth a l1 j = 
    if odd (j %/ p) then 
      if (j < i + p) && (j + q < n + p) 
      then min (nth a l j) (nth a l (j + q - p))
      else nth a l j
    else 
      if (q <= j < i + q) then max (nth a l (j - q + p)) (nth a l j)
      else nth a l j) -> 
  (forall j, j < n ->
  nth a (iter2_aux k n p q i l1) j = 
    if odd (j %/ p) then 
      if (j + q < n + p) then 
        min (nth a l j) (nth a l (j + q - p))
      else nth a l j
    else 
      if (q <= j) then max (nth a l (j - q + p)) (nth a l j)
      else nth a l j).
Proof.
move=> p_gt0 q_gt0 pDq pDqE nEl nEl1.
have pLq : p < q.
  have : p <= q by rewrite dvdn_leq.
  by case: ltngtP => // pE; case/negP: pDqE; rewrite pE divnn q_gt0.
elim: k i l1 nEl1 => [i l1 nEl1 nLi /= Hc j jLn|
                      /= k IH i l1 nEl1 nLi Hc j jLn /=].
  have := Hc j.
  rewrite (leq_trans (leq_trans jLn _) (leq_addr q i)) // andbT.
  by rewrite (leq_trans (leq_trans jLn _) (leq_addr p i)) // andbT.
case: (ltnP (i + q)) => [iqLn|nLiq]; last first.
  have := Hc j.
  have [jpO|jpE]/= := boolP (odd _).
    case: (ltnP (j + q)); rewrite !(andbT, andbF) // => jqLnp.
      case: (ltnP j); rewrite // leqNgt.
    by rewrite -(ltn_add2r q) (leq_trans jqLnp) // addnAC leq_add2r.
  by rewrite (leq_trans jLn _) // andbT.
have iqB : i + p < i + q < n by rewrite ltn_add2l pLq iqLn.
rewrite IH //.
- by case: odd; rewrite // size_swap // -nEl1.
- by rewrite -addSnnS.
move=> j1.
case: (boolP (odd _)) => [ipO|ipE]/=.
  have iqO : odd ((i + q) %/ p).
    case/dvdnP: pDq pDqE => r ->.
    by rewrite mulnK // divnDMl // oddD => /negPf->; rewrite addbF.
  case: (boolP (odd _)) => [j1pO|j1pE]/=.
    have j1Dip : j1 != i + p.
      rewrite -[odd _]negbK in j1pO.
      apply: contra j1pO => /eqP->.
      by rewrite -[X in _ + X]mul1n divnDMl // addn1 /= negbK.
    by rewrite Hc j1pO addSn /= ltnS [j1 <= _]leq_eqVlt (negPf j1Dip).
  rewrite Hc (negPf j1pE) /=.
  rewrite ltnS [j1 <= _]leq_eqVlt; case: eqP =>> //= j1Ei.
  by case/negP: j1pE; rewrite j1Ei.
rewrite nth_swap -?nEl1 //.
have ipO : odd ((i + p) %/ p).
  by rewrite -[X in _ + X]mul1n divnDMl // addn1 /=.
have iqE : ~~ odd ((i + q) %/ p).
  case/dvdnP: pDq pDqE => r ->.
  by rewrite mulnK // divnDMl // oddD => /negPf->; rewrite addbF.
case: eqP => [->|/eqP j1Di].
  rewrite -[X in _ + X]mul1n divnDMl // addn1 /= ipE mul1n.
  rewrite leqnn.
  rewrite addnAC ltn_add2r iqLn /=.
  by rewrite !Hc (negPf iqE) ipO !ltnn !andbF /= addnK.
case: eqP => [->|/eqP j1Dip].
  rewrite (negPf iqE) leq_addl leqnn /= addnK.
  by rewrite !Hc (negPf iqE) ipO !ltnn !leq_addl.
case: (boolP (odd _)) => [j1pO|j1pE].
  by rewrite Hc j1pO addSn ltnS [j1 <= _]leq_eqVlt (negPf j1Di).
by rewrite Hc (negPf j1pE) ltnS [j1 <= _]leq_eqVlt (negPf j1Dip).
Qed.

Lemma perm_iter2_aux k n p q i (l : seq A) :
  0 < p -> p < q -> n = size l -> perm_eq (iter2_aux k n p q i l) l.
Proof.
move=> p_gt0 pLq.
elim: k i l => //= k1 IH i l nE.
case: ltnP => // ipLn.
have ipB : i + p < i + q < n by rewrite ltn_add2l pLq.
apply: perm_trans (IH _ _ _) _.
  by case: odd => //=; rewrite size_swap // -nE.
by case: odd => //; apply: perm_swap; rewrite -nE.
Qed.

Lemma size_iter2_aux k n p q i (l : seq A) :
  0 < p -> p < q -> n = size l -> size (iter2_aux k n p q i l) = size l.
Proof. by move=> p_gt0 qLp nE; apply/perm_size/perm_iter2_aux. Qed.

Lemma perm_iter2 p q (l : seq A) : 0 < p -> p < q -> perm_eq (iter2 p q l) l.
Proof. by move=> p_gt0 pLq; apply: perm_iter2_aux. Qed.

Lemma size_iter2 p q (l : seq A) :
  0 < p -> p < q -> size (iter2 p q l) = size l.
Proof. by move=> p_gt0 pLq; apply/perm_size/perm_iter2. Qed.

Lemma nth_iter2 p q l (a : A) j :
  0 < p -> 0 < q -> p %| q -> ~~ odd (q %/ p) -> 
  nth a (iter2 p q l) j = 
    if odd (j %/ p) then 
      if (j + q < size l + p) then 
        min (nth a l j) (nth a l (j + q - p))
      else nth a l j
    else 
      if (q <= j < size l) then max (nth a l (j - q + p)) (nth a l j)
      else nth a l j.
Proof.
move=> p_gt0 q_gt0 pDq qpE.
have pLq : p < q.
  have : p <= q by rewrite dvdn_leq.
  by case: ltngtP => // pE; case/negP: qpE; rewrite pE divnn q_gt0.
case: (ltnP j (size l)) => jLs; last first.
  rewrite andbF !nth_default ?(maxxx, minxx) ?if_same ?size_iter2 //.
  by rewrite -addnBA ?(leq_trans jLs (leq_addr _ _)) // ltnW.
rewrite andbT.
apply: iter2_aux_nth; rewrite ?(addn0, add0n) // => j1.
case: (boolP (odd _)) => [j1pO|j1pE]//.
  have pLj1 : p <= j1 by rewrite -divn_gt0 //; case: (_ %/ _) j1pO. 
  by rewrite ifN // negb_and; case: leqP pLj1.
by rewrite ifN // negb_and; case: leqP.
Qed.

(******************************************************************************)
(* Proof for iter3                                                            *)
(******************************************************************************)

Lemma iter3_auxS k p q (l : seq A) :
  iter3_aux k.+1 p q (l : seq A) =
  if q > p then
     iter3_aux k p q./2 (iter2 p q l)
  else l.
Proof. by []. Qed.

Lemma perm_iter3_aux k p q (l : seq A) :
  0 < p -> perm_eq (iter3_aux k p q l) l.
Proof.
move=> p_gt0.
elim: k q l => //= k IH q l.
case: leqP => // H.
apply: perm_trans.
apply: IH.
by apply: perm_iter2.
Qed.

Lemma size_iter3_aux k p q (l : seq A) :
  0 < p -> size (iter3_aux k p q l) = size l.
Proof. by move=> p_gt; apply/perm_size/perm_iter3_aux. Qed.

Lemma perm_iter3 p q (l : seq A) : 0 < q -> perm_eq (iter3 p q l) l.
Proof. by apply: perm_iter3_aux. Qed.

Lemma size_iter3  p q (l : seq A) :
  0 < q -> size (iter3 p q l) = size l.
Proof. by move=> q_gt; apply/perm_size/perm_iter3. Qed.

(******************************************************************************)
(* Proof for iknuth_exchance                                                             *)
(******************************************************************************)

Lemma perm_iknuth_exchance_aux k p q (l : seq A) :
  perm_eq (iknuth_exchance_aux k p q l) l.
Proof.
elim: k p q l => //= k IH p q l.
case: leqP => // q_gt0.
apply: perm_trans; first by apply: IH.
apply: perm_trans; first by apply: perm_iter3.
by apply: perm_iter1.
Qed.  

Lemma size_iknuth_exchance_aux k p q (l : seq A) :
  size (iknuth_exchance_aux k p q l) = size l.
Proof. by apply/perm_size/perm_iknuth_exchance_aux. Qed.

Lemma perm_iknuth_exchance (l : seq A) : perm_eq (iknuth_exchance l) l.
Proof. by apply: perm_iknuth_exchance_aux. Qed.

Lemma size_iknuth_exchance (l : seq A) : size (iknuth_exchance l) = size l.
Proof. by apply/perm_size/perm_iknuth_exchance_aux. Qed.

End IKnuthExchangeProof.

(* We develop a true variant of eocat, so that teocatK holds *)
Fixpoint teocat (A : Type) (l1 l2 : seq A) := 
  if l1 is a :: l3 then
  if l2 is b :: l4 then a :: b :: teocat l3 l4 
  else [:: a] else [::].

Lemma teocat_cons (A : Type) a b (l1 l2 : seq A) : 
  teocat (a :: l1) (b :: l2) = a :: b :: teocat l1 l2.
Proof. by []. Qed.

Lemma teocatK (A : Type) (l : seq A) : teocat (etake l) (otake l) = l.
Proof.
have [n leMl] := ubnP (size l).
elim: n l leMl => //= n IH [|a[|b l]] //= slL.
by rewrite IH // -ltnS ltnW.
Qed.
 
Lemma eotakeS (A : Type) (d n : nat) (l : seq A) :
  eotake d.+1 n l =
    if odd n
      then eotake d n./2 (otake l)
      else eotake d n./2 (etake l).
Proof. by []. Qed.

Lemma teocat_take (A : Type) d n (l : seq A) : n < `2^ d -> 
  teocat (eotake d.+1 n l) (eotake d.+1 (`2^ d + n) l) = 
  eotake d n l.
Proof.
move=> nL2d.
have IH0 d1 l1 : teocat (eotake d1.+1 0 l1) (eotake d1.+1 (`2^ d1) l1) = 
                 eotake d1 0 l1.
  elim: d1 l1 => [/= l1|d1 IH l1]; first by rewrite teocatK.
  rewrite !(eotakeS d1.+1).
  by rewrite [RHS]/= -[RHS]IH /= addnn odd_double doubleK.
have [m leMn] := ubnP n.
elim: m n d l leMn nL2d => [[]//|m IH n [|d] l nLm nLd].
  by case: (n) nLd => //= _; apply: teocatK.
rewrite !(eotakeS d.+1) [X in odd(X + _)]addnn oddD odd_double addFb [RHS]/=.
have -> : (`2^ d.+1 + n)./2  = `2^d + n./2.
  by rewrite /= addnn halfD doubleK odd_double.
rewrite -(odd_double_half n) in nLm nLd.
case: (boolP (odd n)) nLm nLd; rewrite ?(addSn, add0n, ltnS) => nO nLm nLd.
  apply: IH => //.
    by rewrite (leq_ltn_trans _ nLm) // -addnn leq_addr.
  by rewrite -ltn_double -[X in _ < X]addnn (leq_ltn_trans _ nLd).
case: (ltngtP 0 n) => // [n_gt0|<-]; last by rewrite addn0 IH0.
apply: IH => //.
  case: (n) nO n_gt0 nLm => // [] [|n1] //= _ _ n1Lm.
  by rewrite (leq_trans _ n1Lm) // -addnn addnS addSn !ltnS leq_addr.
by rewrite -ltn_double -[X in _ < X]addnn (leq_ltn_trans _ nLd).
Qed.

Lemma etake_eotake (A : Type) d n (l : seq A) : n < `2^ d -> 
  etake (eotake d n l) =  eotake d.+1 n l.
Proof.
have IH0 d1 l1 : etake (eotake d1 0 l1) = eotake d1.+1 0 l1.
  elim: d1 l1 => [//|d1 IH l1].
  by rewrite !(eotakeS d1.+1) -[RHS]IH.
move=> nL2d.
have [m leMn] := ubnP n.
elim: m n d l leMn nL2d => [[]//|m IH n [|d] l nLm nLd].
  by case: (n) nLd => //= _; apply: teocatK.
case: (ltngtP 0 n) => // [n_gt0|<-]; last by rewrite IH0.
have n2Ld : n./2 < `2^ d.
  rewrite -ltn_double -[X in _ < X]addnn (leq_ltn_trans _ nLd) //.
  by rewrite -[X in _ <= X](odd_double_half n) leq_addl.
have n2Lm : n./2 < m.
  case: (n) n_gt0 nLm => // [] [|m1] //= _.
  rewrite -(odd_double_half m1.+2) /= doubleS  addnS ltnS.
  move => /(leq_ltn_trans _)->//.
  by rewrite addnS ltnS -addnn addnA leq_addl.
by rewrite !(eotakeS d.+1) [LHS]/=; case: odd; apply: IH.
Qed.

Lemma otake_eotake (A : Type) d n (l : seq A) : n < `2^ d -> 
  otake (eotake d n l) =  eotake d.+1 (`2^ d + n) l.
Proof.
have IH0 d1 l1 : otake (eotake d1 0 l1) = eotake d1.+1 (`2^ d1) l1.
  elim: d1 l1 => [//=|d1 IH l1].
  rewrite !(eotakeS d1.+1) [X in odd X]/= addnn odd_double.
  by rewrite [X in X./2]addnn doubleK -[RHS]IH.
move=> nL2d.
have [m leMn] := ubnP n.
elim: m n d l leMn nL2d => [[]//|m IH n [|d] l nLm nLd].
  by case: (n) nLd => //= _; apply: teocatK.
case: (ltngtP 0 n) => // [n_gt0|<-]; last by rewrite addn0 IH0.
have n2Ld : n./2 < `2^ d.
  rewrite -ltn_double -[X in _ < X]addnn (leq_ltn_trans _ nLd) //.
  by rewrite -[X in _ <= X](odd_double_half n) leq_addl.
have n2Lm : n./2 < m.
  case: (n) n_gt0 nLm => // [] [|m1] //= _.
  rewrite -(odd_double_half m1.+2) /= doubleS  addnS ltnS.
  move => /(leq_ltn_trans _)->//.
  by rewrite addnS ltnS -addnn addnA leq_addl.
have HE : (`2^ d.+1 + n)./2 = `2^ d + n./2.
  by rewrite halfD odd_e2 /= addnn doubleK. 
rewrite !(eotakeS d.+1) oddD odd_e2 HE.
rewrite -IH // [LHS]/=.
by case: odd => //=; rewrite IH.
Qed.

Lemma leq_size_eotake_e2n (A : Type) i p q (l : seq A) :
  i <= q -> size l <= `2^ q -> size (eotake i p l) <= `2^ (q - i).
Proof.
elim: i p q l => [|i IH] p q l iLq Hs /=; first by rewrite subn0.
have q_gt0 : 0 < q by apply: leq_ltn_trans iLq.
case: odd.
  apply: leq_trans (IH _ q.-1 _ _ _) _.
  - by rewrite -ltnS prednK // (leq_ltn_trans _ iLq).
  - rewrite size_otake -leq_double -!addnn -e2Sn addnn.
    rewrite prednK // (leq_trans _ Hs) //.
    by rewrite -[X in _ <= X]odd_double_half; case: odd.
  by case: (q) q_gt0.
apply: leq_trans (IH _ q.-1 _ _ _) _.
- by rewrite -ltnS prednK // (leq_ltn_trans _ iLq).
- by rewrite size_etake leq_uphalf_e2n // prednK.
by case: (q) q_gt0.
Qed.


Lemma teocat_nseq (A : Type) (a : A) n m : 
  m <= n <= m.+1 -> teocat (nseq n a) (nseq m a) = nseq (n + m) a.
Proof.
elim: n m => [[]//|n IH [|m]]; first by case: (n).
rewrite addnS /= !ltnS => H.
by rewrite IH.
Qed.

Definition weight (l : seq bool) := count (fun x => false == x) l.

Lemma weight_size (l : seq bool) : weight l <= size l.
Proof. exact: count_size. Qed.

Lemma weight_cat l1 l2 : weight (l1 ++ l2) = weight l1 + weight l2.
Proof. by exact: count_cat. Qed.

Lemma weight_nseqF a : weight (nseq a false) = a.
Proof. by rewrite [LHS]count_nseq mul1n. Qed.

Lemma weight_nseqT a : weight (nseq a true) = 0.
Proof. by rewrite [LHS]count_nseq mul0n. Qed.

Lemma eotake_sorted (p : nat) (l : seq bool) i :
  i < `2^ p -> 
  [/\ sorted <=%O (eotake p.+1 i l),
      sorted <=%O (eotake p.+1 (`2^ p + i) l) & 
  weight (eotake p.+1 (`2^p + i) l) <= weight (eotake p.+1 i l) <=
  weight (eotake p.+1 (`2^p + i) l) + 1] ->
  sorted <=%O (eotake p i l).
Proof.
move=> iL2p [/isorted_boolP[[a1 b1] E1 /isorted_boolP[[a2 b2] E2]]].
rewrite E1 E2 !weight_cat !weight_nseqT !weight_nseqF !addn0 addn1 => a2La1.
rewrite -teocat_take // E1 E2.
have := size_etake (eotake p i l).
have := size_otake (eotake p i l).
rewrite etake_eotake // otake_eotake // E1 E2 uphalf_half => <-.
rewrite !size_cat !size_nseq.
elim: a1 {E1 E2}a2 a2La1 => [[|a2]//= _ Hs|a1 IH [|a2]].
- rewrite teocat_nseq //.
    by apply/isorted_boolP; exists (0, b1 + b2).
  rewrite add0n in Hs.
  by rewrite Hs; case: odd; rewrite ?add1n !leqnn ?andbT //=.
- case: (a1) => // _; case: (b1); case: (b2) => // b3 b4 Hs.
  rewrite /= in Hs.
  rewrite ![_ ++ _]/= teocat_cons (@teocat_nseq _ true b4.+1).
    rewrite isorted_consF.
    by apply/isorted_boolP; exists (0, (b4.+1 + b3).+1).
  rewrite add1n add0n addnS in Hs.
  by case: Hs=> ->; case: odd; rewrite ?add1n !leqnn ?andbT /=.
rewrite ![_ ++ _]/= !ltnS => HS1 HS2.
rewrite !addSn addnS in HS2.
rewrite [_ ++ nseq b2 _]/= teocat_cons !isorted_consF.
apply: IH => //.
by case: HS2.
Qed.

Lemma iter1_sorted (p : nat) (l : seq bool) i :
  i < `2^ p -> 
  let l1 := iter1 (`2^ p) l in 
  sorted <=%O (eotake p.+1 i l) ->
  sorted <=%O (eotake p.+1 (`2^ p + i) l) 
  -> 
  [/\ 
  sorted <=%O (eotake p.+1 i l1),
  sorted <=%O (eotake p.+1 (`2^p + i) l1) &
  weight (eotake p.+1 (`2^p + i) l1) <= weight (eotake p.+1 i l1)].
Proof.
move=> iL2p l1.
set l2 := eotake _ _ _; set l3 := eotake _ _ _.
pose d : nat := (size l2 != size l3).
move=> /isorted_boolP[[a1 b1] l2E] /isorted_boolP[[a2 b2] l3E].
pose ll := eotake p i l.
have sl2E : size l2 = uphalf (size ll) by rewrite -size_etake etake_eotake.
have sl3E : size l3 = (size ll)./2 by rewrite -size_otake otake_eotake.
have dE : d = odd (size ll).
  rewrite /d sl2E sl3E uphalf_half; case odd; rewrite /= ?eqxx ?add1n //.
  by case: ltngtP (leqnn (size ll)./2.+1).
rewrite uphalf_half -dE l2E size_cat !size_nseq in sl2E.
rewrite l3E size_cat !size_nseq in sl3E.
have a1b1E : a1 + b1 = a2 + b2 + d by rewrite sl2E addnC sl3E.
pose l4 := nseq (maxn a1 a2) false ++ nseq (minn b1 (d + b2)) true. 
have l4S : size l4 = size (eotake p.+1 i l1).
  rewrite size_cat !size_nseq.
  rewrite (eq_size_eotake _ _ (size_iter1 l (e2n_gt0 _))).
  rewrite -/l2 l2E size_cat !size_nseq.
  lia.
pose l5 := nseq (minn a1 a2) false ++ nseq (maxn b1 (d + b2) - d) true.
have l5S : size l5 = size (eotake p.+1 (`2^ p + i) l1).
  rewrite size_cat !size_nseq.
  rewrite (eq_size_eotake _ _ (size_iter1 l (e2n_gt0 _))).
  rewrite -/l3 l3E size_cat !size_nseq.
  lia.
have <- : l4 = eotake p.+1 i l1.
  apply: (@eq_from_nth _ true) => // k kLs.
  rewrite !nth_cat !nth_nseq if_same.
  rewrite nth_eotake nth_iter1 ?e2n_gt0 //.
  rewrite -nth_eotake -/l2 !modn_small; last first.
    by rewrite (leq_trans iL2p) // leq_addr.
  rewrite [_ + `2^ _]addnC addnA.
  rewrite -[_ + i](modn_small (_ : _ < `2^ p.+1)); last first.
    by rewrite e2Sn ltn_add2l.
  rewrite -nth_eotake -/l3.
  rewrite [X in (i + X * _) %/ _]e2Sn addnn -muln2 -mulnA mulnC.
  rewrite divnDMl ?e2n_gt0 // oddD mul2n odd_double addbF.
  rewrite divn_small //= modn_small ?ltn_add2l //.
  rewrite l2E l3E !nth_cat !nth_nseq !size_nseq !if_same.
  case: (ltnP a1 a2) => [a1La2|a2La1].
    case: (ltnP k a1) => [a1Lk|kLa1].
      rewrite !(leq_trans a1Lk (ltnW _)) //=; last first.
      by rewrite minxx if_same.
    case: (ltnP k a2) => [a2Lk|kLa2].
      suff /gtn_size_eotake-> : k < size (eotake p.+1 (`2^ p + i) l).
      - by rewrite minbF.
      - by rewrite ltn_add2l.
      have : k < size l5.
        rewrite size_cat !size_nseq.
        have -> : minn a1 a2 = a1 by lia.
        have -> : maxn b1 (d + b2) = b1 by lia.
        have -> : a1 + (b1 - d) = a2 + b2 by lia.
        by apply: leq_trans (leq_addr _ _).
      rewrite l5S.
      by rewrite (eq_size_eotake _ _ (size_iter1 _ _)) // e2n_gt0.
    by rewrite !if_same.
  case: (ltnP k a2) => [a2Lk|kLa2].
    by rewrite !(leq_trans a2Lk _) // minxx if_same.
  by case: (ltnP k a1) => [a1Lk|kLa1]; rewrite if_same.
have <- : nseq (minn a1 a2) false ++ nseq (maxn b1 (d + b2) - d) true =
          eotake p.+1 (`2^ p + i) l1.
  apply: (@eq_from_nth _ true) => [|k].
    rewrite size_cat !size_nseq.
    rewrite (eq_size_eotake _ _ (size_iter1 l (e2n_gt0 _))).
    rewrite -/l3 l3E size_cat !size_nseq.
    lia.
  rewrite nth_cat !nth_nseq !size_cat !size_nseq if_same.
  rewrite nth_eotake nth_iter1 ?e2n_gt0 //.
  rewrite -nth_eotake -/l2 !modn_small; last first.
    by rewrite e2Sn ltn_add2l.
  rewrite [_ + `2^ _]addnC addnA.
  rewrite -[X in X - `2^ _]addnA [X in X - `2^ _]addnC addnK.
  rewrite -[in i + _ * k](modn_small (_ : i < `2^ p.+1)); last first.
    by rewrite (leq_trans iL2p (leq_addr _ _)).
  rewrite -nth_eotake -/l2 -/l3.
  rewrite [X in (_ + X * _) %/ _]e2Sn addnn -muln2 -mulnA mulnC.
  rewrite divnDMl ?e2n_gt0 // oddD mul2n odd_double addbF.
  rewrite -[X in X + i]mul1n [1 * _ + _]addnC divnDMl ?e2n_gt0 //.
  rewrite divn_small //= mul1n.
  rewrite l2E l3E !nth_cat !nth_nseq !size_nseq !if_same.
  case: (ltnP a1 a2) => [a1La2|a2La1].
    have -> : maxn b1 (d + b2) = b1 by lia.
    case: (ltnP k a1) => [a1Lk|kLa1].
      rewrite !(leq_trans a1Lk _) //=; last first.
      - by apply: (leq_addr _ _).
      - by apply: ltnW.
      by rewrite maxxx if_same.
    case: (ltnP k a2) => [a2Lk|kLa2].
      rewrite ifT // -e2Sn [i + _]addnC.
      suff /gtn_size_eotake-> : k < size (eotake p.+1 (`2^ p + i) l) => //.
        by rewrite ltn_add2l.
      have : k < size l5.
        rewrite size_cat !size_nseq.
        have -> : minn a1 a2 = a1 by lia.
        have -> : maxn b1 (d + b2) = b1 by lia.
        have -> : a1 + (b1 - d) = a2 + b2 by lia.
        by apply: leq_trans (leq_addr _ _).
      rewrite l5S.
      by rewrite (eq_size_eotake _ _ (size_iter1 _ _)) // e2n_gt0.
    by rewrite !if_same.
  have -> : maxn b1 (d + b2) = d + b2 by lia.
  case: (ltnP k a2) => [a2Lk|kLa2] _.
    by rewrite !(leq_trans a2Lk _) // maxxx if_same.
  by case: (ltnP k a1) => [a1Lk|kLa1]; rewrite if_same.
split.
- by apply/isorted_boolP; exists (maxn a1 a2, minn b1 (d + b2)).
- by apply/isorted_boolP; exists (minn a1 a2, maxn b1 (d + b2) - d).
rewrite !weight_cat !weight_nseqF !weight_nseqT !addn0.
by case: (ltnP a1 a2) => // ?; rewrite ltnW.
Qed.

Lemma iter2_sorted (p : nat) q (l : seq bool) i :
  i < `2^ p -> p < q ->
  let l1 := iter2 (`2^ p) (`2^ q) l in 
  [/\ 
  sorted <=%O (eotake p.+1 i l),
  sorted <=%O (eotake p.+1 (`2^ p + i) l) & 
  weight (eotake p.+1 (`2^p + i) l) <= weight (eotake p.+1 i l) <=
  weight (eotake p.+1 (`2^p + i) l) + `2^ (q - p)]
  -> 
  [/\ 
  sorted <=%O (eotake p.+1 i l1),
  sorted <=%O (eotake p.+1 (`2^p + i) l1) &
  weight (eotake p.+1 (`2^p + i) l1) <= weight (eotake p.+1 i l1) <=
  weight (eotake p.+1 (`2^p + i) l1) + `2^ (q.-1 - p)].
Proof.
move=> iL2p pLq l1.
have q_gt0 : 0 < q by apply: leq_ltn_trans pLq.
have p2Lq2 : `2^ p < `2^ q by rewrite ltn_e2n.
have p2Dq2 : `2^ p %| `2^ q by  rewrite dvdn_e2n ltnW.
set l2 := eotake _ _ _; set l3 := eotake _ _ _.
pose d : nat := (size l2 != size l3).
move=> [] /isorted_boolP[[a1 b1] l2E] /isorted_boolP[[a2 b2] l3E].
pose ll := eotake p i l.
pose xi := a1 - a2.
pose j := xi - `2^(q - p.+1).
have sl2E : size l2 = uphalf (size ll) by rewrite -size_etake etake_eotake.
have sl3E : size l3 = (size ll)./2 by rewrite -size_otake otake_eotake.
have dE : d = odd (size ll).
  rewrite /d sl2E sl3E uphalf_half; case odd; rewrite /= ?eqxx ?add1n //.
  by case: ltngtP (leqnn (size ll)./2.+1).
rewrite uphalf_half -dE l2E size_cat !size_nseq in sl2E.
rewrite l3E size_cat !size_nseq in sl3E.
have a1b1E : a1 + b1 = a2 + b2 + d by rewrite sl2E addnC sl3E.
rewrite l3E l2E !weight_cat !weight_nseqF !weight_nseqT !addn0=> a1B.
pose l4 := nseq (a1 - j) false ++ nseq (b1 + j) true.
have l4S : size l4 = size (eotake p.+1 i l1).
  rewrite size_cat !size_nseq.
  rewrite (eq_size_eotake _ _ (size_iter2 l (e2n_gt0 _) _)) //.
  rewrite -/l2 l2E size_cat !size_nseq.
  lia.
pose l5 := nseq (a2 + j) false ++ nseq (b2 - j) true.
have l5S : size l5 = size (eotake p.+1 (`2^ p + i) l1).
  rewrite size_cat !size_nseq.
  rewrite (eq_size_eotake _ _ (size_iter2 l (e2n_gt0 _) _)) //.
  rewrite -/l3 l3E size_cat !size_nseq.
  rewrite -subSS subSn // e2Sn in a1B.
  lia.
have xiLpq : xi <= `2^ (q - p) by lia.
have <- : l4 = eotake p.+1 i l1.
  apply: (@eq_from_nth _ true) => // k kLs.
  rewrite !nth_cat !nth_nseq size_nseq if_same.
  rewrite nth_eotake /l1 nth_iter2 ?e2n_gt0 //; last first.
    rewrite -[q]prednK // e2Sn addnn -muln2.
    rewrite -divn_mulAC ?muln2 ?odd_double // dvdn_e2n //.
    by rewrite -ltnS prednK.
  rewrite -nth_eotake -/l2 !modn_small; last first.
    by rewrite (leq_trans iL2p) // leq_addr.
  rewrite l2E !nth_cat !nth_nseq !size_nseq if_same.
  rewrite [X in (i + X * _) %/ _]e2Sn addnn -doubleMl doubleMr.
  rewrite [_ * _.*2]mulnC divnDMl ?e2n_gt0 // oddD odd_double.
  rewrite divn_small //=.
  have := kLs; rewrite l4S => /gtn_size_eotake.
  have ss : size l1 = size l.
    by apply: size_iter2 => //; apply: e2n_gt0.
  rewrite ss => ->; last first.
    by rewrite // ?(leq_trans _ (leq_addr _ _)) //.
  rewrite andbT.
  case: ltnP => [kLa1j|a1jLk].
    rewrite (leq_trans kLa1j (leq_subr _ _)).
    case: leqP => // q2Lipk.
    have qp2L1k : `2^ (q -p) <= 1 + k.*2.
      have : `2^ q <= `2^ p + (`2^ p + `2^ p) * k
        by apply: leq_trans q2Lipk _; rewrite leq_add2r ltnW.
      rewrite -[in X in X <= _](subnK (ltnW pLq)) e2nD.
      rewrite addnn -doubleMl doubleMr.
      rewrite -[X in _ <= X + _]mul1n  [`2^ p * _]mulnC -mulnDl leq_mul2r.
      by case: e2n (e2n_gt0 p).
    have qp2Lk : `2^ (q - p) <= k.*2.
      have := half_leq qp2L1k.
      rewrite e2n_div2 ?subn_gt0 // halfD /= odd_double /= -leq_double.
      by rewrite -addnn -e2Sn doubleK prednK // subn_gt0.
    rewrite -addnBA; last first.
      rewrite -e2Sn -(subnK pLq) e2nD mulnC leq_mul2l.
      case: e2n (e2n_gt0 p.+1) => //= _ _.
      by rewrite subnS -e2n_div2 ?subn_gt0 // leq_halfl.
    rewrite [i + _ + _]addnAC [i + `2^ _]addnC.
    rewrite -e2Sn -(subnK pLq) [_ - _ + _]addnC e2nD -mulnBr.
    rewrite -[_ + i](modn_small (_ : _ < `2^ p.+1)); last by rewrite ltn_add2l.
    rewrite -nth_eotake -/l3 l3E nth_cat !nth_nseq /= size_nseq.
    case: leqP => //.
    have : (`2^ (q -p.+1)).*2 = `2^ (q -p).
      by rewrite -addnn -e2Sn -subSn.
    lia.
  case: (leqP (`2^ q)) => [q2Lipk|ipkLq2].
    have qp2L1k : `2^ (q -p) <= 1 + k.*2.
      have : `2^ q <= `2^ p + (`2^ p + `2^ p) * k
        by apply: leq_trans q2Lipk _; rewrite leq_add2r ltnW.
      rewrite -[in X in X <= _](subnK (ltnW pLq)) e2nD.
      rewrite addnn -doubleMl doubleMr.
      rewrite -[X in _ <= X + _]mul1n  [`2^ p * _]mulnC -mulnDl leq_mul2r.
      by case: e2n (e2n_gt0 p).
    have qp2Lk : `2^ (q - p) <= k.*2.
      have := half_leq qp2L1k.
      rewrite e2n_div2 ?subn_gt0 // halfD /= odd_double /= -leq_double.
      by rewrite -addnn -e2Sn doubleK prednK // subn_gt0.
    rewrite -addnBA; last first.
      rewrite -e2Sn -(subnK pLq) e2nD mulnC leq_mul2l.
      case: e2n (e2n_gt0 p.+1) => //= _ _.
      by rewrite -leq_double -addnn -e2Sn -subSn.
    rewrite [i + _ + _]addnAC [i + `2^ _]addnC.
    rewrite -e2Sn -(subnK pLq) [_ - _ + _]addnC e2nD -mulnBr.
    rewrite -[_ + i](modn_small (_ : _ < `2^ p.+1)); last by rewrite ltn_add2l.
    rewrite -nth_eotake -/l3 l3E nth_cat !nth_nseq /= size_nseq.
    case: leqP => // k2pqLa2; first by rewrite if_same maxTb.
    case: leqP => //.
    lia.
  case: leqP => //.
  have : (`2^ (q -p) * `2^ p) = `2^ q by rewrite -e2nD subnK // ltnW.
  have : (`2^ (q -p.+1)).*2 = `2^ (q -p) by rewrite -addnn -e2Sn -subSn.
  nia.
have <- : l5 = eotake p.+1 (`2^ p + i) l1.
  apply: (@eq_from_nth _ true) => // k kLs.
  rewrite !nth_cat !nth_nseq size_nseq if_same.
  rewrite nth_eotake /l1 nth_iter2 ?e2n_gt0 //; last first.
    rewrite -[q]prednK // e2Sn addnn -muln2.
    rewrite -divn_mulAC ?muln2 ?odd_double // dvdn_e2n //.
    by rewrite -ltnS prednK.
  rewrite -nth_eotake -/l2 !modn_small; last first.
    by rewrite ltn_add2l.
  rewrite -/l3.
  rewrite l3E !nth_cat !nth_nseq !size_nseq if_same.
  rewrite [X in (_ + i + X * _) %/ _]e2Sn addnn -doubleMl doubleMr.
  rewrite [_ * _.*2]mulnC divnDMl ?e2n_gt0 // oddD odd_double.
  rewrite -[X in (X + i) %/ _]mul1n [X in X %/ _]addnC divnDMl ?e2n_gt0 //.
  rewrite addn1 /= divn_small //=.
  rewrite -!addnA [`2^ p + (_ + _)]addnC !addnA addnK ltn_add2r.
  case: (ltnP k a2) => [kLa2|a2Lk].
    rewrite (leq_trans kLa2 (leq_addr _ _)).
    by rewrite minFb if_same.
  rewrite minTb.
  case: leqP => [a2jLk|kLa2j].
    case: leqP => // q2Lipk.
    rewrite -[i](modn_small (_ : _ < `2^ p.+1)); last first.
      by rewrite e2Sn; lia.
    rewrite -e2Sn -(subnK pLq) e2nD -addnA [_ * k]mulnC -mulnDl mulnC.
    rewrite -nth_eotake.
    rewrite -/l2 l2E nth_cat !nth_nseq /= size_nseq if_same.
    by case: leqP => //; lia.
  rewrite ifT; last first.
    have kqpLa1 : k + `2^ (q - p.+1) < a1 by lia.
    have iL2p1 : i < `2^ p.+1 by rewrite (leq_trans iL2p (leq_addr _ _)).
    have kqpLsl2 : k + `2^ (q - p.+1) < size l2.
      by rewrite l2E size_cat !size_nseq; lia.
    have := gtn_size_eotake iL2p1 kqpLsl2. 
    have : (`2^ (q -p.+1) * `2^ p.+1) = `2^ q by rewrite -e2nD subnK // ltnW.
    rewrite -e2Sn; nia.
  rewrite -[i](modn_small (_ : _ < `2^ p.+1)); last first.
    by rewrite e2Sn; lia.
  rewrite -e2Sn -(subnK pLq) e2nD -addnA [_ * k]mulnC -mulnDl mulnC.
  rewrite -nth_eotake.
  rewrite -/l2 l2E nth_cat !nth_nseq /= size_nseq if_same.
  by case: leqP => //; lia.
split.
- by apply/isorted_boolP; exists (a1 - j, b1 + j).
- by apply/isorted_boolP; exists (a2 + j, b2 - j).
rewrite !weight_cat !weight_nseqF !weight_nseqT !addn0.
have : (`2^ (q.-1 - p)).*2 = `2^ (q -p).
  by rewrite -addnn -e2Sn -subSn ?prednK; lia.
have : (`2^ (q - p.+1)).*2 = `2^ (q -p).
  rewrite -addnn -e2Sn -subSn ?subSS //.
lia.
Qed.

Lemma iter3_aux_sorted k (p : nat) q (l : seq bool) i :
  i < `2^ p -> q < k + p ->
  let l1 := iter3_aux k (`2^ p) (`2^ q) l in 
  [/\ 
  sorted <=%O (eotake p.+1 i l),
  sorted <=%O (eotake p.+1 (`2^ p + i) l) & 
  weight (eotake p.+1 (`2^p + i) l) <= weight (eotake p.+1 i l) <=
  weight (eotake p.+1 (`2^p + i) l) + `2^ (q - p)]
  -> 
  [/\ 
  sorted <=%O (eotake p.+1 i l1),
  sorted <=%O (eotake p.+1 (`2^p + i) l1) &
  weight (eotake p.+1 (`2^p + i) l1) <= weight (eotake p.+1 i l1) <=
  weight (eotake p.+1 (`2^p + i) l1) + 1].
Proof.
move=> iL2p.
elim: k q l => [q l | k IH q l qLp].
  rewrite [iter3_aux _ _ _ _]/= => qLp.
  by have -> : q - p = 0 by lia.
rewrite [iter3_aux _ _ _ _]/=.
case: leqP => [p2Lq2|q2Lp2].
  move=> l1; suff -> : q - p = 0 by [].
  by apply/eqP; rewrite subn_eq0 -leq_e2n.
have q_gt0 : 0 < q by rewrite (leq_ltn_trans (_ : 0 <= p)) -1?ltn_e2n.
rewrite e2n_div2 // => l1 Hs.
apply: IH; try lia.
apply: iter2_sorted => //.
by rewrite -ltn_e2n.
Qed.


Lemma iter3_sorted (p : nat) q (l : seq bool) i :
  i < `2^ p -> `2^ q < size l <= `2^ q.+1 -> p <= q ->
  let l1 := iter3 (`2^ q) (`2^ p) l in 
  [/\ 
  sorted <=%O (eotake p.+1 i l),
  sorted <=%O (eotake p.+1 (`2^ p + i) l) & 
  weight (eotake p.+1 (`2^p + i) l) <= weight (eotake p.+1 i l)]
  -> 
  sorted <=%O (eotake p i l1).
Proof.
move=> iLp /andP[qLsl slL2q] pLq l1 [Hl Hr Hw].
apply: eotake_sorted => //.
apply: iter3_aux_sorted => //.
  apply: leq_trans (leq_addr _ _).
  by rewrite ltnS (leq_trans (ltnW (ltn_ne2n _)) (ltnW qLsl)).
split => //.
apply/andP; split => //.
apply: leq_trans (leq_addl _ _).
apply: leq_trans (weight_size _) _.
rewrite -subSS.
by apply: leq_size_eotake_e2n.
Qed.

Lemma iknuth_exchance_aux_sorted k (p : nat) q (l : seq bool) :
  0 < q -> `2^ q < size l <= `2^ q.+1 -> p <= q -> p < k ->
  let l1 := iknuth_exchance_aux k (`2^ q) (`2^ p) l in 
  (forall i, i < `2^ p -> 
  [/\ 
  sorted <=%O (eotake p.+1 i l) &
  sorted <=%O (eotake p.+1 (`2^ p + i) l)]) ->
  sorted <=%O l1.
Proof.
move=> g_gt0.
elim: k p l => // k IH [|p] l qLs pLq pLk l1 Hs.
  rewrite {}/l1.
  case: {IH pLk}k => /= [|_].
  - apply: (@iter3_sorted 0 q (iter1 1 l) 0) => //.
      by rewrite size_iter1.
    have [|H1 H2]// := Hs 0.
    by apply: iter1_sorted.
  apply: (@iter3_sorted 0 q (iter1 1 l) 0) => //.
    by rewrite size_iter1.
  have [|H1 H2]// := Hs 0.
  by apply: iter1_sorted.
rewrite /l1 /= -e2Sn e2n_gt0 e2n_div2 //.
apply: IH => //.
- by rewrite size_iter3 ?e2n_gt0 // size_iter1 ?e2n_gt0.
- by rewrite /= // (leq_trans _ pLq).
move=> i Hi.
split => //.
  have iL2p : i < `2^ p.+1 by apply: leq_trans Hi _; rewrite leq_e2n.
  have [Hs1 Hs2] := Hs _ iL2p.
  apply: iter3_sorted => //.
    by rewrite size_iter1 ?e2n_gt0.
  by apply: iter1_sorted.
have iL2p : `2^ p + i < `2^ p.+1 by rewrite ltn_add2l.
have [Hs1 Hs2] := Hs _ iL2p.
apply: iter3_sorted => //.
  by rewrite size_iter1 ?e2n_gt0.
by apply: iter1_sorted.
Qed.

Lemma iknuth_exchance_sorted (l : seq bool) :
  sorted <=%O (iknuth_exchance l).
Proof.
case: (ltP 3 (size l)) => [sl_gt4|]; last first.
  case: l => // a [|b [|c []]]//= _; lia.
have sl_gt1 : 1 < size l by apply: leq_trans sl_gt4.
have up_gt0 : 0 < up_log 2 (size l).
  by rewrite up_log_gt0 // (leq_trans _ sl_gt1).
have up_gt1 : 1 < up_log 2 (size l).
  by rewrite -{1}[2]/(up_log 2 4) leq_up_log.
apply: iknuth_exchance_aux_sorted => //.
- by rewrite -ltnS prednK.
- rewrite prednK //.
  by rewrite !e2nE; apply: up_log_bounds.
- apply: ltn_trans (ltn_ne2n _) _.
  have /andP[] := (up_log_bounds (isT: 1 < 2) sl_gt1).
  by  rewrite e2nE.
move=> i iLu;rewrite prednK //.
set x := up_log 2 _; split.
  have : size (eotake x i l) <= `2^ (x - x).
    apply: leq_size_eotake_e2n => //.
    by rewrite e2nE; apply: up_logP.
  by rewrite subnn; case: eotake => //= a [|].
have : size (eotake x (`2^ x.-1 + i) l) <= `2^ (x - x).
  apply: leq_size_eotake_e2n => //.
  by rewrite e2nE; apply: up_logP.
by rewrite subnn; case: eotake => //= a [|].
Qed.
