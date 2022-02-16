From mathcomp Require Import all_ssreflect perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  Definition of the Batcher odd-even merge sorting algorithm                *)
(*                                                                            *)
(*      batcher_merge == the connector that links i to i.+1 for i odd         *)
(*  batcher_merge_rec == the recursive network that calls itself on           *)
(*                       the even and odd parts and then apply batcher_merge  *)
(*                    == the network that calls itself on the top and bottom  *)
(*                       parts and then apply batcher_merge_rec               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Batcher.

Variable d : unit.
Variable A : orderType d.

Definition clink_batcher_merge m : {ffun 'I_m -> 'I_m} :=
  [ffun i : 'I_ _ => if odd i then inext i else ipred i].

Lemma clink_batcher_merge_proof m : 
  [forall i : 'I_m, clink_batcher_merge _ (clink_batcher_merge _ i) == i].
Proof.
apply/forallP => i /=; apply/eqP/val_eqP; rewrite !ffunE.
have m_gt0 : 0 < m by apply: leq_ltn_trans (ltn_ord i).
have [/= oI|eI] := boolP (odd i); rewrite ?(val_inext, val_ipred) /=.
  have [iE | /eqP iD] := (i : nat) =P m.-1.
    by rewrite oI !val_inext /= iE !eqxx.
  by rewrite oddS oI /= val_ipred /= val_inext /= (negPf iD).
case: (ltngtP i 0) => // [o_gt0 | iE].
  rewrite -[odd _]negbK -oddS prednK // eI val_inext val_ipred.
  rewrite -[i.-1 == _]eqSS !prednK //.
  by rewrite [(i : nat) == m]eqn_leq [m <= _]leqNgt ltn_ord andbF.
by rewrite iE /= !(val_inext, val_ipred) iE.
Qed.
  
Definition batcher_merge {m} := connector_of (clink_batcher_merge_proof m).

Lemma cfun_batcher_merge n (t : n.-tuple A) : 
  cfun batcher_merge t = 
  [tuple
    if odd i then min (tnth t i) (tnth t (inext i))
    else max (tnth t i) (tnth t (ipred i)) | i < n].
Proof.
apply: eq_from_tnth => i /=.
rewrite /batcher_merge /cfun /=.
rewrite !tnth_map /= !tnth_ord_tuple ffunE.
have [iO|iE] := boolP (odd i).
  by rewrite ifT // val_inext; case: eqP.
case: leqP => [iLip|] //.
suff -> : ipred i = i by rewrite maxxx minxx.
apply/val_eqP =>> /=; move: iLip; rewrite !val_ipred /=.
by case: (i : nat) => //= i1; rewrite ltnn.
Qed.

Lemma tcast_batcher_merge m1 m2 (m2Em1 : m2 = m1) (t : m2.-tuple A) :
  cfun batcher_merge (tcast m2Em1 t) = tcast m2Em1 (cfun batcher_merge t).
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
suff ci2iEci1i : clink batcher_merge (nth i2 (enum 'I_m2) i) = 
                 clink batcher_merge (nth i1 (enum 'I_m1) i) :> nat.
  congr (if _ then min _ _ else max _ _); first by rewrite ci2iEci1i.
  - by rewrite !(tnth_nth a) val_tcast !nth_enum_ord // m2Em1.
  - by rewrite !(tnth_nth a) val_tcast /= ci2iEci1i.
  - by rewrite !(tnth_nth a) val_tcast !nth_enum_ord // m2Em1.
  by rewrite !(tnth_nth a) val_tcast /= ci2iEci1i.
rewrite !ffunE.
have im2Eim1 : nth i2 (enum 'I_m2) i = nth i1 (enum 'I_m1) i :> nat.
  by rewrite !nth_enum_ord // m2Em1.
rewrite im2Eim1; case: odd; last by rewrite !val_ipred im2Eim1.
by rewrite !val_inext im2Eim1 [X in X.-1]m2Em1.
Qed.

Fixpoint batcher_merge_rec_aux m : network (`2^ m.+1) :=
  if m is m1.+1 then rcons (neodup (batcher_merge_rec_aux m1)) batcher_merge
  else [:: cswap ord0 ord_max].

Lemma size_batcher_merge_rec_aux m : size (batcher_merge_rec_aux m) = m.+1.
Proof.
elim: m => [//| m IH] /=.
by rewrite size_rcons size_map size_zip minnn IH.
Qed.

Definition batcher_merge_rec m := 
  if m is m1.+1 then batcher_merge_rec_aux m1 else [::].

Lemma size_batcher_merge_rec m : size (batcher_merge_rec m) = m.
Proof. by case: m => //= m; rewrite size_batcher_merge_rec_aux. Qed.

Fixpoint batcher m : network (`2^ m) :=
  if m is m1.+1 then ndup (batcher m1) ++ batcher_merge_rec m1.+1
  else [::].

Lemma size_batcher m : size (batcher m) = (m * m.+1)./2.
Proof. 
elim: m => [//|m IH].
rewrite [in LHS]/= size_cat size_map size_zip minnn.
rewrite size_batcher_merge_rec_aux IH.
by rewrite -addn2 mulnDr -!divn2 divnDMl // mulnC.
Qed.

End Batcher.

Lemma aabbEabab a b : (a + a) + (b + b) = (a + b) + (a + b).
Proof. by rewrite [RHS]addnAC !addnA. Qed.

Lemma cfun_batcher_merge_case1 a b :
  ~~ odd (a + b) -> 
  let t1 := [tuple of nseq a false ++ nseq b true] in
  cfun batcher_merge t1 = t1. 
Proof.
rewrite oddD negb_add => /eqP aOE.
move=> t1.
rewrite cfun_batcher_merge.
apply: eq_from_tnth => i.
have ab_gt0 : 0 < a + b by apply: leq_ltn_trans (ltn_ord i).
rewrite !(tnth_nth false) /= nth_cat !nth_nseq /= ?size_nseq.
rewrite !if_same -enum_ord !(nth_map i) ?size_enum_ord //.
rewrite !nth_ord_enum !(tnth_nth false) /=.
rewrite !nth_cat !nth_nseq /= ?size_nseq val_inext val_ipred.
rewrite !if_same.
have [iLa|aLi] := ltnP i.
  by rewrite minFb (_ : i.-1 < a) ?if_same // (leq_ltn_trans (leq_pred _) iLa).
rewrite ltn_subLR // ltn_ord /= maxTb minTb.
have aLab : a < a + b by apply: leq_ltn_trans (ltn_ord i).
case: eqP => [->|/eqP iDab].
rewrite prednK // -[odd _]negbK -oddS prednK // oddD -aOE addbb /=.
rewrite leqNgt (leq_ltn_trans _ (ltn_ord i)) //= ifT //.
case: (b) aLab => [|b1 _]; first by rewrite addn0 ltnn.
  by rewrite addnS /= addnC addnK.
rewrite [_ < a]ltnNge (leq_trans aLi) //=.
rewrite ltn_subLR; last by rewrite (leq_trans aLi).
by rewrite ltn_neqAle ltn_ord -[X in _ != X](prednK ab_gt0) eqSS iDab if_same.
Qed.

Lemma cfun_batcher_merge_case12 a b :
  odd a -> odd b ->
  cfun batcher_merge [tuple of nseq a false ++ true :: false :: nseq b true] =
       [tuple of nseq a.+1 false ++ nseq b.+1 true] :> seq _. 
Proof.
move=> aO bO.
have ab_gt0 : 0 < a + b.+2 by rewrite addnS.
pose u := Ordinal ab_gt0.
rewrite cfun_batcher_merge.
apply: (@eq_from_nth _ false) => [|i].
  by rewrite /= !size_tuple !addnS card_ord.
rewrite /= size_tuple card_ord => iLab.
rewrite !(nth_map u); last 2 first.
- by rewrite -fintype.enumT -enum_ord size_enum_ord.
- by rewrite -enum_ord size_enum_ord.
rewrite -fintype.enumT -enum_ord !nth_enum_ord //.
have -> : i = Ordinal iLab by [].
rewrite !nth_ord_enum /=.
rewrite (tnth_nth false) /=.
rewrite !nth_cat !nth_nseq /= ?size_nseq /=.
rewrite !(tnth_nth false) /=.
rewrite !nth_cat !nth_nseq /= ?size_nseq val_inext val_ipred.
have [iLa|aLi] := ltnP i.
  rewrite minFb maxFb (_ : i.-1 < a) ?if_same; last first.
    by rewrite (leq_ltn_trans (leq_pred _) iLa).
  rewrite (nth_cat _ (nseq _.+1 _)) ?size_nseq /= ltnS ltnW //.
  by rewrite (nth_nseq _ _.+1) if_same.
rewrite (nth_cat _ (nseq _.+1 _)) ?size_nseq ltnS.
rewrite if_same /=.
move: aLi; rewrite leq_eqVlt => /orP[/eqP<-|aLi].
  rewrite subnn /= leqnn (nth_nseq _ _.+1) leqnn.
  rewrite minTb maxTb !addnS /=.
  rewrite eqn_leq [(_ + _).+1 <= a]leqNgt ltnS leq_addr andbF /=.
  by rewrite aO ltnNge leqnSn /= subSn // subnn.
have i_gt0 : 0 < i by apply: leq_ltn_trans aLi.
rewrite prednK // [i <= a]leqNgt aLi /=.
rewrite (nth_nseq _ _.+1) ltn_subLR // addSnnS iLab /=.
have i1La : a <= i.+1 by rewrite -ltnS (leq_trans aLi) // ltnW.
move: aLi; rewrite leq_eqVlt => /orP[/eqP<-|aLi].
  by rewrite subSn // subnn /= aO.
have iaE : i - a = (i - a).-2.+2.
  have iLa : a < i by apply: ltn_trans aLi.
  by rewrite !prednK ?subn_gt0 // -ltnS prednK // ltn_subRL ?addn1 // addn0.
rewrite iaE /= nth_nseq.
have ia2Lb : (i - a).-2 < b.
  rewrite -subn2 ltn_subLR ?add2n; last by rewrite iaE.
  by rewrite ltn_subLR // (leq_trans _ (ltnW aLi)).
rewrite ia2Lb minTb maxTb.
case: eqP => [|/eqP iDcc].
  by rewrite iaE /= nth_nseq ia2Lb ltnNge (leq_trans _ (ltnW aLi)) //= if_same.
rewrite [i.+1 < a]ltnNge i1La /=.
have i1aE : i.+1 - a = (i.+1 - a).-2.+2.
  rewrite subSn /=.
    by rewrite prednK /= // subn_gt0 (ltn_trans _ aLi).
  by apply: leq_trans (ltnW aLi).
rewrite i1aE /= nth_nseq.
move: aLi; rewrite leq_eqVlt => /orP[/eqP a2E|aLi].
  rewrite -a2E /= aO /= -add3n addnK /=.
  have := iLab.
  rewrite -[X in _ < X]addSnnS -a2E -addSnnS -addn1 leq_add2l.
  rewrite leq_eqVlt => /orP[/eqP bE|->//].
  by have := iDcc; rewrite -a2E -addSnnS -addSnnS -bE addn1 eqxx.
suff -> : (i.+1 - a).-2 < b by rewrite if_same.
rewrite -subn2 !ltn_subLR //; last by rewrite i1aE.
rewrite add2n -[X in _ < X]addSnnS.
have := iLab; rewrite leq_eqVlt => /orP[/eqP i1E|//].
  by case/eqP: iDcc; rewrite -[in RHS]i1E.
by rewrite addSnnS.
Qed.

(* This is the big proof could be improved lots of repetitions *)
Lemma sorted_nfun_batcher_merge_rec m (t : (`2^ m.+1).-tuple bool) :
  sorted <=%O (ttake t) -> sorted <=%O (tdrop t) ->
  sorted <=%O (nfun (batcher_merge_rec_aux m) t).
Proof.
elim: m t => [t tS dS|m IH t tS dS /=].
  rewrite [batcher_merge_rec_aux 0]/= tsorted2 /=.
  by rewrite cswapE_min // cswapE_max // le_minl le_maxr lexx.
rewrite nfun_rcons nfun_eodup.
set n1 := nfun _ _; set n2 := nfun _ _.
have n1P : perm_eq n1 (tetake t) by apply: perm_nfun.
have /isorted_boolP[[a1 b1] n1E] : sorted <=%O n1.
  apply: IH.
    by rewrite ttake_etakeE; apply: etake_sorted => // [] [] [] [].
  by rewrite tdrop_etakeE; apply: etake_sorted => // [] [] [] [].
have n2P : perm_eq n2 (totake t) by apply: perm_nfun.
have /isorted_boolP[[a2 b2] n2E] : sorted <=%O n2.
  apply: IH.
  - by rewrite ttake_otakeE; apply: otake_sorted => // [] [] [] [].
  - by rewrite tdrop_otakeE; apply: otake_sorted => // [] [] [] [].
have /isorted_boolP[[a3 b3] tSE] := tS.
have /isorted_boolP[[a4 b4] dSE] := dS.
have /val_eqP tE := cat_ttake_tdrop t; rewrite /= tSE dSE in tE.
have /val_eqP eotE := eocat_tetake_totake t.
rewrite /= (eqP tE) !(etake_cat, otake_cat, etake_cat_nseq, otake_nseq, 
                      etake_nseq, size_cat, size_nseq, otake_cat_nseq) in eotE.
have : ~~ odd (size (ttake t)) by rewrite size_tuple addnn odd_double.
rewrite tSE size_cat !size_nseq => /negPf b3O. 
rewrite b3O in eotE; rewrite oddD in b3O.
have : ~~ odd (size (tdrop t)) by rewrite size_tuple addnn odd_double.
rewrite dSE size_cat !size_nseq oddD => /negPf b4O.
case: (boolP (odd a3)) b3O => [a3O /negP/negP b3O |/negPf a3E b3E].
  case: (boolP (odd a4)) b4O => [a4O /negP/negP b4O|/negPf a4E b4E].
(* First case *)
    move: n1P.
    rewrite tetakeE (eqP tE) !(etake_cat, otake_cat, otake_nseq, etake_nseq,
                              size_cat, size_nseq, uphalf_half) oddD a3O a4O 
            b3O b4O [if true (+) true then _ else _]/= !add1n {1}n1E => Hperm1.
    move: n2P.
    rewrite totakeE (eqP tE) !(etake_cat, otake_cat, otake_nseq, etake_nseq,
                              size_cat, size_nseq, uphalf_half) oddD a3O a4O
            b3O b4O [if true (+) true then _ else _]/= !add1n {1}n2E => Hperm2.
    have [/eqP Ea1 /eqP Eb1] : a1 == (a3./2 + a4./2).+2 /\
                               b1 == b3./2 + b4./2.
      move/allP/(_ false) : (Hperm1); move/allP/(_ true) : (Hperm1).
      rewrite /= !(count_cat, count_nseq) /= !(count_cat, count_nseq) /=.
      rewrite !mul1n !mul0n !(addn0, add0n) !add1n !(addSn, addnS).
      rewrite !(mem_cat, inE, mem_nseq, eqxx, orbT, orTb, orFb, orbF, 
                andbF, andbT) => Hb1 -> //; split=> //.
      by case: (b1) Hb1 => [|x] //; (do 2 case (_./2) => [|?]) => // ->.
    have [/eqP Ea2 /eqP Eb2] : a2 == a3./2 + a4./2 /\ b2 == (b3./2 + b4./2).+2.
      move/allP/(_ false) : (Hperm2); move/allP/(_ true) : (Hperm2).
      rewrite /= !(count_cat, count_nseq) /= !(count_cat, count_nseq) /=.
      rewrite !mul1n !mul0n !(addn0, add0n, add1n, addSn, addnS).
      rewrite !(mem_cat, mem_nseq, inE, eqxx, orTb, andTb, andbT, orbT,
                andbF, orFb, orbF) => -> //.
      by case: (a2) => [|?]//; (do 2 (case: (_./2) => [|?]//)) => ->.
    set x1 := (_ + _) in Ea1 Ea2; set y1 := (_ + _) in Eb1 Eb2.
    pose xx := nseq (x1 + x1).+1 false ++ 
                    [:: true, false & nseq (y1 + y1).+1 true].
    have xxE : [tuple of eocat n1 n2] = [tuple of xx]:> seq bool.
      rewrite -[RHS]eocat_nseq_catDSS.
      congr eocat; first by rewrite n1E; congr (nseq _ _ ++ nseq _ _).
      by rewrite n2E; congr (nseq _ _ ++ nseq _ _).
    have sxxE : size [tuple of eocat n1 n2] = size [tuple of eocat n1 n2] by [].
    rewrite [in LHS]xxE !size_tuple in sxxE.
    have -> : [tuple of eocat n1 n2] = tcast sxxE  [tuple of xx].
      by apply/val_eqP/eqP=> /=; rewrite [in RHS]val_tcast.
    rewrite tcast_batcher_merge /= val_tcast cfun_batcher_merge_case12 //.
    - by apply/isorted_boolP; exists ((x1 + x1).+2, (y1 + y1).+2).
    - by rewrite addnn /= odd_double.
    by rewrite addnn /= odd_double.
(* Second case *)
  rewrite /= in b4E.
  move: n1P.
  rewrite tetakeE (eqP tE) !(etake_cat, otake_cat, otake_nseq, etake_nseq,
                            size_cat, size_nseq, uphalf_half) oddD a3O b3O
        a4E b4E [if true (+) true then _ else _]/= !add0n !add1n {1}n1E 
        => Hperm1.
  move: n2P.
  rewrite totakeE (eqP tE) !(etake_cat, otake_cat, otake_nseq, etake_nseq,
                             size_cat, size_nseq, uphalf_half) oddD a3O a4E
          b3O b4E [if true (+) true then _ else _]/= {1}n2E => Hperm2.
  have [/eqP Ea1 /eqP Eb1] : a1 == (a3./2 + a4./2).+1 /\ b1 == b3./2 + b4./2.
    move/allP/(_ false) : (Hperm1); move/allP/(_ true) : (Hperm1).
    rewrite /= !(count_cat, count_nseq) /= .
    rewrite !mul1n !mul0n !(addn0, add0n) !add1n /=.
    rewrite !(mem_cat, inE, mem_nseq, eqxx, orbT, orTb, orFb, orbF, 
              andbF, andbT) /= => Hb1 ->; split=> //.
    by case: (b1) Hb1 => [|x]; (do 2 case (_./2) => [|?]) => // ->.
  have [/eqP Ea2 /eqP Eb2] : a2 == a3./2 + a4./2 /\ b2 == (b3./2 + b4./2).+1.
    move/allP/(_ false) : (Hperm2); move/allP/(_ true) : (Hperm2).
    rewrite /= !(count_cat, count_nseq) /= !(count_cat, count_nseq) /=.
    rewrite !mul1n !mul0n !(addn0, add0n, add1n, addSn, addnS).
    rewrite !(mem_cat, mem_nseq, inE, eqxx, orTb, andTb, andbT, orbT,
              andbF, orFb, orbF) => -> //.
    by case: (a2) => [|?]//; (do 2 (case: (_./2) => [|?]//)) => ->.
  set x1 := (_ + _) in Ea1 Ea2; set y1 := (_ + _) in Eb1 Eb2.
  pose xx := nseq (x1 + x1).+1 false ++ nseq (y1 + y1).+1 true.
  have xxE : [tuple of eocat n1 n2] = [tuple of xx]:> seq bool.
    rewrite -[RHS]eocat_nseq_catDS.
    congr eocat; first by rewrite n1E; congr (nseq _ _ ++ nseq _ _).
    by rewrite n2E; congr (nseq _ _ ++ nseq _ _).
  have sxxE : size [tuple of eocat n1 n2] = size [tuple of eocat n1 n2] by [].
  rewrite [in LHS]xxE !size_tuple in sxxE.
  have -> : [tuple of eocat n1 n2] = tcast sxxE  [tuple of xx].
    by apply/val_eqP/eqP=> /=; rewrite [in RHS]val_tcast.
  rewrite tcast_batcher_merge cfun_batcher_merge_case1; last first.
    by rewrite sxxE addnn odd_double.
  apply/isorted_boolP; exists ((x1 + x1).+1, (y1 + y1).+1).
  by rewrite val_tcast.
rewrite /= in b3E.
case: (boolP (odd a4)) b4O => [a4O /negP/negP b4O|/negPf a4E b4E].
(* Third case *)
  move: n1P.
  rewrite tetakeE (eqP tE) !(etake_cat, otake_cat, otake_nseq, etake_nseq,
                             size_cat, size_nseq, uphalf_half) oddD
          a3E b3E a4O [if false (+) false then _ else _]/= !add0n {1}n1E
          => Hperm1.
  move: n2P.
  rewrite totakeE (eqP tE) !(etake_cat, otake_cat, otake_nseq, etake_nseq,
                             size_cat, size_nseq, uphalf_half) oddD a3E b3E
                   a4O b4O [if false (+) false then _ else _]/= {1}n2E 
          => Hperm2.
  have [/eqP Ea1 /eqP Eb1] : a1 == (a3./2 + a4./2).+1 /\ b1 == b3./2 + b4./2.
    move/allP/(_ false) : (Hperm1); move/allP/(_ true) : (Hperm1).
    rewrite /= !(count_cat, count_nseq) /= !(count_cat, count_nseq) /=.
    rewrite !mul1n !mul0n !(addn0, add0n) !add1n !(addSn, addnS).
    rewrite !(mem_cat, inE, mem_nseq, eqxx, orbT, orTb, orFb, orbF, 
              andbF, andbT) => Hb1 -> //; split => //.
    by case: (b1) Hb1 => [|x]; (do 2 case (_./2) => [|?]) => // ->.
  have [/eqP Ea2 /eqP Eb2] : a2 == a3./2 + a4./2 /\ b2 == (b3./2 + b4./2).+1.
    move/allP/(_ false) : (Hperm2); move/allP/(_ true) : (Hperm2).
    rewrite /= !(count_cat, count_nseq) /= !(count_cat, count_nseq) /=.
    rewrite !mul1n !mul0n !(addn0, add0n, add1n, addSn, addnS).
    rewrite !(mem_cat, mem_nseq, inE, eqxx, orTb, andTb, andbT, orbT,
               andbF, orFb, orbF) => -> // Hb1; split => //.
    by case: (a2) Hb1 => [|?]//; (do 2 (case: (_./2) => [|?]//)) => ->.
  set x1 := (_ + _) in Ea1 Ea2; set y1 := (_ + _) in Eb1 Eb2.
  pose xx := nseq (x1 + x1).+1 false ++ nseq (y1 + y1).+1 true.
  have xxE : [tuple of eocat n1 n2] = [tuple of xx]:> seq bool.
    rewrite -[RHS]eocat_nseq_catDS.
    congr eocat; first by rewrite n1E; congr (nseq _ _ ++ nseq _ _).
    by rewrite n2E; congr (nseq _ _ ++ nseq _ _).
  have sxxE : size [tuple of eocat n1 n2] = size [tuple of eocat n1 n2] by [].
  rewrite [in LHS]xxE !size_tuple in sxxE.
  have -> : [tuple of eocat n1 n2] = tcast sxxE  [tuple of xx].
    by apply/val_eqP/eqP=> /=; rewrite [in RHS]val_tcast.
  rewrite tcast_batcher_merge cfun_batcher_merge_case1; last first.
    by rewrite sxxE addnn odd_double.
  by rewrite val_tcast; apply/isorted_boolP; exists ((x1 + x1).+1, (y1 + y1).+1).
(* Fourth case *)
rewrite /= in b4E.
move: n1P.
rewrite tetakeE (eqP tE) !(etake_cat, otake_cat, otake_nseq, etake_nseq,
                           size_cat, size_nseq, uphalf_half) oddD
        a3E b3E a4E b4E [if false (+) false then _ else _]/= !add0n {1}n1E
        => Hperm1.
move: n2P.
rewrite totakeE (eqP tE) !(etake_cat, otake_cat, otake_nseq, etake_nseq,
                           size_cat, size_nseq, uphalf_half) oddD a3E b3E
        a4E b4E [if false (+) false then _ else _]/= {1}n2E => Hperm2.
have [/eqP Ea1 /eqP Eb1] : a1 == a3./2 + a4./2 /\ b1 == b3./2 + b4./2.
  move/allP/(_ false) : (Hperm1); move/allP/(_ true) : (Hperm1).
  rewrite /= !(count_cat, count_nseq) /=.
  rewrite !mul1n !mul0n !(addn0, add0n).
  rewrite !(mem_cat, inE, mem_nseq, eqxx, orbT, orTb, orFb, orbF, 
            andbF, andbT) => Hb1 Ha1 //; split.
    by case: (a1) Ha1 => [|x]; (do 2 case (_./2) => [|?]) => // ->.
  by  case: (b1) Hb1 => [|x]; (do 2 case (_./2) => [|?]) => // ->.
have [/eqP Ea2 /eqP Eb2] : a2 == a3./2 + a4./2 /\ b2 == b3./2 + b4./2.
  move/allP/(_ false) : (Hperm2); move/allP/(_ true) : (Hperm2).
  rewrite /= !(count_cat, count_nseq) /=.
  rewrite !mul1n !mul0n !(addn0, add0n, add1n, addSn, addnS).
  rewrite !(mem_cat, mem_nseq, inE, eqxx, orTb, andTb, andbT, orbT,
            andbF, orFb, orbF) => Hb2 Ha2; split.
    by case: (a2) Ha2 => [|?]//; (do 2 (case: (_./2) => [|?]//)) => ->.
  by case: (b2) Hb2 => [|?]//; (do 2 (case: (_./2) => [|?]//)) => ->.
set x1 := (_ + _) in Ea1 Ea2; set y1 := (_ + _) in Eb1 Eb2.
pose xx := nseq (x1 + x1) false ++ nseq (y1 + y1) true.
have xxE : [tuple of eocat n1 n2] = [tuple of xx]:> seq bool.
  rewrite -[RHS](@eocat_nseq_catD _ _ _ _ _ y1).
  congr eocat; first by rewrite n1E; congr (nseq _ _ ++ nseq _ _).
  by rewrite n2E; congr (nseq _ _ ++ nseq _ _).
have sxxE : size [tuple of eocat n1 n2] = size [tuple of eocat n1 n2] by [].
rewrite [in LHS]xxE !size_tuple in sxxE.
have -> : [tuple of eocat n1 n2] = tcast sxxE  [tuple of xx].
  by apply/val_eqP/eqP=> /=; rewrite [in RHS]val_tcast.
rewrite tcast_batcher_merge cfun_batcher_merge_case1; last first.
  by rewrite sxxE addnn odd_double.
by rewrite val_tcast; apply/isorted_boolP; exists ((x1 + x1), (y1 + y1)).
Qed.

Lemma sorted_nfun_batcher_merge m (t : (`2^ m.+1).-tuple bool) :
  sorted <=%O (ttake t) -> sorted <=%O (tdrop t) ->
  sorted <=%O (nfun (batcher_merge_rec m.+1) t).
Proof. exact: sorted_nfun_batcher_merge_rec. Qed.

Lemma sorted_nfun_batcher m (t : (`2^ m).-tuple bool) :
  sorted <=%O (nfun (batcher m) t).
Proof.
elim: m t => [t|m IH t] /=; first by apply: tsorted01.
rewrite nfun_cat.
apply: sorted_nfun_batcher_merge_rec.
  by rewrite nfun_dup ttakeK; apply: IH.
by rewrite nfun_dup; rewrite tdropK; apply: IH.
Qed.

Lemma sorted_batcher m : batcher m \is sorting.
Proof. apply/forallP => x; apply: sorted_nfun_batcher. Qed.

