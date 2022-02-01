From mathcomp Require Import all_ssreflect perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  Definition of the Batcher sorting algorithm                               *)
(*                                                                            *)
(*      Batcher_merge == the connector that links i to i.+1 for i odd         *)
(*  Batcher_merge_rec == the recursive connect that calls itself on           *)
(*                       the even and odd parts and then apply Batcher_merge  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Batcher.

Variable d : unit.
Variable A : orderType d.

Definition clink_Batcher_merge m : {ffun 'I_m -> 'I_m} :=
  [ffun i : 'I_ _ => if odd i then inext i else ipred i].

Lemma clink_Batcher_merge_proof m : 
  [forall i : 'I_(m + m), clink_Batcher_merge _ (clink_Batcher_merge _ i) == i].
Proof.
apply/forallP => i /=; apply/eqP/val_eqP; rewrite !ffunE.
have mmE : ~~ (odd (m + m)) by rewrite addnn odd_double.
have mm_gt0 : 0 < m + m by apply: leq_ltn_trans (ltn_ord i).
have [iO|iE] := boolP (odd i); rewrite /= !(ipred_val, inext_val).
  case:  ((i : nat) =P (m + m).-1) => [/eqP iEm | /eqP iDm].
    by rewrite iO !inext_val /= !iEm.
  by rewrite /= iO /= ipred_val inext_val (negPf iDm).
have [i1O|i1E] := boolP (odd i.-1); rewrite /= !(ipred_val, inext_val).
  have i_gt0 : 0 < i by case: (i : nat) iE i1O.
  by rewrite prednK // ifN // -eqSS !prednK // neq_ltn ltn_ord.
by case: (i : nat) iE i1E => //= n; case: odd.
Qed.
  
Definition Batcher_merge {m} := connector_of (clink_Batcher_merge_proof m).

Lemma cfun_Batcher_merge n (t : (n + n).-tuple A) : 
  cfun Batcher_merge t = 
  [tuple
    if odd i then min (tnth t i) (tnth t (inext i))
    else max (tnth t i) (tnth t (ipred i)) | i < n + n].
Proof.
apply: eq_from_tnth => i /=.
rewrite /Batcher_merge /cfun /=.
rewrite !tnth_map /= !tnth_ord_tuple ffunE.
have [iO|iE] := boolP (odd i).
  by rewrite ifT // inext_val; case: eqP.
case: leqP => [iLip|] //.
suff -> : ipred i = i by rewrite maxxx minxx.
apply/val_eqP =>> /=; move: iLip; rewrite !ipred_val /=.
by case: (i : nat) => //= i1; rewrite ltnn.
Qed.

Fixpoint Batcher_merge_rec_aux m : network (`2^ m.+1) :=
  if m is m1.+1 then rcons (neodup (Batcher_merge_rec_aux m1)) Batcher_merge
  else [:: cswap ord0 ord_max].

Definition Batcher_merge_rec m := 
  if m is m1.+1 then Batcher_merge_rec_aux m1 else [::].

Fixpoint Batcher m : network (`2^ m) :=
  if m is m1.+1 then ndup (Batcher m1) ++ Batcher_merge_rec m1.+1
  else [::].

End Batcher.

Lemma aabbEabab a b : (a + a) + (b + b) = (a + b) + (a + b).
Proof. by rewrite [RHS]addnAC !addnA. Qed.


Lemma cfun_Batcher_merge_case1 a b c (H : a + b = c + c) : 
  let t1 := tcast H [tuple of nseq a false ++ nseq b true] in
  cfun Batcher_merge t1 = t1. 
Proof.
move=> t1.
rewrite cfun_Batcher_merge.
apply: eq_from_tnth => i.
have cc_gt0 : 0 < c + c by apply: leq_ltn_trans (ltn_ord i).
rewrite !tcastE !(tnth_nth false) /= nth_cat !nth_nseq /= ?size_nseq.
rewrite !if_same -enum_ord !(nth_map i) ?size_enum_ord //.
rewrite !tcastE  nth_ord_enum !(tnth_nth false) /=.
rewrite !nth_cat !nth_nseq /= ?size_nseq inext_val ipred_val.
rewrite !if_same.
have [iLa|aLi] := ltnP i.
  by rewrite minFb (_ : i.-1 < a) ?if_same // (leq_ltn_trans (leq_pred _) iLa).
rewrite ltn_subLR // H ltn_ord /= maxTb minTb.
case: eqP => [->|/eqP iDcc].
  have aLcc : a <= (c + c).-1.
    by rewrite -ltnS prednK // (leq_ltn_trans aLi).
  rewrite ltnNge aLcc /= ltn_subLR // H.
  by case: (c + c) cc_gt0 => //= c1; rewrite leqnn if_same.
have aLi1 : a <= i.+1 by apply: leq_trans aLi _.
rewrite ltnNge aLi1 /= ltn_subLR // H.
rewrite -[odd i]negbK -oddS.
move: (ltn_ord i); rewrite leq_eqVlt => /orP[/eqP i1E|->].
  by rewrite -[in X in _ != X]i1E eqxx in iDcc.
by rewrite if_same.
Qed.

Lemma cfun_Batcher_merge_case12 a b c 
  (H1 : a + b.+2 = c + c) (H2 : a.+1 + b.+1 = c + c) : 
  odd a ->
  let t1 := tcast H1 [tuple of nseq a false ++ true :: false :: nseq b true] in
  let t2 := tcast H2 [tuple of nseq a.+1 false ++ nseq b.+1 true] in
  cfun Batcher_merge t1 = t2. 
Proof.
move=> aO t1 t2.
have bO : odd b.
  have : ~~ odd (c + c) by rewrite addnn odd_double.
  by rewrite -H2 oddD /= aO /= negbK.
rewrite cfun_Batcher_merge.
apply: eq_from_tnth => i.
have cc_gt0 : 0 < c + c by apply: leq_ltn_trans (ltn_ord i).
rewrite !tcastE /= !(tnth_nth false) /= !(nth_map i); last 2 first.
- by rewrite -fintype.enumT -enum_ord size_enum_ord.
- by rewrite -enum_ord size_enum_ord.
rewrite -fintype.enumT -enum_ord !nth_enum_ord // !nth_ord_enum.
rewrite !tcastE /= (tnth_nth false) /= /t1 /=.
rewrite !nth_cat !nth_nseq /= ?size_nseq /=.
rewrite !(tnth_nth false) /=.
rewrite !nth_cat !nth_nseq /= ?size_nseq inext_val ipred_val.
have [iLa|aLi] := ltnP i.
  rewrite minFb maxFb (_ : i.-1 < a) ?if_same; last first.
    by rewrite (leq_ltn_trans (leq_pred _) iLa).
  rewrite (nth_cat _ (nseq _.+1 _)) ?size_nseq /= ltnS ltnW //.
  by rewrite (nth_nseq _ _.+1) if_same.
rewrite (nth_cat _ (nseq _.+1 _)) ?size_nseq ltnS.
rewrite if_same.
move: aLi; rewrite leq_eqVlt => /orP[/eqP<-|aLi].
  rewrite subnn /= leqnn (nth_nseq _ _.+1) leqnn.
  rewrite minTb maxTb.
  case: eqP (H2) => [->/eqP|/eqP iDcc _].
    by rewrite prednK // -[X in _ == X -> _]addn0 eqn_add2l.
  by rewrite aO ltnNge leqnSn /= subSn // subnn.
have i_gt0 : 0 < i by apply: leq_ltn_trans aLi.
rewrite prednK // [i <= a]leqNgt aLi /=.
rewrite (nth_nseq _ _.+1) ltn_subLR // H2 ltn_ord /=.
have i1La : a <= i.+1 by rewrite -ltnS (leq_trans aLi) // ltnW.
move: aLi; rewrite leq_eqVlt => /orP[/eqP<-|aLi].
  by rewrite subSn // subnn /= aO.
have iaE : i - a = (i - a).-2.+2.
  have iLa : a < i by apply: ltn_trans aLi.
  by rewrite !prednK ?subn_gt0 // -ltnS prednK // ltn_subRL ?addn1 // addn0.
rewrite iaE /= nth_nseq.
have ia2Lb : (i - a).-2 < b.
  rewrite -subn2 ltn_subLR ?add2n; last by rewrite iaE.
  rewrite ltn_subLR; last by apply: leq_trans (ltnW aLi).
  by rewrite -addSnnS [X in i < X]H2 ltn_ord.
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
  have := ltn_ord i.
  rewrite -[X in _ < X]H2 -a2E -addSnnS -addn1 leq_add2l.
  rewrite leq_eqVlt => /orP[/eqP bE|->//].
  by have := iDcc; rewrite -a2E -H2 -addSnnS -bE addn1 eqxx.
suff -> : (i.+1 - a).-2 < b by rewrite if_same.
rewrite -subn2 !ltn_subLR //; last by rewrite i1aE.
rewrite add2n -addSnnS [X in _ < X]H2.
have := ltn_ord i; rewrite leq_eqVlt => /orP[/eqP i1E|//].
by case/eqP: iDcc; rewrite -[in RHS]i1E.
Qed.

(* This is the big proof could be improved lots of repetitions *)
Lemma sorted_nfun_Batcher_merge_rec m (t : (`2^ m.+1).-tuple bool) :
  sorted <=%O (ttake t) -> sorted <=%O (tdrop t) ->
  sorted <=%O (nfun (Batcher_merge_rec_aux m) t).
Proof.
elim: m t => [t tS dS|m IH t tS dS /=].
  rewrite [Batcher_merge_rec_aux 0]/= tsorted2 /=.
  by rewrite cswapE_min // cswapE_max // le_minl le_maxr lexx.
rewrite nfun_rcons nfun_eodup.
set n1 := nfun _ _; set n2 := nfun _ _.
have n1P : perm_eq n1 (tetake t) by apply: nfun_perm.
have /isorted_boolP[[a1 b1] n1E] : sorted <=%O n1.
  apply: IH.
    by rewrite ttake_etakeE; apply: etake_sorted => // [] [] [] [].
  by rewrite tdrop_etakeE; apply: etake_sorted => // [] [] [] [].
have n2P : perm_eq n2 (totake t) by apply: nfun_perm.
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
                andbF, andbT) => HH -> //; split=> //.
      by case: (b1) HH => [|x] //; (do 2 case (_./2) => [|?]) => // ->.
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
    rewrite cfun_Batcher_merge_case12 => [|sxxE1|].
    - by rewrite !(addSn, addnS) in sxxE *.
    - rewrite val_tcast.
      by apply/isorted_boolP; exists ((x1 + x1).+2, (y1 + y1).+2).
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
              andbF, andbT) /= => HH ->; split=> //.
    by case: (b1) HH => [|x]; (do 2 case (_./2) => [|?]) => // ->.
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
  rewrite cfun_Batcher_merge_case1 //.
  rewrite val_tcast.
  by apply/isorted_boolP; exists ((x1 + x1).+1, (y1 + y1).+1).
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
              andbF, andbT) => HH -> //; split => //.
    by case: (b1) HH => [|x]; (do 2 case (_./2) => [|?]) => // ->.
  have [/eqP Ea2 /eqP Eb2] : a2 == a3./2 + a4./2 /\ b2 == (b3./2 + b4./2).+1.
    move/allP/(_ false) : (Hperm2); move/allP/(_ true) : (Hperm2).
    rewrite /= !(count_cat, count_nseq) /= !(count_cat, count_nseq) /=.
    rewrite !mul1n !mul0n !(addn0, add0n, add1n, addSn, addnS).
    rewrite !(mem_cat, mem_nseq, inE, eqxx, orTb, andTb, andbT, orbT,
               andbF, orFb, orbF) => -> // HH; split => //.
    by case: (a2) HH => [|?]//; (do 2 (case: (_./2) => [|?]//)) => ->.
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
  rewrite cfun_Batcher_merge_case1.
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
rewrite cfun_Batcher_merge_case1.
by rewrite val_tcast; apply/isorted_boolP; exists ((x1 + x1), (y1 + y1)).
Qed.
Qed.

Lemma sorted_nfun_Batcher_merge m (t : (`2^ m.+1).-tuple bool) :
  sorted <=%O (ttake t) -> sorted <=%O (tdrop t) ->
  sorted <=%O (nfun (Batcher_merge_rec m.+1) t).
Proof. exact: sorted_nfun_Batcher_merge_rec. Qed.

Lemma sorted_nfun_Batcher m (t : (`2^ m).-tuple bool) :
  sorted <=%O (nfun (Batcher m) t).
Proof.
elim: m t => [|m IH t] /=.
  by do 2 case => // [] [] [].
rewrite nfun_cat.
apply: sorted_nfun_Batcher_merge_rec.
  rewrite nfun_dup.
  rewrite ttakeK.
  by apply: IH.
rewrite nfun_dup.
rewrite tdropK.
by apply: IH.
Qed.

Lemma sorted_Batcher m : Batcher m \is sorting.
Proof.
apply/forallP => x; apply: sorted_nfun_Batcher.
Qed.

