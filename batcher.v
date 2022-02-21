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

Definition batcher_merge {m} := @codd_jump m 1.

Lemma cfun_batcher_merge n (t : n.-tuple A) : 
  cfun batcher_merge t = 
  [tuple
    if odd i then min (tnth t i) (tnth t (inext i))
    else max (tnth t i) (tnth t (ipred i)) | i < n].
Proof.
rewrite [LHS]cfun_odd_jump //.
apply/val_eqP/eqP=> /=; apply/eq_map => i;
      congr (if _ then min (tnth _ _) (tnth _ _) 
             else max _ _).
  case: (n) i => //= n1 i; rewrite add1n.
  by have := ltn_ord i; rewrite ltnS; case: (ltngtP i n1).
congr (tnth _ _); apply/val_eqP/eqP=> /=.
rewrite /isub /ipred.
by case: (n) i => //= n1 i; case: (i : nat) => [|i1]; rewrite ?addn1 ?subn1.
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

Lemma cfun_batcher_sorted_even m (t : m.-tuple bool) :
  sorted <=%O t -> ~~ odd m -> cfun batcher_merge t = t. 
Proof.
rewrite isorted_noFT => /eqP tE.
have mE : m = noF t + noT t.
  by rewrite -[LHS](size_tuple t) tE size_cat !size_nseq !noE addnC.
rewrite [X in odd X]mE oddD negb_add => /eqP odd_noE.
rewrite cfun_batcher_merge.
apply: eq_from_tnth => i.
have m_gt0 : 0 < m by apply: leq_ltn_trans (ltn_ord i).
rewrite !(tnth_nth true) /= tE nth_cat !nth_nseq /= size_nseq.
rewrite !if_same -enum_ord !(nth_map i) ?size_enum_ord //.
rewrite !nth_ord_enum !(tnth_nth false) /=.
rewrite tE !nth_cat !nth_nseq /= ?size_nseq val_inext val_ipred !noE !if_same.
have [iLF|FLi] := ltnP i.
  by rewrite minFb (_ : i.-1 < noF _) ?if_same ?(leq_ltn_trans (leq_pred _) _).
rewrite ltn_subLR // -mE ltn_ord /= maxTb minTb.
have FLm : noF t < m by apply: leq_ltn_trans (ltn_ord i).
case: eqP => [->|/eqP iDm1].
  rewrite prednK // leqNgt FLm /= ltn_subLR; last by rewrite -ltnS prednK.
  by rewrite -mE prednK // leqnn if_same.
rewrite ltnNge (leq_trans FLi) //= ltn_subLR ?(leq_trans FLi) //.
rewrite -mE [X in if _ then X else _]ifT ?if_same //.
by rewrite ltn_neqAle ltn_ord -[X in _ != X]prednK // eqSS iDm1.
Qed.

Lemma sorted_batcher_merge  (m : nat) (t : (m + m).-tuple bool) :
 noF (totake t) <= noF (tetake t) <= (noF (totake t)).+2 ->
 sorted <=%O (tetake t) -> sorted <=%O (totake t) ->
 sorted <=%O (cfun batcher_merge t).
Proof.
move=> /andP[FotLFet FotLFet2] eS oS.
pose i := noF (tetake t) - noF (totake t).
have i_le2 : i <= 2 by rewrite leq_subLR addn2.
have nFE : noF (tetake t) = noF (totake t) + i by rewrite addnC subnK.
have [ceS coF ncFE] := sorted_odd_jump (isT : odd 1) i_le2 eS oS nFE.
set  u := i - _ in ncFE; suff uE : u = (u != 0).
  rewrite uE in ncFE.
  by apply: sorted_tetake_totake ncFE.
by rewrite /u; case: (i) i_le2 => // [] [|[]].
Qed.
 
(* This is the big proof could be improved : lots of repetitions *)
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
have n1S : sorted <=%O n1.
  apply: IH.
    by rewrite ttake_etakeE; apply: etake_sorted => // [] [] [] [].
  by rewrite tdrop_etakeE; apply: etake_sorted => // [] [] [] [].
have n2P : perm_eq n2 (totake t) by apply: perm_nfun.
have n2S : sorted <=%O n2.
  apply: IH.
  - by rewrite ttake_otakeE; apply: otake_sorted => // [] [] [] [].
  - by rewrite tdrop_otakeE; apply: otake_sorted => // [] [] [] [].
apply: sorted_batcher_merge; rewrite ?(tetakeK, totakeK) //.
have /isorted_boolP[[a1 b1] n1E] := n1S.
have /isorted_boolP[[a2 b2] n2E] := n2S.
rewrite !n1E !n2E !noE.
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
rewrite tetakeE totakeE (eqP tE) !(etake_cat, otake_cat, otake_nseq, 
                                    etake_nseq, size_cat, size_nseq, 
                                    uphalf_half)
         oddD n1E n2E in n1P n2P.
case: (boolP (odd a3)) b3O => [a3O /negP/negP b3O |/negPf a3E b3E].
  case: (boolP (odd a4)) b4O => [a4O /negP/negP b4O|/negPf a4E b4E].
(* First case *)
    rewrite a3O a4O b3O b4O [if true (+) true then _ else _]/= !add1n in n1P.
    rewrite a3O a4O b3O b4O [if true (+) true then _ else _]/= !add1n in n2P.
    have [/eqP Ea1 /eqP Eb1] : a1 == (a3./2 + a4./2).+2 /\
                               b1 == b3./2 + b4./2.
      move/allP/(_ false) : (n1P); move/allP/(_ true) : n1P.
      rewrite /= !(count_cat, count_nseq) /= !(count_cat, count_nseq) /=.
      rewrite !mul1n !mul0n !(addn0, add0n) !add1n !(addSn, addnS).
      rewrite !(mem_cat, inE, mem_nseq, eqxx, orbT, orTb, orFb, orbF, 
                andbF, andbT) => Hb1 -> //; split=> //.
      by case: (b1) Hb1 => [|x] //; (do 2 case (_./2) => [|?]) => // ->.
    have [/eqP Ea2 /eqP Eb2] : a2 == a3./2 + a4./2 /\ b2 == (b3./2 + b4./2).+2.
      move/allP/(_ false) : (n2P); move/allP/(_ true) : n2P.
      rewrite /= !(count_cat, count_nseq) /= !(count_cat, count_nseq) /=.
      rewrite !mul1n !mul0n !(addn0, add0n, add1n, addSn, addnS).
      rewrite !(mem_cat, mem_nseq, inE, eqxx, orTb, andTb, andbT, orbT,
                andbF, orFb, orbF) => -> //.
      by case: (a2) => [|?]//; (do 2 (case: (_./2) => [|?]//)) => ->.
    by move=> {a3O b3O a4O b4O n1P n2P}//; lia.
(* Second case *)
  rewrite /= in b4E.
  rewrite a3O b3O a4E b4E [if true (+) true then _ else _]/= 
          !add0n !add1n in n1P. 
  rewrite a3O a4E b3O b4E [if true (+) true then _ else _]/= in n2P.
  have [/eqP Ea1 /eqP Eb1] : a1 == (a3./2 + a4./2).+1 /\ b1 == b3./2 + b4./2.
    move/allP/(_ false) : (n1P); move/allP/(_ true) : n1P.
    rewrite /= !(count_cat, count_nseq) /= .
    rewrite !mul1n !mul0n !(addn0, add0n) !add1n /=.
    rewrite !(mem_cat, inE, mem_nseq, eqxx, orbT, orTb, orFb, orbF, 
              andbF, andbT) /= => Hb1 ->; split=> //.
    by case: (b1) Hb1 => [|x]; (do 2 case (_./2) => [|?]) => // ->.
  have [/eqP Ea2 /eqP Eb2] : a2 == a3./2 + a4./2 /\ b2 == (b3./2 + b4./2).+1.
    move/allP/(_ false) : (n2P); move/allP/(_ true) : n2P.
    rewrite /= !(count_cat, count_nseq) /= !(count_cat, count_nseq) /=.
    rewrite !mul1n !mul0n !(addn0, add0n, add1n, addSn, addnS).
    rewrite !(mem_cat, mem_nseq, inE, eqxx, orTb, andTb, andbT, orbT,
              andbF, orFb, orbF) => -> //.
    by case: (a2) => [|?]//; (do 2 (case: (_./2) => [|?]//)) => ->.
  by move=> {a3O b3O a4E b4E n1P n2P}//; lia.  
case: (boolP (odd a4)) b4O => [a4O /negP/negP b4O|/negPf a4E b4E].
(* Third case *)
  rewrite /= in b3E.
  rewrite a3E b3E a4O [if false (+) false then _ else _]/= !add0n in n1P.
  rewrite a3E b3E a4O b4O [if false (+) false then _ else _]/= in n2P. 
  have [/eqP Ea1 /eqP Eb1] : a1 == (a3./2 + a4./2).+1 /\ b1 == b3./2 + b4./2.
    move/allP/(_ false) : (n1P); move/allP/(_ true) : n1P.
    rewrite /= !(count_cat, count_nseq) /= !(count_cat, count_nseq) /=.
    rewrite !mul1n !mul0n !(addn0, add0n) !add1n !(addSn, addnS).
    rewrite !(mem_cat, inE, mem_nseq, eqxx, orbT, orTb, orFb, orbF, 
              andbF, andbT) => Hb1 -> //; split => //.
    by case: (b1) Hb1 => // => [|x]; (do 2 case (_./2) => [|?]) => // ->.
  have [/eqP Ea2 /eqP Eb2] : a2 == a3./2 + a4./2 /\ b2 == (b3./2 + b4./2).+1.
    move/allP/(_ false) : (n2P); move/allP/(_ true) : n2P.
    rewrite /= !(count_cat, count_nseq) /= !(count_cat, count_nseq) /=.
    rewrite !mul1n !mul0n !(addn0, add0n, add1n, addSn, addnS).
    rewrite !(mem_cat, mem_nseq, inE, eqxx, orTb, andTb, andbT, orbT,
               andbF, orFb, orbF) => -> // Hb1; split => //.
    by case: (a2) Hb1 => [|?]//; (do 2 (case: (_./2) => [|?]//)) => ->.
  by move=> {a3E b3E a4O b4O n1P n2P}//; lia.
(* Fourth case *)
rewrite /= in a3E b3E b4E.
rewrite a3E b3E a4E b4E [if false (+) false then _ else _]/= !add0n in n1P.
rewrite a3E b3E a4E b4E [if false (+) false then _ else _]/= in n2P.
have [/eqP Ea1 /eqP Eb1] : a1 == a3./2 + a4./2 /\ b1 == b3./2 + b4./2.
  move/allP/(_ false) : (n1P); move/allP/(_ true) : n1P.
  rewrite /= !(count_cat, count_nseq) /=.
  rewrite !mul1n !mul0n !(addn0, add0n).
  rewrite !(mem_cat, inE, mem_nseq, eqxx, orbT, orTb, orFb, orbF, 
            andbF, andbT) => Hb1 Ha1 //; split.
    by case: (a1) Ha1 => [|x]; (do 2 case (_./2) => [|?]) => // ->.
  by  case: (b1) Hb1 => [|x]; (do 2 case (_./2) => [|?]) => // ->.
have [/eqP Ea2 /eqP Eb2] : a2 == a3./2 + a4./2 /\ b2 == b3./2 + b4./2.
  move/allP/(_ false) : (n2P); move/allP/(_ true) : n2P.
  rewrite /= !(count_cat, count_nseq) /=.
  rewrite !mul1n !mul0n !(addn0, add0n, add1n, addSn, addnS).
  rewrite !(mem_cat, mem_nseq, inE, eqxx, orTb, andTb, andbT, orbT,
            andbF, orFb, orbF) => Hb2 Ha2; split.
    by case: (a2) Ha2 => [|?]//; (do 2 (case: (_./2) => [|?]//)) => ->.
  by case: (b2) Hb2 => [|?]//; (do 2 (case: (_./2) => [|?]//)) => ->.
by move=> {a3E b3E a4E b4E n1P n2P}//; lia.
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

