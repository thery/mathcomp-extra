(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From mathcomp Require Import all_ssreflect.
Require Import ZArith.


(******************************************************************************)
(* This file contains some facts about addition chains. It is inspired by     *)
(* Pascal's Veron HDR :                                                       *)
(*        Contributions en arithmétique modulaire pour la cryptographie       *)
(* The particular result we were aiming at is frun_rev                        *)
(*                                                                            *)
(*  `L(m, n)  = returns the list of coefficients of the continued fraction    *)
(*              for m/n                                                       *)
(*  `K l      = evaluates the continuant on the list l                        *)
(*                                                                            *)
(*   bl2nl l  = takes a list of boolean l and returns a list on numbers       *)
(*   nl2bl l  = the converse operations                                       *)
(*                                                                            *)
(*   next b p  = given the boolean b computes one step of the addition chain  *)
(*               on the pair p                                                *)
(*   run p l  =  execute the addition chain given by the list of booleans l   *)
(*               starting from the pair p                                     *)
(*   frun p  =  execute the addition chain given by the list of booleans l    *)
(*               starting from (1,2) returning a number that is the sum of    *)
(*               the element of the resulting pair                            *)
(*                                                                            *)
(******************************************************************************)

(* Compute the list of coefficients of the continued fraciton of a rational   *)

Fixpoint lfrac_aux k (m n : nat) :=
  if n is 0 then [::] else
  if n is 1 then [:: m] else
  if k is k1.+1 then m %/ n :: lfrac_aux k1 n (m %% n) else [::].

Definition lfrac m n := lfrac_aux m m n.

Notation " `L( m , n ) " := (lfrac m n) (at level 10, format "`L( m ,  n )").

Compute `L(29, 23).
Compute `L(8, 3).

Fact lfrac_aux_n0 k m : lfrac_aux k m 0 = [::].
Proof. by case: k. Qed.

Fact lfrac_aux_n1 k m : lfrac_aux k m 1 = [:: m].
Proof. by case: k. Qed.

Fact lfrac_aux_eq k m n : n <= m <= k -> lfrac_aux k m n = lfrac_aux m m n.
Proof.
elim: k {-2}k (leqnn k) m n => [|k1 IH].
  by case => // _  [] //= ? ?; rewrite leqn0 andbF.
case => [|k] kLk1 m n nLm; first by case: m nLm => // ?; rewrite leqn0 andbF.
case: m nLm => [|m /=]; first by case: n.
case: n => // [] [//|n]; rewrite !ltnS => /andP[nLm mLk].
move: nLm; rewrite leq_eqVlt => /orP[/eqP<-|nLm].
  by rewrite modnn !lfrac_aux_n0.
rewrite !IH //; first by rewrite (leq_trans mLk).  
  by rewrite ltnW // ltn_mod.
by rewrite ltnW // ?ltn_mod //= (leq_trans nLm).
Qed.

Lemma lfrac_n0 m : `L(m, 0) = [::].
Proof. by exact: lfrac_aux_n0. Qed.

Lemma lfrac_n1 m : `L(m, 1) = [:: m].
Proof. by exact: lfrac_aux_n1. Qed.

Lemma lfrac_rec m n : 1 < n <= m -> `L(m, n) = (m %/ n) :: `L(n, m %% n).
Proof.
case: m => [|m] nLm //=; first by case: n nLm => //= [] [].
rewrite /lfrac /=.
case: n nLm => [|[|n]] //; rewrite !ltnS => /andP[_ nLm].
rewrite leq_eqVlt in nLm; case/orP: nLm => [/eqP ->|nLm].
  by rewrite modnn !lfrac_aux_n0.
by rewrite lfrac_aux_eq // ltnW // ltn_mod.
Qed.

Definition all_nz l := all (fun x => x != 0) l.

Lemma nz_frac m n : 0 < n <= m -> all_nz (`L(m, n)).
Proof.
elim: m {-2}m (leqnn m) n => [|k IH m mLk n]; first by case => //  _ [].
rewrite leq_eqVlt => /andP[] /orP[/eqP<-|n_pos nLm].
  by rewrite lfrac_n1; case: (m).
rewrite lfrac_rec /=; last by rewrite n_pos.
rewrite -lt0n divn_gt0; last by rewrite ltnW.
move: nLm; rewrite leq_eqVlt => /orP[/eqP->|nLm].
  by rewrite eqxx modnn lfrac_n0.
rewrite nLm orbT /=; case: (m %% n =P 0) => [->|]; first by rewrite lfrac_n0.
move/eqP; rewrite -lt0n => mMn_pos.
rewrite IH //.
  by rewrite -ltnS (leq_trans nLm).
by rewrite mMn_pos ltnW // ltn_mod ltnW.
Qed.

(* Continuants *)
Fixpoint pcont l :=
  if l is x1 :: l1 then 
    if l1 is x2 :: l2 then 
      x1 * pcont l1 + pcont l2
    else x1
  else 1.

Notation "`K l " := (pcont l) (at level 10).

Compute `K (`L(29, 23)).

Lemma pcont_nil : `K [::] = 1.
Proof. by []. Qed.

Lemma pcont_one x : `K [:: x] = x.
Proof. by []. Qed.

Lemma pcont_rec x y l : `K [:: x, y & l] = x * `K (y :: l) + `K l.
Proof. by []. Qed.

Lemma pcont_rcons x y l : 
  `K (rcons (rcons l y) x) = x * `K (rcons l y) + `K l.
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) => [[]|k IH [|x1[|y1 l]]] // Hl.
- by rewrite /= mulnC.
- by rewrite /= mulnC.
- by rewrite /= !mulnDr !muln1 addnAC mulnA mulnC.
rewrite /= ltnS in Hl.
rewrite [rcons _ _]/= pcont_rec -!rcons_cons !IH //; last by rewrite ltnW.
rewrite !rcons_cons !pcont_rec !mulnDr !addnA !mulnA.
by congr (_ + _); rewrite addnAC [_ * x]mulnC.
Qed.

Lemma pcont_rev l : `K (rev l) = `K l. 
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) => [[]|k IH [|x1[|y1 l]]] // Hl.
rewrite /= ltnS in Hl.
by rewrite !rev_cons pcont_rcons -rev_cons !IH // ltnW.
Qed.

Lemma lfrac_cont_gcdl m n : n <= m -> m = `K (`L(m,  n)) * gcdn m n.
Proof.
have := leq0n n; rewrite leq_eqVlt; case/orP=>[/eqP <-|n_pos].
  by rewrite lfrac_n0 pcont_nil mul1n gcdn0.
elim: m {-2}m (leqnn m) n n_pos => [|k IH m mLk n n_pos nLm].
  by case => [_|m]; [case | rewrite ltn0].
rewrite leq_eqVlt in n_pos; case/orP : n_pos => [/eqP<-|n_pos1].
  by rewrite lfrac_n1 pcont_one gcdn1 muln1.
have := leq0n (m %% n); rewrite leq_eqVlt; case/orP=>[/eqP mMnE|mMn_pos].
rewrite lfrac_rec; last by rewrite n_pos1.
  rewrite -mMnE lfrac_n0 pcont_one.
  by rewrite {1 3}(divn_eq m n) -mMnE addn0 gcdnC gcdnMl.
rewrite -gcdn_modl.
move: nLm; rewrite leq_eqVlt; case/orP=>[/eqP nEm|nLm].
  rewrite nEm lfrac_rec //; last by rewrite -nEm n_pos1 leqnn.
  by rewrite modnn lfrac_n0 divnn -nEm ltnW // gcd0n pcont_one mul1n.
rewrite lfrac_rec ?n_pos1 1?ltnW //.
move: mMn_pos; rewrite leq_eqVlt; case/orP=>[/eqP mMnE|mMn_pos].
  by rewrite -mMnE lfrac_n1 gcd1n muln1 pcont_rec pcont_one 
             pcont_nil mMnE -divn_eq.
rewrite lfrac_rec; last by rewrite mMn_pos /= ltnW // ltn_mod // ltnW.
rewrite pcont_rec -lfrac_rec; last by rewrite mMn_pos ltnW // ltn_mod ltnW.
rewrite mulnDl -mulnA gcdnC -IH; last 3 first.
- by rewrite -ltnS (leq_trans nLm).
- by rewrite ltnW.
- by rewrite ltnW // ltn_mod ltnW.
have := leq0n (n %% (m %% n));
   rewrite leq_eqVlt; case/orP=>[/eqP nMmMnE|nMmMn_pos].
  by rewrite -nMmMnE lfrac_n0 pcont_nil mul1n -gcdn_modl -nMmMnE gcd0n -divn_eq.
rewrite -gcdn_modl gcdnC -IH //; last 2 first.
- by rewrite -ltnS (leq_trans _ mLk) // (ltn_trans _ nLm) // ltn_mod ltnW.
- by rewrite ltnW // ltn_mod ltnW.
by rewrite -divn_eq.
Qed.

Lemma lfrac_cont_gcdr m n :
  0 < n <= m -> n = `K (behead (lfrac m n)) * gcdn m n.
Proof.
move=> /andP[]; rewrite leq_eqVlt => /orP[/eqP<-|n_pos1 nLm].
  by rewrite gcdn1 lfrac_n1 pcont_nil.
rewrite lfrac_rec ?n_pos1 // -gcdn_modl gcdnC -lfrac_cont_gcdl //.
by rewrite ltnW // ltn_mod ltnW.
Qed.

Lemma pcontD x y l : `K  (x + y :: l) = `K(x :: l) + y * `K l.
Proof.
case: l => [|z l]; first by rewrite !pcont_one pcont_nil muln1.
by rewrite !pcont_rec addnAC -mulnDl.
Qed.

(* Conversions between list of booleans and list of nat *)

Fixpoint nl2bl nl := 
  if nl is n :: nl1 then 
    if nl1 is _ :: _ then nseq n.-1 true ++ false :: nl2bl nl1 
    else nseq n.-1 true
  else [::].

Fixpoint bl2nl_aux n bl :=
  if bl is b :: bl1 then
    if b then bl2nl_aux n.+1 bl1 else n.+1 :: bl2nl_aux 0 bl1 
  else [::n.+1].

Definition bl2nl l := bl2nl_aux 0 l.

Compute nl2bl [::1; 1].
Compute bl2nl [::false].
Compute nl2bl [::2;1;3].
Compute bl2nl [:: true;  false;  false; true;  true] .
Compute bl2nl (rev [:: true;  false;  false; true;  true]).

Compute nl2bl [::1; 2; 3].
Compute rev (nl2bl (rev [::1; 2; 3])).
Compute bl2nl (rev ([:: false;  true;  false;  true;  true] )).

Lemma nl2bl_cons a l :
  nl2bl (a :: l) = 
    if l is _ :: _ then nseq a.-1 true ++ false :: nl2bl l 
    else nseq a.-1 true.
Proof. by []. Qed.

Lemma all_nz_bl2nz l : all_nz (bl2nl l).
Proof. by rewrite /bl2nl; elim: l 0 => // [] [] /=. Qed.


Lemma bl2nlK l : nl2bl (bl2nl l) = l.
Proof.
case: (l =P [::]) => [->//|/eqP l_neq0].
suff H m : nl2bl (bl2nl_aux m l) = nseq m true ++ l .
  by apply H.
elim: l m l_neq0 => //= [] [] [|b l] // IH m _.
- by rewrite /= -(nseqD _ 1) addn1.
- by rewrite IH // -addn1 nseqD /= -catA.
rewrite nl2bl_cons.
by case: bl2nl_aux (IH 0 isT) => // ? ? ->.
Qed.

Lemma nseqS_rcons (A : Type) k (v : A) : nseq k.+1 v = rcons (nseq k v) v.
Proof. by elim: k => //= k ->. Qed.

Lemma bl2nl_nseq n : bl2nl (nseq n true) = [:: n.+1].
Proof.
suff: forall m, bl2nl_aux m (nseq n true) = [:: m + n.+1] by apply.
elim: n => [m|n IH m] /=; first by rewrite addn1.
by rewrite IH !addnS.
Qed.

Lemma bl2nl_nseq_false n l : 
  bl2nl (nseq n true ++ (false :: l)) = n.+1 :: bl2nl l.
Proof.
suff: forall m, 
  bl2nl_aux m (nseq n true ++ (false :: l)) = m + n.+1 :: bl2nl l by apply.
elim: n => [m|n IH m] /=; first by rewrite addn1.
by rewrite IH !addnS.
Qed.

Lemma bl2nl_false_nseq n l : 
  bl2nl (l ++ false :: nseq n true) = rcons (bl2nl l) n.+1.
Proof.
rewrite /bl2nl; elim: l 0 => [k | [] l IH k] //=.
  by rewrite [bl2nl_aux _ _]bl2nl_nseq.
by rewrite IH.
Qed.

Lemma bnseqE l : 
  {n | l = nseq n true} + {nl | l = nseq nl.1 true ++ false :: nl.2}.
Proof.
elim: l => /= [|[] l [[n ->]|[[n l1] ->]]] ; first by left; exists 0.
- by left; exists n.+1.
- by right; exists (n.+1, l1).
- by right; exists (0, nseq n true).
by right; exists (0, nseq n true ++ false :: l1).
Qed.

Lemma bnseq_ind P l : 
  (forall n, P (nseq n true)) -> 
  (forall n l, P l -> P (nseq n true ++ false :: l)) 
   -> P l.
Proof.
elim: {l}size {-2}l (leqnn (size l)) => [[] _ H _ //=|k IH l sL IH1 IH2].
  by apply: (H 0).
have [[n lE]|[[n l1] lE]] := bnseqE l; first by rewrite lE; apply: IH1.
rewrite lE; apply/IH2/IH => //.
rewrite -ltnS (leq_trans _ sL) // lE /= size_cat size_nseq /=.
by rewrite addnS ltnS leq_addl.
Qed.

Lemma  bnseqrE l : 
  {n | l = nseq n true} + {nl | l = nl.2  ++ false :: (nseq nl.1 true)}.
Proof.
elim: l => /= [|[] l [[n ->]|[[n l1] ->]]]; first by left; exists 0.
- by left; exists n.+1.
- by right; exists (n, true :: l1).
- by right; exists (n, [::]).
by right; exists (n, false :: l1).
Qed.

Lemma  bnseqr_ind P l : 
  (forall n, P (nseq n true)) -> 
  (forall n l, P l -> P (l ++ false :: nseq n true))
   -> P l.
Proof.
elim: {l}size {-2}l (leqnn (size l)) => [[] _ H _ //=|k IH l sL IH1 IH2].
  by apply: (H 0).
have [[n lE]|[[n l1] lE]] := bnseqrE l; first by rewrite lE; apply: IH1.
rewrite lE; apply/IH2/IH => //.
rewrite -ltnS (leq_trans _ sL) // -ltnS -(size_rcons l true) lE.
by rewrite size_rcons size_cat /= size_nseq !addnS !ltnS leq_addr.
Qed.


Lemma rev_bl2nl bl : rev (bl2nl bl) = bl2nl (rev bl).
Proof.
elim/bnseq_ind : bl => [n| n l IH]; first by rewrite rev_nseq bl2nl_nseq.
rewrite bl2nl_nseq_false rev_cat rev_nseq !rev_cons cat_rcons bl2nl_false_nseq.
by rewrite IH.
Qed.

Lemma nl2blK l : l != [::] -> all_nz l -> bl2nl (nl2bl l) = l.
Proof.
elim: l => //= []  [//|a] [|b l] IH _ /andP[_ nzl]; first by rewrite bl2nl_nseq.
by rewrite bl2nl_nseq_false IH.
Qed.

(* Start with addition chains *)

Definition next (b : bool) (p : nat * nat)  :=
  let: (m, n) := p in if b then (m, m + n) else (n, m + n).

Definition run (p : nat * nat) (l : seq bool) := 
  foldl (fun l b => next b l) p l.

Definition frun l := let: (m, n) := run (1, 2) l in m + n.

Compute next true (1, 2).
Compute next false (1, 2).

Compute run (1,2) ([::true; false; false]).
Compute run (1,2) (rev [::true; false; false]).

Compute frun ([::true; false; false]).
Compute frun (rev [::true; false; false]).

Lemma run_cat p l1 l2 : run p (l1 ++ l2) = run (run p l1) l2.
Proof. by exact: foldl_cat. Qed.

Lemma run_gcdn m n l : gcdn (run (m, n) l).1 (run (m, n) l).2 = gcdn m n.
Proof.
by elim: l m n => //= [] [] l IH m n /=; rewrite IH ?gcdnDr ?gcdnDl // gcdnC.
Qed.

Lemma run_rcons p b l : run p (rcons l b) = next b (run p l).
Proof. by elim: l p b => /=. Qed.

Lemma run_nseq k p : run p (nseq k true) = (p.1, p.2 + k * p.1).
Proof.
elim: k p => [[m n]|k IH [m n]] /=; first by rewrite addn0.
by rewrite IH  /= mulSn addnCA addnA.
Qed.

Lemma frunE l : frun l = (run (1, 2) (rcons l true)).2.
Proof.
suff H p : (let '(x, y) := run p l in x + y) = (run p (rcons l true)).2.
  by apply: H.
by elim: l p => //=; case.
Qed.


Lemma run_lt m n bl : 
  0 < n < m -> let: (m1, n1) := run (n, m) bl in 0 < m1 < n1.
Proof.
elim: bl n m => //= [] [] l IH n m /andP[n_pos nLm] /=; apply: IH.
  by rewrite n_pos (leq_trans _ (leq_addl _ _)).
by rewrite (leq_trans _ nLm) // -{1}(add0n m) ltn_add2r.
Qed.

Lemma frac_run_bl2nl bl : 
  let: (m, n) := run (1, 2) bl in `L(n, m) = bl2nl (rev (true :: bl)).
Proof.
elim/bnseqr_ind : bl => /= [k |b bl].
  rewrite run_nseq rev_cons rev_nseq -nseqS_rcons bl2nl_nseq /=.
  by rewrite muln1 add2n /= lfrac_n1.
rewrite run_cat.
case: run (run_lt _ _ bl (isT : 0 < 1 < 2)) => m n /andP[n_pos nLm] IH.
rewrite rev_cons rev_cat rev_cons rev_nseq rcons_cat cat_rcons.
rewrite bl2nl_nseq_false -rev_cons -IH.
rewrite /= run_nseq /= lfrac_rec; last first.
  by rewrite (leq_trans _ nLm) //= (leq_trans _ (leq_addr _ _)) // leq_addl.
rewrite -addnA mulnC -mulnS divnDr; last by rewrite dvdn_mulr.
rewrite divn_small // mulKn; last by rewrite (leq_trans _ nLm).
by rewrite add0n addnC mulnC modnMDl modn_small.
Qed.

Lemma frun_rev l : frun (rev l) = frun l.
Proof.
rewrite !frunE.
case Hr : run (run_gcdn 1 2 (rcons l true)) (frac_run_bl2nl (rcons l true)) => 
   /= [m n] Hc Hf.
rewrite (lfrac_cont_gcdl n m); last first.
  by have := run_lt 2 1 (rcons l true) isT; rewrite Hr; case/andP => _ /ltnW.
rewrite gcdnC Hc muln1 -pcont_rev Hf rev_bl2nl revK.
case Hr1: run (run_gcdn 1 2 (rcons (rev l) true)) 
         (frac_run_bl2nl (rcons (rev l) true)) => /= [m1 n1] Hc1 Hf1.
rewrite (lfrac_cont_gcdl n1 m1); last first.
  by have := run_lt 2 1 (rcons (rev l) true) isT; rewrite Hr1; 
     case/andP => _ /ltnW.
by rewrite gcdnC Hc1 muln1 Hf1 rev_cons rev_rcons /= revK.
Qed.
