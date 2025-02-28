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
(*  `K s      = evaluates the continuant on the sequence s                    *)
(*                                                                            *)
(*   bs2ns s  = takes a sequence of boolean numbers s and returns a sequence  *)
(*              of natural numbers using false as separator                   *)
(*   ns2bs s  = the converse operation                                        *)
(*                                                                            *)
(*   next b p  = given the boolean b computes one step of the addition chain  *)
(*               on the pair p                                                *)
(*   run p s  =  execute the addition chain given by the sequence of boolean  *)
(*               numbers s starting from the pair p                           *)
(*   frun s  =  execute the addition chain given by the list of booleans l    *)
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
Compute `L(11, 8).

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

Definition all_nz s := all (fun x => x != 0) s.

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
Fixpoint pcont s :=
  if s is x1 :: s1 then 
    if s1 is x2 :: s2 then 
      x1 * pcont s1 + pcont s2
    else x1
  else 1.

Notation "`K s " := (pcont s) (at level 10).

Compute `K (`L(29, 23)).

Lemma pcont_nil : `K [::] = 1.
Proof. by []. Qed.

Lemma pcont_one x : `K [:: x] = x.
Proof. by []. Qed.

Lemma pcont_rec x y s : `K [:: x, y & s] = x * `K (y :: s) + `K s.
Proof. by []. Qed.

Lemma pcont_rcons x y s : 
  `K (rcons (rcons s y) x) = x * `K (rcons s y) + `K s.
Proof.
elim: {s}(size s) {-2}s (leqnn (size s)) => [[]|k IH [|x1[|y1 s]]] // Hl.
- by rewrite /= mulnC.
- by rewrite /= mulnC.
- by rewrite /= !mulnDr !muln1 addnAC mulnA mulnC.
rewrite /= ltnS in Hl.
rewrite [rcons _ _]/= pcont_rec -!rcons_cons !IH //; last by rewrite ltnW.
rewrite !rcons_cons !pcont_rec !mulnDr !addnA !mulnA.
by congr (_ + _); rewrite addnAC [_ * x]mulnC.
Qed.

Lemma pcont_rev s : `K (rev s) = `K s. 
Proof.
elim: {s}(size s) {-2}s (leqnn (size s)) => [[]|k IH [|x1[|y1 s]]] // Hl.
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

Lemma pcontD x y s : `K  (x + y :: s) = `K(x :: s) + y * `K s.
Proof.
case: s => [|z s]; first by rewrite !pcont_one pcont_nil muln1.
by rewrite !pcont_rec addnAC -mulnDl.
Qed.

(* Conversions between list of booleans and list of nat *)

Fixpoint ns2bs s := 
  if s is n :: s1 then 
    if s1 is _ :: _ then nseq n.-1 true ++ false :: ns2bs s1 
    else nseq n.-1 true
  else [::].

Fixpoint bs2ns_aux n s :=
  if s is b :: s1 then
    if b then bs2ns_aux n.+1 s1 else n.+1 :: bs2ns_aux 0 s1 
  else [::n.+1].

Definition bs2ns s := bs2ns_aux 0 s.

Compute ns2bs [::1; 1].
Compute bs2ns [::false].
Compute ns2bs [::2;1;3].
Compute bs2ns [:: true;  false;  false; true;  true] .
Compute bs2ns (rev [:: true;  false;  false; true;  true]).

Compute ns2bs [::1; 2; 3].
Compute rev (ns2bs (rev [::1; 2; 3])).
Compute bs2ns (rev ([:: false;  true;  false;  true;  true] )).

Lemma ns2bs_cons a s :
  ns2bs (a :: s) = 
    if s is _ :: _ then nseq a.-1 true ++ false :: ns2bs s 
    else nseq a.-1 true.
Proof. by []. Qed.

Lemma all_nz_bl2nz s : all_nz (bs2ns s).
Proof. by rewrite /bs2ns; elim: s 0 => // [] [] /=. Qed.


Lemma bs2nsK s : ns2bs (bs2ns s) = s.
Proof.
case: (s =P [::]) => [->//|/eqP s_neq0].
suff H m : ns2bs (bs2ns_aux m s) = nseq m true ++ s by apply H.
elim: s m s_neq0 => //= [] [] [|b s] // IH m _.
- by rewrite /= -(nseqD _ 1) addn1.
- by rewrite IH // -addn1 nseqD /= -catA.
rewrite ns2bs_cons.
by case: bs2ns_aux (IH 0 isT) => // ? ? ->.
Qed.

Lemma nseqS_rcons (A : Type) k (v : A) : nseq k.+1 v = rcons (nseq k v) v.
Proof. by elim: k => //= k ->. Qed.

Compute bs2ns [::true; false; false].

Lemma bs2ns_nseq n : bs2ns (nseq n true) = [:: n.+1].
Proof.
suff: forall m, bs2ns_aux m (nseq n true) = [:: m + n.+1] by apply.
elim: n => [m|n IH m] /=; first by rewrite addn1.
by rewrite IH !addnS.
Qed.

Lemma bs2ns_nseq_false n s : 
  bs2ns (nseq n true ++ false :: s) = n.+1 :: bs2ns s.
Proof.
suff: forall m, 
  bs2ns_aux m (nseq n true ++ (false :: s)) = m + n.+1 :: bs2ns s by apply.
elim: n => [m|n IH m] /=; first by rewrite addn1.
by rewrite IH !addnS.
Qed.

Lemma bs2ns_false_nseq n s : 
  bs2ns (s ++ false :: nseq n true) = rcons (bs2ns s) n.+1.
Proof.
rewrite /bs2ns; elim: s 0 => [k | [] s IH k] //=.
  by rewrite [bs2ns_aux _ _]bs2ns_nseq.
by rewrite IH.
Qed.

Lemma bnseqE s : 
  {n | s = nseq n true} + {ns | s = nseq ns.1 true ++ false :: ns.2}.
Proof.
elim: s => /= [|[] s [[n ->]|[[n s1] ->]]] ; first by left; exists 0.
- by left; exists n.+1.
- by right; exists (n.+1, s1).
- by right; exists (0, nseq n true).
by right; exists (0, nseq n true ++ false :: s1).
Qed.

Lemma bnseq_ind P s : 
  (forall n, P (nseq n true)) -> 
  (forall n s, P s -> P (nseq n true ++ false :: s)) 
   -> P s.
Proof.
elim: {s}size {-2}s (leqnn (size s)) => [[] _ H _ //=|k IH s sL IH1 IH2].
  by apply: (H 0).
have [[n sE]|[[n s1] sE]] := bnseqE s; first by rewrite sE; apply: IH1.
rewrite sE; apply/IH2/IH => //.
rewrite -ltnS (leq_trans _ sL) // sE /= size_cat size_nseq /=.
by rewrite addnS ltnS leq_addl.
Qed.

Lemma  bnseqrE s : 
  {n | s = nseq n true} + {ns | s = ns.2  ++ false :: (nseq ns.1 true)}.
Proof.
elim: s => /= [|[] s [[n ->]|[[n s1] ->]]]; first by left; exists 0.
- by left; exists n.+1.
- by right; exists (n, true :: s1).
- by right; exists (n, [::]).
by right; exists (n, false :: s1).
Qed.

Lemma  bnseqr_ind P s : 
  (forall n, P (nseq n true)) -> 
  (forall n s, P s -> P (s ++ false :: nseq n true))
   -> P s.
Proof.
elim: {s}size {-2}s (leqnn (size s)) => [[] _ H _ //=|k IH s sL IH1 IH2].
  by apply: (H 0).
have [[n sE]|[[n s1] sE]] := bnseqrE s; first by rewrite sE; apply: IH1.
rewrite sE; apply/IH2/IH => //.
rewrite -ltnS (leq_trans _ sL) // -ltnS -(size_rcons s true) sE.
by rewrite size_rcons size_cat /= size_nseq !addnS !ltnS leq_addr.
Qed.

Lemma rev_bs2ns s : rev (bs2ns s) = bs2ns (rev s).
Proof.
elim/bnseq_ind : s => [n| n s IH]; first by rewrite rev_nseq bs2ns_nseq.
rewrite bs2ns_nseq_false rev_cat rev_nseq !rev_cons cat_rcons bs2ns_false_nseq.
by rewrite IH.
Qed.

Lemma ns2bsK s : s != [::] -> all_nz s -> bs2ns (ns2bs s) = s.
Proof.
elim: s => //= []  [//|a] [|b s] IH _ /andP[_ nzl]; first by rewrite bs2ns_nseq.
by rewrite bs2ns_nseq_false IH.
Qed.

(* Start with addition chains *)

Definition next (b : bool) (p : nat * nat)  :=
  let: (m, n) := p in if b then (m, m + n) else (n, m + n).

Definition run (p : nat * nat) (s : seq bool) := 
  foldl (fun p b => next b p) p s.

Definition frun s := let: (m, n) := run (1, 2) s in m + n.

Compute next true (1, 2).
Compute next false (1, 2).

Compute run (1,2) ([::true; false; false]).
Compute run (1,2) (rev [::true; false; false]).

Compute frun ([::true; false; false]).
Compute frun (rev [::true; false; false]).

Lemma run_cat p s1 s2 : run p (s1 ++ s2) = run (run p s1) s2.
Proof. by exact: foldl_cat. Qed.

Lemma run_gcdn m n s : gcdn (run (m, n) s).1 (run (m, n) s).2 = gcdn m n.
Proof.
by elim: s m n => //= [] [] s IH m n /=; rewrite IH ?gcdnDr ?gcdnDl // gcdnC.
Qed.

Lemma run_rcons p b s : run p (rcons s b) = next b (run p s).
Proof. by elim: s p b => /=. Qed.

Lemma run_nseq k p : run p (nseq k true) = (p.1, p.2 + k * p.1).
Proof.
elim: k p => [[m n]|k IH [m n]] /=; first by rewrite addn0.
by rewrite IH  /= mulSn addnCA addnA.
Qed.

Lemma frunE s : frun s = (run (1, 2) (rcons s true)).2.
Proof.
suff H p : (let '(x, y) := run p s in x + y) = (run p (rcons s true)).2.
  by apply: H.
by elim: s p => //=; case.
Qed.

Lemma run_lt m n s : 
  0 < n < m -> let: (m1, n1) := run (n, m) s in 0 < m1 < n1.
Proof.
elim: s n m => //= [] [] s IH n m /andP[n_pos nLm] /=; apply: IH.
  by rewrite n_pos (leq_trans _ (leq_addl _ _)).
by rewrite (leq_trans _ nLm) // -{1}(add0n m) ltn_add2r.
Qed.

Lemma frac_run_bs2ns s : 
  let: (m, n) := run (1, 2) s in `L(n, m) = rev (bs2ns (true :: s)).
Proof.
elim/bnseqr_ind : s => /= [k |b s].
  by rewrite (bs2ns_nseq k.+1) run_nseq lfrac_n1 /= muln1 add2n.
rewrite run_cat.
case: run (run_lt _ _ s (isT : 0 < 1 < 2)) => m n /andP[n_pos nLm] IH.
rewrite -cat_cons bs2ns_false_nseq rev_rcons -IH /=.
rewrite run_nseq /= lfrac_rec; last first.
  by rewrite (leq_trans _ nLm) //= (leq_trans _ (leq_addr _ _)) // leq_addl.
rewrite -addnA mulnC -mulnS divnDr; last by rewrite dvdn_mulr.
rewrite divn_small // mulKn; last by rewrite (leq_trans _ nLm).
by rewrite add0n addnC mulnC modnMDl modn_small.
Qed.

Lemma frun_rev s : frun (rev s) = frun s.
Proof.
rewrite !frunE.
case Hr : run (run_gcdn 1 2 (rcons s true)) (frac_run_bs2ns (rcons s true)) => 
   /= [m n] Hc Hf.
rewrite (lfrac_cont_gcdl n m); last first.
  by have := run_lt 2 1 (rcons s true) isT; rewrite Hr; case/andP => _ /ltnW.
rewrite gcdnC Hc muln1 -pcont_rev Hf revK.
case Hr1: run (run_gcdn 1 2 (rcons (rev s) true)) 
         (frac_run_bs2ns (rcons (rev s) true)) => /= [m1 n1] Hc1 Hf1.
rewrite (lfrac_cont_gcdl n1 m1); last first.
  by have := run_lt 2 1 (rcons (rev s) true) isT; rewrite Hr1; 
     case/andP => _ /ltnW.
by rewrite gcdnC Hc1 muln1 Hf1 /= rev_bs2ns rev_cons rev_rcons revK.
Qed.
