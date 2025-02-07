(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From mathcomp Require Import all_ssreflect.
Require Import ZArith.

(******************************************************************************)
(* This file contains some fact about addition chains                         *)
(*                                                                            *)
(*  'L(m, n)  = returns the list of coefficient of the continued fraction     *)
(*              for m/n                                                       *)
(*  'K l      = evaluates the continuant on the list l                        *)
(*                                                                            *)
(******************************************************************************)

Definition next (b : bool) (c : nat * nat)  :=
  if b then (c.1, c.1 + c.2) else (c.2, c.1 + c.2).

Definition run b l := foldl (fun l b => next b l) b l.

Definition nextz (b : Z) (c : Z * Z)  :=
  (b * c.1 + (1 - b) * c.2, c.1 + c.2)%Z.

Definition test l := 
  ((run (1,2) (rcons l true)).2 ==
   (run (1,2) (rcons (rev l) true)).2).

Compute test  [::true; false; false].
Compute test  [::true; false; true; false].

Fixpoint get_all n := 
  if n is n1.+1 then 
     let l := get_all n1 in [seq true :: i | i <- l] ++ [seq false :: i | i <- l]
  else [::[::]].

Compute [seq test i | i <- get_all 10].

Fixpoint lfrac_aux k (m n : nat) :=
  if n is 0 then [::] else
  if n is 1 then [:: m] else
  if k is k1.+1 then m %/ n :: lfrac_aux k1 n (m %% n) else [::].

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

(* give the continued fraction coefs of m/n *)
Definition lfrac m n := lfrac_aux m m n.

Notation " `L( m , n ) " := (lfrac m n) (at level 10, format "`L( m ,  n )").

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

Compute lfrac 29 23.


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
  `K (rcons (rcons l x) y) = y * `K (rcons l x) + `K l.
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) => [[]|k IH [|x1[|y1 l]]] // Hl.
- by rewrite /= mulnC.
- by rewrite /= mulnC.
- by rewrite /= !mulnDr !muln1 addnAC mulnA mulnC.
rewrite /= ltnS in Hl.
rewrite [rcons _ _]/= pcont_rec -!rcons_cons !IH //; last by rewrite ltnW.
rewrite !rcons_cons !pcont_rec !mulnDr !addnA !mulnA.
by congr (_ + _); rewrite addnAC [_ * y]mulnC.
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

Compute run (1,2) (rcons [::true; false; false] true).

Compute run (1,2) (rev [::true; false; false]).
