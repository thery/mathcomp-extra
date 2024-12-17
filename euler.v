(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
From mathcomp Require Import all_ssreflect all_algebra.

(******************************************************************************)
(* This files contains a proof of Euler Criterion                             *)
(*    res_quad p a == a is a residue quadratic of n                           *)
(*                                                                            *)
(* Thanks to Bruno Rafael                                                     *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect all_algebra.

Lemma modn_prodm I r (P : pred I) F d :
  \prod_(i <- r | P i) (F i %% d) = \prod_(i <- r | P i) F i %[mod d].
Proof.
apply/eqP; elim/big_rec2: _ => // i m n _ /eqP nEm.
by rewrite modnMml -modnMmr nEm modnMmr.
Qed.

Definition res_quad p a := has (fun i => i * i == a %[mod p]) (iota 0 p).

Compute res_quad 7 4.

Lemma res_quadP a p : 
  reflect (exists i : 'I_p, i * i = a %[mod p]) (res_quad p a).
Proof. 
apply: (iffP hasP) => [[x /[!mem_iota] [/andP[_ xLp] /eqP xxE]]|[x xxE]].
  by exists (Ordinal xLp).
by exists (val x); [rewrite mem_iota /= | apply/eqP].
Qed.

Lemma res_quadPn a p : 
  reflect (forall i : 'I_p, i * i != a %[mod p]) (~~ (res_quad p a)).
Proof.
apply: (iffP hasPn) => [xxE i| xxE i /[!mem_iota] /= iI].
  by apply: xxE; rewrite mem_iota /=.
by apply: (xxE (Ordinal iI)).
Qed.

Lemma res_qua0d a : ~~ res_quad 0 a.
Proof. by []. Qed.

Lemma res_qua1d a : res_quad 1 a.
Proof. by rewrite /res_quad /= !modn1. Qed.

Lemma res_quad0 p : 0 < p -> res_quad p 0.
Proof. by case: p. Qed.

Lemma res_quad1 p : 0 < p -> res_quad p 1.
Proof. by case: p => // [] [|p]. Qed.

Lemma res_quad_mod a p : res_quad p (a %% p) = res_quad p a.
Proof. by rewrite /res_quad modn_mod. Qed.

Lemma res_quad_div a p : 0 < p -> p %| a -> res_quad p a.
Proof.
by move=> p_gt0; case/dvdnP => k ->; rewrite -res_quad_mod modnMl res_quad0.
Qed. 

Lemma fact_sqr_exp a p :
   prime p -> ~~ res_quad p a -> (p.-1`!) = a ^ p.-1./2 %[mod p].
Proof.
move=> pP aR.
have p_gt0 : 0 < p by apply: prime_gt0.
have pNDa : ~~ (p %| a).
  by apply/negP => pDa; case/negP : aR; apply: res_quad_div.
have -> : p.-1`! = \prod_(i in 'F_p | i != 0%R) i.
  apply: etrans (_ : \prod_(i in 'F_p | i != 0 :> nat) i = _); last first.
    by apply: eq_bigl => i.
  rewrite /= Fp_cast //.
  rewrite fact_prod big_add1 /= big_mkord.
  case: p {p_gt0 pNDa aR}pP => //= p pP.
  by rewrite [RHS]big_mkcond /= big_ord_recl /= mul1n.
pose a' : 'F_p := inZp a.
have a'E : a' = a %% p :> nat by rewrite /= Fp_cast.
have a'_neq0 : a' != 0%R.
  apply/eqP/val_eqP; rewrite [val a']a'E /=.
  by have /negPf := pNDa; rewrite /dvdn => ->.
rewrite -modnXm -a'E.
pose f (i : 'F_p) : 'F_p := (a' / i)%R.
have f_eq0 : f 0%R = 0%R by rewrite /f GRing.invr0 GRing.mulr0.
have fM (i : 'F_p) : i != ord0 -> (f i * i = a')%R.
  by move=> i_neq0; rewrite /f GRing.divfK.
have fI (i : 'F_p) : f (f i) = i.
  by rewrite /f GRing.invf_div GRing.mulrC GRing.divfK.
have fI_neq0 (i : 'F_p) : i != 0%R -> f i != i.
  move=> i_neq0; apply/eqP => fiE.
  have iL : i < p by rewrite -[X in _ < X]Fp_cast.
  have /res_quadPn/(_ (Ordinal iL)) /= := aR.
  have /val_eqP := fM _ i_neq0; rewrite fiE /=.
  rewrite ![X in _ %% X]Fp_cast //= => /eqP->.
  by rewrite Fp_cast // eqxx.
have fB : {on [pred i |  i != ord0],  bijective f}.
  by exists f => j _; apply: fI.
pose can (i : 'F_p) :=  if i < (f i) then i else f i.
have -> : \prod_(i in 'F_p | i != 0%R) i =
  \prod_(j in 'F_p | (j < f j))
    \prod_(i in 'F_p | (i != 0%R) && (can i == j)) i.
  apply: partition_big => i /andP[iF i_neq0].
  rewrite andTb /can; case: (leqP (S i) _) => //.
  rewrite fI ltnS leq_eqVlt.
  by have /eqP/val_eqP/negPf/=-> := fI_neq0 _ i_neq0.
apply: etrans (_ : \prod_(j in 'F_p | j < f j) (j * f j) = _ %[mod p]).
  congr (_ %% _); apply: eq_bigr => j /andP[jF jLfj].
  rewrite (bigD1 j); last first.
    rewrite jF /can jLfj eqxx andTb andbT.
    by apply/eqP=> j_eq0; rewrite j_eq0 f_eq0 ltnn in jLfj.
  rewrite (bigD1 (f j)); last first.
    rewrite inE /can ifN.
      rewrite fI eqxx.
      case: (f j =P 0%R) => [fj_eq0|].
        by rewrite fj_eq0 -[j]fI fj_eq0 f_eq0 ltnn in jLfj.
      by case: eqP => [fj_eqj|//]; rewrite fj_eqj ltnn in jLfj.
    by rewrite fI -leqNgt ltnW.
  rewrite big1 /= ?muln1 // => i.
  rewrite /can; case: leqP; last by case: (i =P j); rewrite andbF.
  case: (f i =P j); rewrite ?andbF // => <-.
  by rewrite fI eqxx andbF.
apply: etrans (_ : \prod_(j in 'F_p | j < f j) a' = _ %[mod p]).
  rewrite -modn_prodm; congr (_ %% _); apply: eq_bigr => i /andP[_ iLfi].
  have i_neq0 : i != 0%R.
    by apply/eqP=> i_eq0; rewrite i_eq0 f_eq0 ltnn in iLfi.
  rewrite -(fM i i_neq0) mulnC.
  by congr (_ %% _); rewrite Fp_cast.
congr (_ %% _).
rewrite prod_nat_const.
congr (_ ^  _)%nat.
rewrite -[p in RHS](card_Fp pP).
rewrite [in RHS](cardD1 0%R) inE add1n -pred_Sn.
set A := [predD1 'F_p & 0%R].
pose B := [pred i |  (i : 'F_p) < f i].
rewrite -(cardID B A).
have <- : #|image f [predI A & B]| = #|[predD A & B]|.
  apply: eq_card => i; rewrite !inE.
  rewrite -[in LHS](fI i) mem_map; last first.
    by move=> i1 j1 fiEfj; rewrite -[i1]fI fiEfj fI.
  have -> : (f i  \in enum [predI A & B])  = ([predI A & B] (f i)).
    have F (U : finType) (p1 : pred U) (x : U) : x \in enum p1 = p1 x.
      by rewrite mem_enum .
    by rewrite F.
  rewrite [LHS]/= !inE fI.
  case: (i =P 0%R) => [->|]; first by rewrite f_eq0.
  case: (f i =P 0%R) => [fi0|/eqP fi_neq0 /eqP i_neq0].
    by case; rewrite -(fI i) fi0 f_eq0.
  case: ltngtP => // /eqP/val_eqP fiEi.
  by have := fI_neq0 i i_neq0; rewrite fiEi eqxx.
rewrite card_image; last by move=> i j fiEfj; rewrite -[i]fI fiEfj fI.
rewrite addnn (half_bit_double _ false).
apply: eq_card => i; rewrite !inE.
by case: eqP => // ->; rewrite f_eq0 ltnn.
Qed.

Lemma euler_criterion a p : 
  prime p -> ~~ (p %| a) -> 
  a ^ p.-1./2 = (if res_quad p a then 1 else p.-1) %[mod p].
Proof.
move=> pP pNDa.
have p_gt0 : 0 < p by apply: prime_gt0.
have [/res_quadP[i Hi]|Hrn] := boolP (res_quad p a); last first.
  rewrite -fact_sqr_exp //.
  apply/eqP; rewrite -(eqn_modDr 1) !addn1 prednK //.
  have /dvdnP[k->] : (p %| (p.-1)`!.+1) by rewrite -Wilson // prime_gt1.
  by rewrite modnn modnMl.
rewrite -modnXm -Hi modnXm mulnn -expnM mul2n.
have [pO|/(prime_oddPn pP) pE2]:= boolP (odd p); last first.
  by rewrite [in X in (_ ^ X)%nat]pE2 /= expn0.
have i_gt0 : 0 < i.
  case: i Hi pNDa => [] [] //= _.
  by rewrite /dvdn => <- /[!mod0n].
rewrite even_halfK; last by case: (p) pP pO.
apply/eqP; rewrite eqn_mod_dvd //; last by rewrite expn_gt0 i_gt0.
rewrite -(Gauss_dvdr _ (_ : coprime _ i)); last first.
  rewrite prime_coprime //; apply/negP => /dvdnP [k iE].
  rewrite iE mulnA modnMl in Hi.
  by case/negP: pNDa; rewrite /dvdn -Hi.
rewrite mulnBr muln1 -expnS prednK //.
rewrite -eqn_mod_dvd //; first by apply/eqP/fermat_little.
by apply: leq_pexp2l (_ : 1 <= p).
Qed.
