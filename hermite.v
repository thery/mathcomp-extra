(******************************************************************************)
(*                                                                            *)
(*                                                                            *)
(*                    Proof of Hermite's identity                             *)
(*                                                                            *)
(*    `⌊x⌋  : floor function                                                  *)
(*    `⌈x⌋  : nearest-int function with `⌈ n + 1/2 ⌋ = n + 1                  *)
(*                                                                            *)
(*    hermite's identity : `⌊nx⌋ = \sum_(k < n) `⌊x + k / n⌋                  *)
(*                                                                            *)
(*    special case when n = 2 : `⌊2x⌋ - `⌊x⌋ = `⌈x⌋                           *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.

Local Open Scope ring_scope.

Import GRing.Theory Num.Theory Order.TTheory.

Section Hermite.

Variable R : archiRealFieldType.

Local Notation " `⌊ x ⌋ " := ((Num.floor x)%:~R) (format "`⌊ x ⌋" ).

Definition frac_part (x : R) := x - `⌊ x ⌋.

Local Notation " `{ x } " := (frac_part x) (format "`{ x }" ).

Lemma fracE (x : R) : x = `⌊x⌋ + `{x}.
Proof. by rewrite /frac addrC subrK. Qed.

Lemma frac_le (x : R) : 0 <= `{x} < 1.
Proof. by rewrite subr_ge0 ltrBlDl floor_le -(intrD _ _ 1) floorD1_gt. Qed.

Definition half_up (x : R) : R := `⌊x + 2^-1⌋.

Local Notation " `⌈ x ⌋ " := (half_up x) (format "`⌈ x ⌋" ).

Lemma half_up_le x : `⌊x⌋ <= `⌈x⌋.
Proof.
rewrite ler_int; apply: le_floor.
by rewrite -[X in X <= _]addr0 lerD2l invr_ge0 (ler_nat _ 0 2).
Qed.

Lemma half_up_gt x : `⌈x⌋ <= `⌊x⌋ + 1.
Proof.
rewrite -(intrD _ _ 1) -(floor1 R) -floorDrz // ler_int; apply: le_floor.
by rewrite lerD2l invf_le1 // (ler_nat _ 1 2).
Qed.

Inductive half_up_build (x : R) : R -> Prop := 
  half_up_build_floor : x < `⌊x⌋ + 2^-1 -> half_up_build x `⌊x⌋
| half_up_build_ceil : `⌊x⌋ + 2^-1 <= x -> half_up_build x (`⌊x⌋ + 1)%R.

Lemma half_upP x : half_up_build x `⌈x⌋.
Proof.
have [xLx2|x2Lx] := leP (`⌊x⌋ + 2^-1) x; last first.
  suff -> : `⌈x⌋ = `⌊x⌋ by apply/half_up_build_floor.
  suff x2E : Num.floor (x + 2^-1)  = Num.floor x.
    by congr (_%:~R); apply/sym_equal/eqP; rewrite floor_eq x2E floor_itv.
  apply/floor_def.
  rewrite intrD (le_trans (floor_le _) _) //=; last first.
    by rewrite lerDl invr_ge0 (ler_nat _ 0 2).
  by rewrite [1%:~R]splitr mul1r addrA ltrD2r.
suff -> : `⌈x⌋ = `⌊x⌋ + 1 by apply/half_up_build_ceil.
suff x2E : Num.floor (x + 2^-1)  = Num.floor x + 1 
  by rewrite /half_up x2E intrD.
apply/floor_def.
rewrite 2!intrD [1%:~R]splitr mul1r addrA lerD2r xLx2 /= addrA ltrD2r.
by rewrite (lt_le_trans (floorD1_gt _)) // lerDl invr_ge0 (ler_nat _ 0 2).
Qed.

Lemma half_up_half : `⌈2^-1⌋ = 1. 
Proof.
by have := splitr (1 : R); rewrite mul1r /half_up => <-; rewrite floorK.
Qed.

Lemma half_up_nearest (x : R) (y : int ): `|x - `⌈x⌋| <= `|x - y%:~R|.
Proof.
have [yLx|xLy] := leP y (Num.floor x).
  suff F : `|x - `⌈x⌋| <= `|x - `⌊x⌋|.
    apply: le_trans F _.
    rewrite !ger0_norm ?subr_ge0 ?floor_le //; first by rewrite lerB ?ler_int.
    by rewrite (le_trans _ (floor_le _)) // ler_int.
  have [//|xLx2] := half_upP.
  rewrite [X in _ <= X]ger0_norm; last by rewrite subr_ge0 floor_le.
  rewrite ler0_norm; last first.
    by rewrite subr_le0; have /ltW := floorD1_gt x; rewrite intrD.
  rewrite opprB.
  apply: le_trans (_ : 2^-1 <= _); last by rewrite lerBrDl.
  rewrite addrAC [X in _ + X <= _]splitr -[X in _ <= X]add0r mul1r addrA.
  by rewrite lerD2r addrAC lerBlDl addr0.
rewrite -lezD1 in xLy.
rewrite [X in _ <= X]ler0_norm ?opprB; last first.
  by rewrite subr_le0 (le_trans (ltW (floorD1_gt _))) // ler_int.
suff F : `|x - `⌈x⌋| <= `|x - `⌊x + 1⌋|.
  apply: le_trans F _.
  rewrite ler0_norm ?opprB; last first.
    by rewrite subr_le0 floorDrz // floor1 (ltW (floorD1_gt _)).
  by rewrite lerD2r floorDrz // floor1 ler_int.
have [xLx2|x2Lx] := half_upP; last by rewrite floorDrz // floor1 intrD.
rewrite [X in _ <= X]ler0_norm ?opprB; last first.
  by rewrite subr_le0 floorDrz // floor1 (ltW (floorD1_gt _)).
have xLx2' := ltW xLx2.
rewrite ger0_norm; last by rewrite subr_ge0 floor_le.
apply: le_trans (_ : 2^-1 <= _); first by rewrite lerBlDl.
rewrite floorDrz // floor1 intrD addrAC.
rewrite [X in _ <= _ + X]splitr -[X in X <= _]add0r mul1r addrA lerD2r.
by rewrite addrAC subr_ge0.
Qed.

Lemma hermite_id (n : nat) x : 
 `⌊n%:R * x⌋ = \sum_(k < n) (`⌊x + k%:R / (n%:R:R)⌋ : R).
Proof.
have [//|n_gt0|->] := ltngtP n 0; last by rewrite big_ord0 mul0r floor0.
have n_neq0 : n%:R != 0 :> R by rewrite (eqr_nat _ _ 0); case: (n) n_gt0.
have nr_nt0 : (0 : R) < n%:R by rewrite (ltr_nat _ 0).
pose g (k : nat) : R := `⌊x + k%:R / (n%:R : R)⌋.
rewrite -(@big_mkord _ _ _ _ xpredT g) {}/g.
rewrite (fracE x) mulrDr addrC -(intrM _ (Posz n)) floorDrz // intrD.
rewrite [X in _ + X = _]floorK // intrM.
under eq_bigr do rewrite -addrA addrC floorDrz // intrD.
rewrite big_split /=.
rewrite sumr_const_nat subn0.
rewrite [in X in _ = _ + X]floorK // [X in _ + X = _]mulr_natl.
suff <- : `⌊n%:R * `{ x}⌋ = (\sum_(0 <= i < n)  `⌊`{ x} + i%:R / n%:R⌋ : R).
   by [].
have /andP[x_ge0 x_lt1] := frac_le x.
pose fnx := Num.floor (n%:R * `{x}).
have fnx_pos : 0 <= fnx by rewrite floor_ge0 mulr_ge0.
have fnxLn : (`|fnx| <= n)%N.
  rewrite -lez_nat intOrdered.gez0_norm //.
  rewrite -(ler_int R) (le_trans (floor_le _)) //.
  by rewrite -[X in _ <= X]mulr1 ler_pM  // ltW.
pose t := (n - `|fnx|)%N.
pose cnx := Num.ceil (n%:R * (1 - `{x})).
have cnx_pos : 0 <= cnx.
  by rewrite ceil_ge0 (lt_le_trans (ltrN10 R)) // mulr_ge0 // subr_ge0 ltW.
have nLcnx : (`|cnx| <= n)%N.
  rewrite -(ler_nat R) natr_absz ger0_norm //.
  have /le_ceil : n%:R * (1 - `{x}) <= n%:R.
    by rewrite mulrBr mulr1 gerBl mulr_ge0.
  rewrite -/cnx -(ler_int R) //.
  suff /eqP->// : (Num.Def.ceil (n%:R : R))%:~R == (n%:R : R) by [].
  by rewrite -intrEceil.
have tE : t = (`|cnx| : nat).
  rewrite /cnx mulrBr mulr1 addrC ceilDrz // ceilNfloor opprK addrC.
  have -> : Num.Def.ceil (n%:R : R) = (n : int).
    by apply/eqP; rewrite -(eqr_int R) -intrEceil.
  by rewrite -[LHS]distnEl ?intOrdered.gez0_norm.
rewrite (big_cat_nat_idem _ (_ : 0 <= t)%N) //=; last 2 first.
- by rewrite add0r.
- by rewrite leq_subr.
rewrite big_nat_cond /= big1 ?add0r => [|i iLt]; last first.
  rewrite andbT tE in iLt.
  have iLt' : (i%:~R < n%:R * (1 - `{x})).
    rewrite -real_ceil_gt_int; last by rewrite !realE mulr_ge0 // subr_ge0 ltW.
    by rewrite -ltz_nat // intOrdered.gez0_norm in iLt.
  have -> : 0 = 0%:~R :>R by [].
  congr (_%:~R); apply: floor_def.
  rewrite add0r addr_ge0 //=; last by rewrite divr_ge0.
  rewrite -[`{x}](mulfK n_neq0) -mulrDl ltr_pdivrMr // mul1r.
  by rewrite -ltrBrDl -[X in _ < X - _]mul1r -mulrBl mulrC.
rewrite big_nat_cond (eq_bigr (fun _ => 1%R)).
  rewrite -big_nat_cond sumr_const_nat natrB ?tE //.
  rewrite -tE natrB ?opprB //.
  by rewrite addrC subrK natr_absz ger0_norm.
move=> i; rewrite andbT => /andP[tLi iLn].
rewrite tE in tLi.
rewrite -[RHS]/(1%:~R).
congr (_%:~R); apply: floor_def; apply/andP; split.
  rewrite -[`{x}](mulfK n_neq0) -mulrDl ler_pdivlMr // mul1r.
  rewrite -lerBlDl -[X in X - _ <= _]mul1r -mulrBl mulrC.
  rewrite (le_trans (ceil_ge _)) -/cnx //.
  by rewrite -(ler_nat R) natr_absz ger0_norm in tLi.
rewrite intrD (le_lt_trans (_ : _ <= `{x} + 1)) //.
  by rewrite lerD // ler_pdivrMr // mul1r ler_nat ltnW.
by rewrite ltr_leD.
Qed.

Lemma hermite_id2 x :  `⌊2 * x⌋ - `⌊x⌋ = `⌈x⌋.
Proof.
rewrite hermite_id big_ord_recr /= big_ord1 mul0r addr0.
by rewrite mul1r /half_up addrAC subrr add0r.
Qed.

End Hermite.