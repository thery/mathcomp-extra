From mathcomp Require Import all_boot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*                      Formalisation of Montgomery reduction                 *)
(*                                                                            *)
(******************************************************************************)


Section Montgomery.

Record montgomery := { 
    p : nat;
    b : nat;
    n : nat;
    co: [&& coprime p b, b * p != 0 & p < b ^ n]
  }.

Lemma coprime_bp m : coprime (b m) (p m).
Proof. by rewrite coprime_sym; case: m => p b n /= /and3P[]. Qed.

Implicit Type m : montgomery.

Lemma p_gt0 m : 0 < p m.
Proof. by case: m => [] [|p] [|b] n /and3P[] //=; rewrite muln0. Qed.

Lemma b_gt0 m : 0 < b m.
Proof. by case: m => [] [|p] [|b] n /and3P[] //=; rewrite muln0. Qed.

Definition w m := b m ^ n m.

Lemma pLw m : p m < w m.
Proof. by rewrite /w; case: m => p b n /= /and3P[]. Qed.

Lemma w_gt0 m : 0 < w m.
Proof. by rewrite expn_gt0 b_gt0. Qed.

Definition oppw m v := 
  let v1 := v %% w m in if v1 == 0 then 0 else w m - v1.

Lemma ltn_oppw m v : oppw m v < w m.
Proof.
rewrite /oppw; case: (v %% w m) (ltn_pmod v (w_gt0 m)) => //= v1 v1Lw.
by case: w v1Lw => //= w1 _; rewrite subSS ltnS leq_subr.
Qed.

Lemma oppwE m v : v + oppw m v = 0 %[mod w m].
Proof.
rewrite /oppw -modnDml.
case: (v %% w m) (ltn_pmod v (w_gt0 m)) => //= v1 v1Lw.
by rewrite mod0n addnC subnK ?modnn // ltnW.
Qed.

Lemma oppw_mod m v : oppw m (v %% w m) = oppw m v.
Proof. by rewrite /oppw modn_mod. Qed.

Lemma oppwMr m v1 v2 : oppw m v1 * v2 = oppw m (v1 * v2) %[mod w m].
Proof.
have w_gt0 := w_gt0 m.
rewrite /oppw -[(v1 * v2) %% _]modnMml.
case: (v1 %% _) (ltn_pmod v1 w_gt0) => [|v3]; rewrite /= ?mod0n // => v3Lw.
case: eqP => [wL|wL].
  rewrite mulnBl modnB //.
    by rewrite wL subn0 modnMr addn0 ltnn mod0n.
  by rewrite leq_mul2r ltnW ?orbT.
rewrite mulnBl !modnB //; last 2 first.
- by rewrite ltnW // ltn_mod.
- by rewrite leq_mul2r ltnW ?orbT.
rewrite !modnn modn_mod.
by rewrite -modnMml modnn mod0n.
Qed.

Lemma coprime_pw m : coprime (p m) (w m).
Proof. by apply: coprimeXr; rewrite coprime_sym; apply: coprime_bp. Qed.

(* A_h *)
Definition high m a := a %/ w m.
(* A_l *)
Definition low m a := a %% w m.

Lemma high_low m a : a = high m a * w m + low m a.
Proof. by exact: divn_eq. Qed.

(* P ^ -1 mod b ^ n *)
Definition invp m := (egcdn (p m) (w m)).1 %% w m.

Lemma invpE m : p m * invp m = 1 %[mod w m].
Proof.
rewrite /invp.
case: egcdnP => [|/= km kn Hm _]; first by exact: p_gt0.
by rewrite modnMmr mulnC Hm (eqP (coprime_pw m)) modnMDl.
Qed.

(* b ^ -1 mod P *)
Definition invb m := (egcdn (b m) (p m)).1 %% p m.

Lemma invbE m : b m * invb m = 1 %[mod p m].
Proof.
rewrite /invb.
case: egcdnP => [|/= km kn Hm _]; first by exact: b_gt0.
by rewrite modnMmr mulnC Hm (eqP (coprime_bp m)) modnMDl.
Qed.

(* Q = - A0 * P ^-1 mod b ^ n *)
Definition q m a := oppw m ((low m a * invp m) %% w m).

Lemma q_bound m a : q m a < w m.
Proof. by apply: ltn_oppw. Qed.

Definition reduce m a := 
  let v := high m (a + q m a * p m) in 
  if v < p m then v else v - p m.

Definition invw m := invb m ^ n m.

Lemma invwE m : w m * invw m = 1 %[mod p m].
Proof. by rewrite -expnMn -modnXm invbE modnXm exp1n. Qed.

Lemma reduceE m a : a < w m * p m -> reduce m a = (a * invw m) %% p m.
Proof.
move=> aLwp.
rewrite /reduce.
set a1 := _ + _ * _.
have a1w : a1 = 0 %[mod w m].
  rewrite /a1 /q -modnDmr oppwMr modnDmr.
  rewrite -oppw_mod modnMml -mulnA -modnMmr [_ * p m]mulnC invpE modnMmr muln1.
  by rewrite oppw_mod {1}[a](high_low m) -addnA modnMDl oppwE.
have a1P : a1 = a %[mod p m] by rewrite /a1 -modnDmr modnMl addn0.
rewrite -modnMml -a1P modnMml [a1 in RHS](high_low m) /low a1w mod0n addn0.
rewrite -mulnA -modnMmr invwE modnMmr muln1.
case: leqP => // Hp; last by rewrite modn_small.
suff hL2p : high m a1 < (p m).*2.
  rewrite -[in RHS](subnK Hp) -modnDmr modnn addn0 modn_small //.
  by rewrite ltn_subLR ?addnn.
rewrite ltn_divLR ?w_gt0 // /a1 -addnn mulnDl.
apply: leq_ltn_trans (_ : a + p m * w m < _).
  by rewrite leq_add2l mulnC leq_mul2l ltnW ?orbT // q_bound.
by rewrite ltn_add2r mulnC.
Qed.

Definition w2 m := (b m ^ (n m).*2) %% p m.

Definition encode m a := reduce m (a * w2 m).

Lemma encodeE m a : a < w m -> encode m a = (a * w m) %% p m.
Proof.
move=> aLp.
rewrite /encode reduceE /w2 -addnn expnD // -[b m ^ n m]/(w m).
  by rewrite -modnMml modnMmr modnMml !mulnA -mulnA -modnMmr invwE modnMmr muln1.
apply: leq_ltn_trans (_ : a * p m < _).
  by rewrite leq_mul2l ltnW ?orbT // ltn_mod p_gt0.
by rewrite ltn_mul2r p_gt0.
Qed.

Definition decode m a := reduce m a.

Definition mult m a b := decode m (reduce m (encode m a * encode m b)).

Lemma multE m a b : a < p m -> b < p m -> mult m a b = a * b %% p m.
Proof.
move=> aL bL.
have aL1 : a < w m by apply: ltn_trans aL (pLw _).
have bL1 : b < w m by apply: ltn_trans bL (pLw _).
rewrite /mult /decode !encodeE // ?reduceE.
- rewrite modnMml -!mulnA modnMml mulnC -!mulnA modnMml.
  rewrite [invw m * (a * _)]mulnC !mulnA -mulnA.
  rewrite -modnMmr invwE modnMmr muln1 mulnC !mulnA -mulnA.
  by rewrite -modnMmr invwE modnMmr muln1.
- apply: leq_ltn_trans (_ : (a * w m) %% p m * p m < _).
    by rewrite leq_mul2l ltnW ?orbT // ltn_mod p_gt0.
  rewrite ltn_mul2r p_gt0.
  by apply: leq_ltn_trans (pLw m); rewrite ltnW // ltn_mod p_gt0.
- apply: leq_trans (_ : 1 * p m <= _).
    by rewrite mul1n ltn_mod p_gt0.
  by rewrite leq_mul2r w_gt0 orbT.
apply: leq_ltn_trans (_ : (a * w m) %% p m * p m < _).
  by rewrite leq_mul2l ltnW ?orbT // ltn_mod p_gt0.
rewrite ltn_mul2r p_gt0.
by apply: leq_ltn_trans (pLw m); rewrite ltnW // ltn_mod p_gt0.
Qed.

(* An example *)

Definition m0 := {| p := 293; b := 10; n := 3; co := isT |}.

Compute (mult m0 234 167).

Definition m1 := {| p := 293; b := 2; n := 9; co := isT |}.

Compute (mult m1 234 167).


End Montgomery.
