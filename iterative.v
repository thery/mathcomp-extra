From mathcomp Require Import all_boot order all_algebra ssrnum.

(** ITERATIVE : Turning a recursive algo in an iterative one                  *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.POrderTheory Num.ExtraDef Num.

Section iterative.

Local Open Scope ring_scope.

(* Arbitrary ring *)
Variable R : nzRingType.

Implicit Type p : {poly R}.

Local Notation nat := Datatypes.nat.

Variable left : nat -> {poly R} -> {poly R}.
Variable right : nat -> {poly R} -> {poly R}.
Variable merge : nat -> {poly R} -> {poly R} -> {poly R}.

Hypothesis size_left : 
  forall n p, (size p <= 2 ^ n.+1 -> size (left n p) <= 2 ^ n)%N.
Hypothesis size_right : 
  forall n p, (size p <= 2 ^ n.+1 -> size (right n p) <= 2 ^ n)%N.
Hypothesis size_merge : 
  forall n (p q : {poly R}), (size p <= 2 ^ n -> size q <= 2 ^ n -> 
               size (merge n p q) <= 2 ^ n.+1)%N.
Hypothesis merge0 : forall n, merge n 0 0 = 0. 

Fixpoint algo (n : nat) (p : {poly R}) := 
  if n is n1.+1 then 
    merge n1 (algo n1 (left n1 p)) (algo n1 (right n1 p)) 
  else (p`_0)%:P.

Lemma size_algo n p : (size (algo n p) <= 2 ^ n)%N.
Proof.
elim: n p => /= [|n IH] p; first by rewrite size_polyC; case: eqP.
by apply: size_merge; apply: IH.
Qed.

Fixpoint bottom (n : nat) (p : {poly R}) := 
  if n is n1.+1 then 
    bottom n1 (left n1 p) + 'X^(2 ^n1) * bottom n1 (right n1 p)
  else (p`_0)%:P.

Lemma size_bottom n p : (size (bottom n p) <= 2 ^ n)%N.
Proof.
elim: n p => /= [|n IH] p; first by apply: size_polyC_leq1.
apply: leq_trans (size_polyD _ _) _.
rewrite geq_max (leq_trans (IH _)) //=; last by rewrite leq_exp2l.
apply: leq_trans (size_polyMleq _ _) _.
by rewrite size_polyXn expnS mul2n -addnn leq_add.
Qed.

Definition left_poly m (p : {poly R}) := \poly_(i < m) p`_i.
Definition right_poly m (p : {poly R}) := \poly_(i < m) p`_(i + m).

Lemma coef_left_poly m p i : 
  (left_poly m p)`_ i = if (i < m)%N then p`_ i else 0.
Proof. by rewrite coef_poly. Qed.

Lemma coef_right_poly m p i : 
  (right_poly m p)`_ i = if (i < m)%N then p`_ (i + m) else 0.
Proof. by rewrite coef_poly. Qed.

Lemma left_poly_id m p : (size p <= m)%N -> left_poly m p = p.
Proof.
move=> Hs; apply/polyP => i.
rewrite coef_poly; case: leqP => // Hs1.
by apply/sym_equal/nth_default/(leq_trans Hs).
Qed.

Lemma left_polyMXn m p : left_poly m ('X^ m * p) = 0.
Proof.
apply/polyP => i.
rewrite -[_ * p]commr_polyXn coef_poly coefMXn coef0.
by case: leqP.
Qed.

Lemma left_poly_add m (p q : {poly R}) :
  left_poly m (p + q) = left_poly m p + left_poly m q.
Proof.
apply/polyP => i; rewrite !(coefD, coef_poly).
by case: leqP; rewrite ?add0r.
Qed.

Lemma left_poly0 m : left_poly m 0 = 0.
Proof. by apply/polyP => i; rewrite coef_poly coef0 if_same. Qed.

Lemma left_poly_sum m n (p : 'I_n -> {poly R}) :
  left_poly m (\sum_(i < n) p i) = \sum_(i < n) (left_poly m (p i)).
Proof.
have F (q : nat -> _) : 
       left_poly m (\sum_(i < n) q i) = \sum_(i < n) (left_poly m (q i)).
  elim: n {p}q => [|n IH] q; first by rewrite !big_ord0 left_poly0.
  by rewrite !big_ord_recr /= left_poly_add IH.
case: n p F => [|n] p F; first by rewrite !big_ord0 left_poly0.
have := F (fun x => p (inord x)).
under eq_bigr do rewrite inord_val.
by under [X in _ = X -> _]eq_bigr do rewrite inord_val.
Qed.

Lemma right_poly_size_0 m p : (size p <= m)%N -> right_poly m p = 0.
Proof.
move=> Hs; apply/polyP => i.
rewrite coef_poly coef0; case: leqP => // Hs1.
apply: nth_default.
by apply: leq_trans Hs (leq_addl _ _).
Qed.

Lemma right_polyMXn m p : (size p <= m)%N -> right_poly m ('X^ m * p) = p.
Proof.
move=> Hs; apply/polyP => i.
rewrite -[_ * p]commr_polyXn coef_poly coefMXn addnK.
rewrite [(_ + _ < _)%N]ltnNge leq_addl /=.
case: leqP => // mLi.
by apply/sym_equal/nth_default/(leq_trans _ mLi).
Qed.

Lemma right_poly_add m (p q : {poly R}) :
  right_poly m (p + q) = right_poly m p + right_poly m q.
Proof.
apply/polyP => i; rewrite !(coefD, coef_poly).
by case: leqP; rewrite ?add0r.
Qed.

Lemma right_poly0 m : right_poly m 0 = 0.
Proof. by apply/polyP => i; rewrite coef_poly !coef0 if_same. Qed.

Lemma right_poly_sum m n (p : 'I_n -> {poly R}) :
  right_poly m (\sum_(i < n) p i) = \sum_(i < n) (right_poly m (p i)).
Proof.
have F (q : nat -> _) : 
       right_poly m (\sum_(i < n) q i) = \sum_(i < n) (right_poly m (q i)).
  elim: n {p}q => [|n IH] q; first by rewrite !big_ord0 right_poly0.
  by rewrite !big_ord_recr /= right_poly_add IH.
case: n p F => [|n] p F; first by rewrite !big_ord0 right_poly0.
have := F (fun x => p (inord x)).
under eq_bigr do rewrite inord_val.
by under [X in _ = X -> _]eq_bigr do rewrite inord_val.
Qed.

Lemma left_right_polyE m p :
  (size p <= m.*2)%N -> p = left_poly m p + right_poly m p * 'X^m.
Proof.
move=> sL2m; apply/polyP => i.
rewrite coefD coefMXn !coef_poly.
case: leqP => HlP; last by rewrite addr0.
case: leqP => H1lP; last by rewrite subnK ?add0r.
rewrite add0r nth_default //.
apply: leq_trans sL2m _.
by rewrite -addnn -leq_subRL.
Qed.

Fixpoint invariant_algo m n p q :=
  if m is m1.+1 then 
  invariant_algo m1 n (left (m1 + n) p) (left_poly (2 ^ (m1 + n)) q) /\ 
  invariant_algo m1 n (right (m1 + n) p) (right_poly (2 ^ (m1 + n)) q)
  else q = algo n p.

Lemma invariantS_algo m n p q :
  invariant_algo m.+1 n p q <->
  invariant_algo m n (left (m + n) p) (left_poly (2 ^ (m + n)) q) /\ 
  invariant_algo m n (right (m + n) p) (right_poly (2 ^ (m + n)) q).
Proof. by []. Qed.

Lemma invariant_algo_bottom p m :
  invariant_algo m 0 p (bottom m p).
Proof.
elim: m p => //= m IH p.
rewrite addn0 left_poly_add right_poly_add; split.
  rewrite left_polyMXn addr0 left_poly_id; first by by apply: IH.
  by apply: size_bottom.
  
rewrite (right_poly_size_0 (size_bottom _ _)) add0r.
rewrite right_polyMXn; last by apply: size_bottom.
by apply: IH.
Qed.

Definition step m n (p : {poly R}) :=
  \sum_(l < 2 ^ m)
  let le := \poly_(i < 2 ^ n) p`_(i + l * 2 ^ n.+1) in
  let ri := \poly_(i < 2 ^ n) p`_(i + l * 2 ^ n.+1 + 2 ^ n) in
    merge n le ri * 'X^(l * 2 ^ n.+1).

Lemma size_step m n p : (size (step m n p) <= (2 ^ (m + n).+1))%N.
Proof.
apply: leq_trans (size_sum _ _ _) _.
apply/bigmax_leqP_seq => i _ _.
apply: leq_trans (size_polyMleq _ _ ) _.
rewrite size_polyXn addnS /=.
apply: leq_trans (leq_add (size_merge (size_poly _ _) (size_poly _ _)) 
                          (leqnn _)) _.
by rewrite -mulSn -addnS expnD leq_mul2r ltn_ord orbT.
Qed.

Lemma left_step m n (p : {poly R}) :
  (size p <= 2 ^ (m + n).+2)%N ->
  left_poly (2 ^ (m + n).+1) (step m.+1 n p) =
  step m n (left_poly (2 ^ (m + n).+1) p).
Proof.
move=> pLmn.
apply/polyP=> i; rewrite coef_left_poly.
case: leqP => [mnLi|iLmn].
  rewrite nth_default //.
  by apply: leq_trans (size_step _ _ _) _.
rewrite !coef_sum expnS mul2n -addnn big_split_ord /=.
rewrite [X in _ + X = _]big1 ?addr0 => [|j _]; last first.
  by rewrite coefMXn ifT // (leq_trans iLmn) // mulnDl -expnD addnS leq_addr.
apply: eq_bigr => j _.
congr ((merge _ _ _ * _) `_ _).
  apply/polyP => k; rewrite !coef_poly.
  case: leqP => // kLn.
  rewrite ifT // -[in X in (_ < X)%N]addnS expnD.
  rewrite -[X in (_ < X * _)%N]prednK ?expn_gt0 // mulSn -addSn.
  apply: leq_add.
    by apply: leq_trans kLn _; rewrite leq_exp2l.
  by rewrite leq_mul2r -ltnS prednK ?expn_gt0 // ltn_ord orbT.
apply/polyP => k; rewrite !coef_poly.
case: leqP => // kLn.
rewrite ifT // -[in X in (_ < X)%N]addnS expnD addnAC.
rewrite -[X in (_ < X * _)%N]prednK ?expn_gt0 // mulSn -addSn.
apply: leq_add.
  by rewrite expnS mul2n -addnn ltn_add2r.
by rewrite leq_mul2r -ltnS prednK ?expn_gt0 // ltn_ord orbT.
Qed.

Lemma right_step m n (p : {poly R}) :
  (size p <= 2 ^ (m + n).+2)%N ->
  right_poly (2 ^ (m + n).+1) (step m.+1 n p) =
  step m n (right_poly (2 ^ (m + n).+1) p).
Proof.
move=> pLmn.
apply/polyP=> i; rewrite coef_right_poly.
case: leqP => [mnLi|iLmn].
  rewrite nth_default //.
  by apply: leq_trans (size_step _ _ _) _.
rewrite !coef_sum expnS mul2n -addnn big_split_ord /=.
rewrite [X in X + _ = _]big1 ?add0r => [|j _]; last first.
  rewrite coefMXn ifN; last first.
    rewrite -leqNgt (leq_trans _ (leq_addl _ _)) //.
    by rewrite -addnS expnD leq_mul2r // ltnW ?orbT.
  rewrite nth_default // (leq_trans (size_merge _ _)) // ?size_poly //.
  rewrite leq_subRL (leq_trans _ (leq_addl _ _)) //.
    by rewrite addnC -mulSn -addnS expnD leq_mul2r ltn_ord orbT.
  by rewrite -addnS expnD leq_mul2r ltnW ?orbT // ltn_ord.
apply: eq_bigr => j _.
rewrite !coefMXn addnC mulnDl -expnD addnS ltn_add2l.
case: leqP => // jLi; rewrite subnDl.
congr ((merge _ _ _) `_ _).
  apply/polyP => k; rewrite !coef_poly.
  case: leqP => // kLn.
  rewrite ifT; first by rewrite addnAC addnA.
  rewrite -[in X in (_ < X)%N]addnS expnD.
  rewrite -[X in (_ < X * _)%N]prednK ?expn_gt0 // mulSn -addSn.
  apply: leq_add.
    by apply: leq_trans kLn _; rewrite leq_exp2l.
  by rewrite leq_mul2r -ltnS prednK ?expn_gt0 // ltn_ord orbT.
apply/polyP => k; rewrite !coef_poly.
case: leqP => // kLn.
rewrite ifT.
  rewrite -!addnA.
  congr (_ `_ (_ + _)); first by rewrite addnC !addnA.
rewrite addnAC -[in X in (_ < X)%N]addnS expnD.
rewrite -[X in (_ < X * _)%N]prednK ?expn_gt0 // mulSn -addSn.
apply: leq_add.
  by rewrite expnS mul2n -addnn ltn_add2r.
by rewrite leq_mul2r -ltnS prednK ?expn_gt0 // ltn_ord orbT.
Qed.

Lemma invariant_algo_step m n p p1 :
  (size p <= 2 ^ (m + n).+1)%N ->
  (size p1 <= 2 ^ (m + n).+1)%N ->
  invariant_algo m.+1 n p p1 ->
  invariant_algo m n.+1 p (step m n p1).
Proof.
elim: m n p p1; last first.
  move=> m IH n p p1 Hsp Hsp1/invariantS_algo[H2 H3].
  apply/invariantS_algo; split.
    rewrite addnS left_step //.
    apply: IH => //.
      by apply: leq_trans (size_left _) _.
    by rewrite size_poly.
  rewrite addnS right_step //.
  apply: IH => //.
    by apply: leq_trans (size_right _) _.
  by rewrite size_poly.
move=> n p p1; rewrite add0n => Hp Hp1 [H1 H2].
rewrite /= -H1 -H2.
rewrite /step big_ord1 mul0n mulr1.
by congr (merge _ _ _); apply/polyP=> i; rewrite !coef_poly !add0n !addn0.
Qed.

Fixpoint istep_aux m n p :=
  if m is m1.+1 then  istep_aux m1 n.+1 (step m1 n p) else p.

Definition istep n p := istep_aux n 0 (bottom n p).

Lemma istep_algo n p : (size p <= 2 ^ n)%N -> istep n p = algo n p.
Proof.
move=> Hs.
suff /(_ n 0%N): forall m1 n1 (p1 q1 : {poly R}), 
    (size p1 <= 2 ^ (m1 + n1))%N ->
    (size q1 <= 2 ^ (m1 + n1))%N ->
    invariant_algo m1 n1 p1 q1 -> 
    invariant_algo 0 (m1 + n1) p1 (istep_aux m1 n1 q1).
  rewrite addn0; apply => //; first by apply: size_bottom.
  by apply: invariant_algo_bottom.
elim => [//| m1 IH] n1 p1 q1 Hs1 Hs2 H1.
rewrite /istep_aux -/istep_aux addSnnS.
apply: IH; first by rewrite addnS.
  rewrite addnS.
  by apply: leq_trans (size_step _ _ _) _.
by apply: invariant_algo_step.
Qed.

End iterative.
