From mathcomp Require Import all_ssreflect.

From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Board.

Inductive turn := white | black.

Definition flip  t := if t is white then black else white.

Lemma flipK : involutive flip.
Proof. by case. Qed.

Variable board : finType.
Variable init : board.
Variable moves : turn -> board -> seq board.
Variable depth : board -> nat.

Hypothesis moves_depth : 
  forall t b b1, b1 \in moves t b -> depth b1 = (depth b).-1.

Inductive state := win | loss | draw.

Implicit Type s : state.

Coercion s2n s := 
  match s with 
  | loss => 1
  | draw => 3
  | win => 5
  end.


Definition eqs s1 s2 := (s1 == s2 :> nat).

Lemma eqsP : Equality.axiom eqs.
Proof. by do 2!case; constructor. Qed.

Canonical state_eqMixin := EqMixin eqsP.
Canonical state_eqType := Eval hnf in EqType state state_eqMixin.

Definition smin s1 s2 := if s1 <= s2 then s1 else s2.

Lemma sminC : commutative smin.
Proof. by do 2 case. Qed.

Lemma sminA : associative smin.
Proof. by do 3 case. Qed.

Lemma sminwn : left_id win smin.
Proof. by case. Qed.

Lemma sminnw : right_id win smin.
Proof. by case. Qed.

Lemma sminln : left_zero loss smin.
Proof. by case. Qed.
Lemma sminnl : right_zero loss smin.
Proof. by case. Qed.

Canonical smin_monoid := Monoid.Law sminA sminwn sminnw.
Canonical smin_comoid := Monoid.ComLaw sminC.

Definition smax s1 s2 := if s1 <= s2 then s2 else s1. 

Lemma smaxC : commutative smax.
Proof. by do 2 case. Qed.

Lemma smaxA : associative smax.
Proof. by do 3 case. Qed.

Lemma smaxln : left_id loss smax.
Proof. by case. Qed.

Lemma smaxnl : right_id loss smax.
Proof. by case. Qed.

Lemma smaxwn : left_zero win smax.
Proof. by case. Qed.

Lemma smaxnw : right_zero win smax.
Proof. by case. Qed.

Canonical smax_monoid := Monoid.Law smaxA smaxln smaxnl.
Canonical smax_comoid := Monoid.ComLaw smaxC.

Notation "\smin_ ( i <- l ) F" := (\big[smin/win]_(i <- l) F)
 (at level 41, F at level 41, i, l at level 50,
  format "\smin_ ( i  <-  l )  F").

Notation "\smax_ ( i <- l ) F" := (\big[smax/loss]_(i <- l) F)
 (at level 41, F at level 41, i, l at level 50,
  format "\smax_ ( i  <-  l )  F").

Definition sflip x := 
  if x is win then loss else if x is loss then win else draw.

Lemma sflip_inj : injective sflip.
Proof. by case; case. Qed.

Lemma sflipK : involutive sflip.
Proof. by case. Qed.

Lemma sflip_max s1 s2 : sflip (smax s1 s2) = smin (sflip s1) (sflip s2).
Proof. by case: s1; case: s2. Qed.

Lemma sflip_min s1 s2 : sflip (smin s1 s2) = smax (sflip s1) (sflip s2).
Proof. by case: s1; case: s2. Qed.

Lemma ge_sminr s1 s2 : smin s1 s2 <= s2.
Proof. by case: s1; case: s2. Qed.

Lemma ge_sminl s1 s2 : smin s1 s2 <= s1.
Proof. by case: s1; case: s2. Qed.

Lemma le_smaxr s1 s2 : s2 <= smax s1 s2.
Proof. by case: s1; case: s2. Qed.

Lemma le_smaxl (s1 s2 : state) : s1 <= smax s1 s2.
Proof. by case: s1; case: s2. Qed.

Lemma smin_lel s1 s2 : s1 <= s2 -> smin s1 s2 = s1.
Proof. by case: s1; case: s2. Qed.

Lemma smin_ler s1 s2 : s2 <= s1 -> smin s1 s2 = s2.
Proof. by case: s1; case: s2. Qed.

Lemma lt_smin s1 s2 s3 : s1 < s2 -> s1 < s3 -> s1 < smin s2 s3.
Proof. by case: s1; case: s2; case: s3. Qed.

Lemma ge_winE s : win <= s -> s = win.
Proof. by case: s. Qed.
 
Lemma le_win s : s <= win.
Proof. by case: s. Qed.

Lemma le_lossE s : s <= loss -> s = loss.
Proof. by case: s. Qed.

Lemma ge_loss s : loss <= s.
Proof. by case: s. Qed.

Lemma sle_antisym s1 s2 : s1 <= s2 -> s2 <= s1 -> s1 = s2.
Proof. by case: s1; case: s2. Qed.

Lemma sflip_le s1 s2 : (sflip s1 <= sflip s2) = (s2 <= s1).
Proof. by case: s1; case: s2. Qed.

Lemma sflip_lt s1 s2 : (sflip s1 < sflip s2) = (s2 < s1).
Proof. by case: s1; case: s2. Qed.

Lemma smaxE s1 s2 s3 : (smax s1 s2 == s3) -> ((s1 == s3) || (s2 == s3)).
Proof. by case: s1; case: s2; case: s3. Qed.

Lemma le_bigsmax (A : eqType) (f : A -> state) c l : 
  c \in l -> f c <= \smax_(i <- l) f i.
Proof.
elim: l => // a l IH;
    rewrite big_cons in_cons => /orP[/eqP<-| /IH /leq_trans H].
  by case: (f) (\smax_(_ <- _) _) => // [] [].
by apply: H; case: (f) (\smax_(_ <- _) _) => // [] [].
Qed.

Lemma le_bigsmin (A : eqType) (f : A -> _) c l : 
  c \in l ->  \smin_(i <- l) f i <= f c.
Proof.
elim: l => // a l IH;
    rewrite big_cons in_cons => /orP[/eqP<-| /IH /leq_trans H].
  by case: (f) (\smin_(_ <- _) _) => // [] [].
by apply: leq_trans (H _ (leqnn _)); 
   case: (f) (\smin_(_ <- _) _) => // [] [].
Qed.

Lemma bigsmax_ex (A : eqType) (f : A -> _) l : 
  l != nil -> exists2 c, c \in l & \smax_(i <- l) f i = f c.
Proof.
elim: l => // a [ _ _|b l /(_ isT) [c H1c H2c] _].
  exists a; first by rewrite in_cons eqxx.
  by rewrite big_cons big_nil; case: f.
have [faE|] := f a =P \smax_(i <- [:: a, b & l]) f i.
  by exists a; rewrite // in_cons eqxx.
rewrite big_cons H2c => faNE; exists c; first by rewrite in_cons H1c orbT.
by case: (f a) faNE; case: (f c).
Qed.

Lemma bigsmin_ex (A : eqType) (f : A -> _) l : 
  l != nil -> exists2 c, c \in l & \smin_(i <- l) f i = f c.
Proof.
elim: l => // a [ _ _|b l /(_ isT) [c H1c H2c] _].
  exists a; first by rewrite in_cons eqxx.
  by rewrite big_cons big_nil; case: f.
have [faE|] := f a =P \smin_(i <- [:: a, b & l]) f i.
  by exists a; rewrite // in_cons eqxx.
rewrite big_cons H2c => faNE; exists c; first by rewrite in_cons H1c orbT.
by case: (f a) faNE; case: (f c).
Qed.

Variable ieval : turn -> board -> option state.

Hypothesis liveness : forall t b, (ieval t b == None) = (moves t b != nil).
Hypothesis depth_ieval : forall t b, (ieval t b == None) = (depth b != 0).

Fixpoint eval_rec n t b :=
   if ieval t b is some v then v else
   if n is n1.+1 then 
     let t1 := flip t in
     sflip (\smin_(i <- moves t b) eval_rec n1 t1 i)
   else draw (* this will never occur if we choose n well *).

Definition eval t b := eval_rec (depth b) t b.

Lemma eval_recE n t b : 
  eval_rec n t b =
   if ieval t b is some v then v else
   if n is n1.+1 then 
     let t1 := flip t in
     sflip (\smin_(i <- moves t b) eval_rec n1 t1 i)
   else draw.
Proof. by case: n. Qed.

Lemma eval_recS n t b : 
  (depth b <= n)%N -> eval_rec n.+1 t b = eval_rec n t b.
Proof.
elim: n t b => [/=|n IH] t b Hd.
  by case: ieval (depth_ieval t b) Hd => //; case: depth.
rewrite !eval_recE; case: ieval => //.
elim: moves (@moves_depth t b) => [_ |b1 bs IH1 H1d].
   by rewrite  /= !big_nil.
lazy zeta in IH1 |- *; rewrite !big_cons !sflip_min.
rewrite IH ?IH1 //.
  by move=> b2 Hb2; apply: H1d; rewrite in_cons Hb2 orbT.
rewrite H1d; last by rewrite in_cons eqxx.
by rewrite -ltnS; case: depth Hd.
Qed.

Lemma eval_rec_stable m n t b : (depth b <= m <= n)%N ->
  eval_rec n t b = eval_rec m t b.
Proof.
move=> /andP[bLm] /subnK<-; elim: (_ - _) {-2}m bLm => // {m}k IH m bLm.
by rewrite addSnnS IH // ?eval_recS // (leq_trans bLm).
Qed.

Lemma evalE t b : 
  eval t b =
   if ieval t b is some v then v else
     let t1 := flip t in
     sflip (\smin_(b1 <- moves t b) eval t1 b1).
Proof.
rewrite /eval;
   case E : depth (depth_ieval t b) (@moves_depth t b) => [|n] /=;
   case: ieval => //= _ Hd.
congr sflip; elim: moves Hd => [|b1 bs IH] Hd.
  by rewrite !big_nil.
rewrite !big_cons IH => [|b2 Hb2]; last by rewrite Hd // in_cons Hb2 orbT.
rewrite (eval_rec_stable _ (_ : depth b1 <= depth b1 <= n)%nat) //. 
by rewrite leqnn Hd ?leqnn // in_cons eqxx.
Qed.

Lemma i_eval t b v : ieval t b = some v -> eval t b = v.
Proof. by rewrite evalE => ->. Qed.


(* we get a maximal *)
Lemma le_eval t b1 b2 :
  b2 \in moves t b1  -> sflip (eval (flip t) b2) <= eval t b1.
Proof.
move=> b2I.
rewrite [X in _ <= s2n X]evalE.
case: ieval (liveness t b1) => [a /(@sym_equal _ _ _) /negbT| _].
  by rewrite negbK => /eqP H; rewrite H in b2I.
by lazy zeta; rewrite sflip_le le_bigsmin.
Qed.

(* and the maximum is reached in the sons *)
Lemma peval_next t b : 
  ieval t b = None -> 
  exists2 b1, b1 \in moves t b & eval t b = sflip (eval (flip t) b1).
Proof.
move=> Hi; have := liveness t b; rewrite evalE Hi => /(@sym_equal _ _ _).
rewrite eqxx => /idP /(bigsmin_ex (eval (flip t))) [c H1c H2c].
by exists c => //=; rewrite H2c.
Qed.

(* inversion theorem for win *)
Lemma eval_win t b1 b2 :
  b2 \in moves t b1 -> eval (flip t) b2 = loss -> eval t b1 = win.
Proof.
move=> b2I H2; rewrite evalE; case: ieval (liveness t b1) => [v|_].
  move/(@sym_equal _ _ _)=> /negbT; rewrite negbK => /eqP H.
  by rewrite H in b2I.
elim: moves b2I => //= b3 bs IH.
rewrite big_cons sflip_min in_cons => /orP[/eqP<-|/IH->].
  by rewrite H2 smaxwn.
by rewrite smaxnw.
Qed.

(* inversion theorem for loss *)
Lemma eval_loss t b1 :
  ieval t b1 = None -> 
  (forall b, b \in moves t b1 -> eval (flip t) b = win) -> 
  eval t b1 = loss.
Proof.
rewrite evalE => ->.
elim: moves => /= [|b2 bs IH H]; first by rewrite big_nil.
rewrite big_cons sflip_min H ?IH ?in_cons ?eqxx // => b Hb.
by rewrite H // in_cons Hb orbT.
Qed.

(* Inversion theorem for draw *)
Lemma eval_draw t b1 b2 :
  b2 \in moves t b1 -> eval (flip t) b2 = draw -> 
  (forall b, b \in moves t b1 -> 
             eval (flip t) b = draw \/ eval (flip t) b = win) -> 
  eval t b1 = draw.
Proof.
move=> b2I Hb2 H; rewrite evalE.
case: ieval (liveness t b1) => /= [s /(@sym_equal _ _ _) /negbT|_].
  by rewrite negbK => /eqP H1; rewrite H1 in b2I.
elim: moves H b2I => //= b3 bs IH H.
rewrite big_cons sflip_min in_cons => /orP[/eqP<-| /IH->]; last first.
- by move=> b4 Hb4; apply: H; rewrite in_cons Hb4 orbT.
- by case (H b3) => [|-> |->] //; rewrite in_cons eqxx.
rewrite Hb2.
elim: (bs) H => [|b4 {IH}bs IH H]; first by rewrite big_nil.
rewrite big_cons sflip_min smaxA [smax (sflip _) _]smaxC -smaxA IH //.
  by case: (H b4) => [|->|->] //; rewrite !in_cons eqxx orbT.
move=> b5 Hb5; apply: H; rewrite !in_cons orbA [(b5 == _) || _]orbC -orbA.
by rewrite -in_cons Hb5 orbT.
Qed.

(* First refinement we explictly compute the big op *)
Fixpoint process_eval_rec1 (eval : board -> state) res l :=
  if l is i :: l1 then
    let res1 := smin (eval i) res in process_eval_rec1 eval res1 l1
  else res.

Fixpoint eval_rec1 n t b := 
  if ieval t b is some v then v else
  if n is n1.+1 then 
     sflip (process_eval_rec1 (eval_rec1 n1 (flip t)) win (moves t b))
  else draw.

Lemma process_eval_rec1_correct f res l l1 :
  res = \smin_(i <- l1) f i ->
  process_eval_rec1 f res l = \smin_(i <- l ++ l1) f i.
Proof.
elim: l l1 res => //= i l IH l1 res resE.
have /IH-> : smin (f i) res = \smin_(i <- (i :: l1)) f i.
  by rewrite big_cons //= -resE.
rewrite !(big_cat, big_cons) /=.
by rewrite sminC -!sminA [X in smin _ X]sminC.
Qed.

Lemma eval_rec1_correct n t b : eval_rec1 n t b = eval_rec n t b.
Proof.
elim: n t b => //= n IH t b.
case: ieval => //; congr (sflip _).
rewrite -{2}[moves t b]cats0.
have H : win= \smin_(i <- [::]) eval_rec n (flip t) i by rewrite big_nil.
rewrite {1}H.
elim: (moves t b) [::]=> //= i l1 IH1 l2.
have := IH1 (i :: l2).
rewrite IH big_cons // => ->.
by rewrite !(big_cat, big_cons) /= sminC -sminA [X in smin _ X = _]sminC sminA.
Qed.

Lemma le_process_eval_rec1 eval res l : 
    process_eval_rec1 eval res l <= res.
Proof.
elim: l res =>  /= [res|i l IH res]; first by apply: leqnn.
by apply: leq_trans (IH _) (ge_sminr _ _).
Qed.

Definition eval1 t b := eval_rec1 (depth b) t b.

Lemma eval1_correct t b : eval1 t b = eval t b.
Proof. by apply: eval_rec1_correct. Qed.

(* Second refinement we stop on first loss *)
Fixpoint process_eval_rec2 (eval : board -> state) res l :=
  if l is i :: l1 then
    let res1 := smin (eval i) res in 
    if res1 is loss then loss else process_eval_rec2 eval res1 l1
  else res.

Fixpoint eval_rec2 n t b := 
  if ieval t b is some v then v else
  if n is n1.+1 then 
     sflip (process_eval_rec2 (eval_rec2 n1 (flip t)) win (moves t b))
  else draw.

Lemma process_eval_rec1_loss f l : process_eval_rec1 f loss l = loss.
Proof. by elim: l => //= i l H; rewrite sminnl. Qed. 

Lemma process_eval_rec2_correct f res l :
  process_eval_rec2 f res l = process_eval_rec1 f res l.
Proof.
elim: l res => //= i l IH res.
by case: (f i); case: res; rewrite /= ?process_eval_rec1_loss.
Qed.

Lemma eval_rec2_correct n t b : eval_rec2 n t b = eval_rec n t b.
Proof.
elim: n t b => //= n IH t b.
case: ieval => //.
rewrite process_eval_rec2_correct.
have /process_eval_rec1_correct : 
  win = \smin_(i <- [::]) (eval_rec2 n (flip t)) i by rewrite big_nil.
move=> /(_ (moves t b)); rewrite cats0 => ->.
by congr (sflip _); apply: eq_bigr => *; apply: IH.
Qed.

Definition eval2 t b := eval_rec2 (depth b) t b.

Lemma eval2_correct t b : eval2 t b = eval t b.
Proof. by apply: eval_rec2_correct. Qed.

(* Third refinement we introduce alpha beta *)

Fixpoint process_eval_rec3 (eval :  state -> state -> board -> state) 
                            alpha beta res l : state :=
  if l is i :: l1 then
    let res1 := eval alpha beta i in
    if res <= res1 then process_eval_rec3 eval alpha beta res l1 else
    (* res1 is good *)
    if beta <= res1 then process_eval_rec3 eval alpha beta res1 l1
    else 
    (* we improve max *)
    let beta := res1 in
    if beta <= alpha then res1 (* cut *) else 
        process_eval_rec3 eval alpha beta res1 l1 
    else res.
  
Lemma le_process_eval_rec3 eval alpha beta res l : 
    process_eval_rec3 eval alpha beta res l <= res.
Proof.
elim: l alpha beta res => /= [_ _ res |i l IH alpha beta res].
  by apply: leqnn.
have [E1|E1] := leqP res _; first by apply: IH.
have {}E1 : eval alpha beta i <= res by case: (eval _ _) E1; case: res.
have [E2|E2] := leqP beta _.
  by apply: leq_trans E1; apply: IH.
have [E3|E3] := leqP _ alpha; first by case: (eval _ _) E1; case: res.
by apply: leq_trans E1; apply: IH.
Qed.

Fixpoint eval_rec3 n t alpha beta b := 
  if ieval t b is some v then v else
  if n is n1.+1 then 
     sflip (process_eval_rec3 (eval_rec3 n1 (flip t)) 
                (sflip beta) (sflip alpha) win (moves t b))
  else draw.

Section ProcessEvalRec3.

Variable alpha : state.
Variable f1 : board -> state.
Variable f2 : state -> state -> board -> state.

Hypothesis f1Ha : forall i (b : state),
  f1 i <= alpha < b -> f2 alpha b i <= alpha.
Hypothesis f1Hb : forall i (b : state),
  alpha < b <= f1 i -> b <= f2 alpha b i.
Hypothesis f1H : forall i (a b : state),
  a < b -> a <= f1 i <= b -> f2 a b i = f1 i.

Lemma process_eval_rec3_correct_a res (beta : state) l :
  alpha < beta -> \smin_(i <- l) f1 i <= alpha ->
  process_eval_rec3 f2 alpha beta res l <= alpha.
Proof.
elim: l res beta => [|i l IH] res beta aLb.
  by rewrite big_nil // => /ge_winE->; apply: le_win.
rewrite big_cons /= => H.
have [E1|E1] := leqP res (f2 _ _ _). 
  have [E2|E2] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    apply: leq_trans (le_process_eval_rec3 _ _ _ _ _) _ => //.
    by apply: leq_trans E1 (f1Ha _); rewrite H.
  rewrite smin_ler in H; last by apply: ltnW.
  by apply: IH.
have [E2|E2] := leqP beta (f2 _ _ _).
  have [E3|E3] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    apply: leq_trans (le_process_eval_rec3 _ _ _ _ _) _ => //.
    by apply: f1Ha; rewrite H.
  rewrite smin_ler in H; last by apply: ltnW.
  by apply: IH.
have [E3|E3] := leqP (f2 _ _ _) alpha => //.
apply: IH => //.
have [E4|E4] := leqP (f1 i) (\smin_(j <- l) f1 j).
  rewrite ltnNge in E3; case/negP: E3.
  apply: f1Ha; rewrite aLb andbT.
  by move: H; rewrite smin_lel.
by move: H; rewrite smin_ler // ltnW.
Qed.

Lemma process_eval_rec3_correct_b (res beta : state) l :
  alpha < beta <= res ->
  beta <= \smin_(i <- l) f1 i ->
  beta <= process_eval_rec3 f2 alpha beta res l.
Proof.
elim: l res beta => /= [| i l IH] res beta /andP[aLb bLr] //.
rewrite big_cons /= => H.
have [E1|E1] := leqP res _.
  apply: IH => //; first by rewrite aLb.
  by apply: leq_trans H (ge_sminr _ _).
have [E2|E2] := leqP beta (f2 _ _ _).
  apply: IH => //; first by rewrite aLb.
  by apply: leq_trans H (ge_sminr _ _).
rewrite ltnNge in E2; case/negP: E2.
apply: f1Hb => //; rewrite aLb /=.
by apply: leq_trans H (ge_sminl _ _).
Qed.

Lemma process_eval_rec3_correct (res beta : state) l :
  alpha < beta -> alpha <= beta <= res ->
  let res1 := \smin_(i <- l) f1 i in
  let res2 := process_eval_rec3 f2 alpha beta res l in
    alpha <= res1 <= beta -> res2 = res1.
Proof.
elim: l res beta => [|i l IH] res beta aLsb /andP[aLb bLr]; lazy zeta.
  rewrite big_nil => /andP[_ /ge_winE rEwin].
  by move: bLr; rewrite rEwin => /ge_winE->.
rewrite big_cons /= => H; have /andP[H1 H2] := H.
have [E1|E1] := leqP res _.
  have [E2|E2] := leqP (\smin_(j <- l) f1 j) (f1 i).
    rewrite smin_ler // in H H1 H2 *.
    by apply: IH => //; rewrite aLb.
  rewrite smin_lel // in H H1 H2 *; try by apply: ltnW.
  rewrite f1H // in E1.
  have f1E : f1 i = beta by apply: sle_antisym => //; apply: leq_trans E1.
  rewrite f1E in E1 E2 H1 H2 *.
  have rE : res = beta by apply: sle_antisym.
  rewrite rE. 
  apply: sle_antisym => //.
    by rewrite le_process_eval_rec3.
  by apply: process_eval_rec3_correct_b (ltnW E2); rewrite aLsb leqnn.
have [E2|E2] := leqP beta _.
  have [E3|E3] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H H1 H2 *.
    rewrite f1H // in E1 E2 *.
    apply: sle_antisym.
      by rewrite le_process_eval_rec3.
    have -> : f1 i = beta by apply: sle_antisym.
    apply: process_eval_rec3_correct_b (leq_trans E2 E3) => //.
    by rewrite aLsb leqnn.
  rewrite (smin_ler (ltnW E3)).
  rewrite smin_ler in H H1 H2; last by apply: ltnW.
  by rewrite IH // aLb.
have [E3|E3] := leqP (f2 _ _ _) alpha => //.
  have [E4|E4] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite (smin_lel E4) in H H1 H2 *.
    by rewrite (f1H aLsb H).
  rewrite (smin_ler (ltnW E4)) in H H1 H2 *.
  have H3 : alpha < f1 i by apply: leq_ltn_trans H1 E4.
  have H4 : alpha <= f1 i by apply: ltnW.
  have [E5|E5] := leqP (f1 i) beta.
    have H4E5 : alpha <= f1 i <= beta by rewrite H4.
    rewrite (f1H aLsb H4E5) in E1 E2 E3 *.
    by rewrite ltnNge in H3; case/negP: H3.
  rewrite ltnNge in E2; case/negP: E2.
  by apply: f1Hb; rewrite // aLsb /= ltnW.
have [E4|E4] := leqP (f1 i) (\smin_(j <- l) f1 j).
  rewrite (smin_lel E4) in H H1 H2 *.
  rewrite (f1H aLsb H) in E1 E2 E3 *.
  apply: sle_antisym; first by rewrite le_process_eval_rec3.
  apply: process_eval_rec3_correct_b E4 => //.
  by rewrite E3 leqnn.
rewrite (smin_ler (ltnW E4)) in H H1 H2 *.
have [E5|E5] := leqP (f1 i) beta.
  have H3 : alpha < f1 i by apply: leq_ltn_trans H1 E4.
  have H4 : alpha <= f1 i by apply: ltnW.
  have H4E5 : alpha <= f1 i <= beta by rewrite H4.
  rewrite (f1H aLsb H4E5) in E1 E2 E3 *.
  rewrite IH //; last by rewrite H1 ltnW.
  by rewrite (ltnW E3) leqnn.
rewrite ltnNge in E2; case/negP: E2.
by apply: f1Hb; rewrite // aLsb ltnW.
Qed.

End ProcessEvalRec3.

Lemma eval_rec3_correct n t (alpha beta : state) b :
  alpha < beta ->
  [/\ 
    eval_rec n t b <= alpha -> eval_rec3 n t alpha beta b <= alpha,
    beta <= eval_rec n t b  -> beta <= eval_rec3 n t alpha beta b &
    alpha <= eval_rec n t b <= beta ->
    eval_rec3 n t alpha beta b = eval_rec n t b].
Proof.
elim: n t alpha beta b => //= n IH t alpha beta b aLb.
case: ieval => //; split.
- rewrite -{1 3}(sflipK alpha) !sflip_le => H.
  apply: process_eval_rec3_correct_b (H).
    move=> i b1 /andP[H1 H2]; have [_ ->// _] := IH (flip t) _ _ i H1.
  by rewrite sflip_lt aLb le_win.
- rewrite -{1 2}(sflipK beta) !sflip_le => H.
  apply: process_eval_rec3_correct_a H => //; last first.
    by rewrite sflip_lt.
  move=> b1 s1 /andP[H1 H2].
  by have [/(_ H1)-> _ _] := (IH (flip t) (sflip beta) s1 b1 H2).
rewrite -{1}(sflipK alpha) -{1}(sflipK beta) !sflip_le => /andP[H1 H2].
congr (sflip _).
apply: process_eval_rec3_correct => //.
- move=> i a1 /andP[H a1L].
  by have [_ /(_ a1L)] := IH (flip t) _ a1 i H.
- move=> i a1 b1 a1Lsb1 /andP[a1Le eLb1].
  have [_ _ ->//]:= IH (flip t) a1 b1 i a1Lsb1.
  by rewrite a1Le.
- by rewrite sflip_lt.
- by rewrite le_win sflip_le ltnW.
by rewrite H2.
Qed. 

Definition eval3 t b := eval_rec3 (depth b) t loss win b.

Lemma eval3_correct t b : eval3 t b = eval t b.
Proof.
have [_ _ H] := eval_rec3_correct (depth b) t b (isT : loss < win).
by apply: H => //; rewrite ge_loss le_win.
Qed.

(* We are trying to add intermediate *)

Inductive estate := eloss | lossdraw | edraw | drawwin | ewin.

Coercion es2n e :=
  match e with 
  | eloss => 1
  | lossdraw => 2 
  | edraw  => 3 
  | drawwin => 4
  | ewin => 5
end.

Implicit Type es : estate.

Definition eqes es1 es2 := (es1 == es2 :> nat).

Lemma eqesP : Equality.axiom eqes.
Proof. by do 2!case; constructor. Qed.

Canonical estate_eqMixin := EqMixin eqesP.
Canonical estate_eqType := Eval hnf in EqType estate estate_eqMixin.

Definition esflip e :=
  match e with 
  | eloss => ewin
  | lossdraw => drawwin 
  | edraw  => edraw
  | drawwin => lossdraw
  | ewin => eloss
end.

Lemma esflipE es1 es2 : (esflip es1 == esflip es2) = (es1 == es2).
Proof. by case: es1; case: es2. Qed.

Definition es2s e :=
  match e with 
  | eloss => Some loss
  | lossdraw => None
  | edraw  => Some draw
  | drawwin => None
  | ewin => Some win
end.

Coercion s2es e :=
  match e with 
  | loss => eloss
  | draw  => edraw
  | win => ewin
end.

Lemma s2esK e : es2s (s2es e) = Some e.
Proof. by case: e. Qed.

Lemma ge_ewinE es : ewin <= es -> es = ewin.
Proof. by case: es. Qed.

Lemma le_ewin es : es <= ewin.
Proof. by case: es. Qed.

Definition esmin es1 es2 := if es1 <= es2 then es1 else es2.

Lemma esminnw es : esmin es ewin = es.
Proof. by case: es. Qed.

Lemma es2ns2esK s : es2n (s2es s) = s2n s.
Proof. by case: s. Qed.

Lemma esle_antisym es1 es2 : es1 <= es2 -> es2 <= es1 -> es1 = es2.
Proof. by case: es1; case: es2. Qed.

Lemma ge_esminl es1 es2 : esmin es1 es2 <= es1.
Proof. by case: es1; case: es2. Qed.

Lemma ge_esminr es1 es2 : esmin es1 es2 <= es2.
Proof. by case: es1; case: es2. Qed.

Lemma esmin_ler es1 es2 : es2 <= es1 -> esmin es1 es2 = es2.
Proof. by case: es1; case: es2. Qed.

Lemma esmin_lel es1 es2 : es1 <= es2 -> esmin es1 es2 = es1.
Proof. by case: es1; case: es2. Qed.

Lemma esflipK : involutive esflip.
Proof. by case. Qed.

Lemma esflip_le es1 es2 : (esflip es1 <= esflip es2) = (es2 <= es1).
Proof. by case: es1; case: es2. Qed.

Lemma esflip_lt es1 es2 : (esflip es1 < esflip es2) = (es2 < es1).
Proof. by case: es1; case: es2. Qed.

Lemma esminwn : left_id ewin esmin.
Proof. by case. Qed.

Lemma s2es_flip s : (sflip s) = esflip s :> estate.
Proof. by case: s. Qed.

Lemma es2n_flip s : s2n (sflip s) = es2n (esflip (s2es s)).
Proof. by case: s. Qed.

Lemma le_elossE es : es <= eloss -> es = eloss.
Proof. by case: es. Qed.

Definition etop e :=
  match e with 
  | eloss => eloss
  | lossdraw => edraw
  | edraw  => edraw
  | drawwin => ewin
  | ewin => ewin
end.

Definition ebot e :=
  match e with 
  | eloss => eloss
  | lossdraw => eloss
  | edraw  => edraw
  | drawwin => edraw
  | ewin => ewin
end.

Definition is_state e :=
  match e with 
  | eloss => true
  | lossdraw => false
  | edraw  => true
  | drawwin => false
  | ewin => true
end.

Lemma is_state_es s : is_state (s2es s).
Proof. by case: s. Qed.

Definition econtained s es := ebot es <= s <= etop es.

Fixpoint process_eval_rec4 (eval :  estate -> estate -> board -> estate) 
                            alpha beta res l : estate :=
  if l is i :: l1 then
    let res1 := eval alpha beta i in
    if res <= res1 then process_eval_rec4 eval alpha beta res l1 else
    (* res1 is good *)
    if beta <= res1 then process_eval_rec4 eval alpha beta res1 l1
    else 
    (* we improve max *)
    if res1 <= alpha then 
      (if res1 is edraw then 
           if l1 is _ :: _ then lossdraw else res1 else res1) (* cut *) else 
        process_eval_rec4 eval alpha res1 res1 l1 
    else res.
  
Lemma le_process_eval_rec4 eval alpha beta res l : 
    process_eval_rec4 eval alpha beta res l <= res.
Proof.
elim: l alpha beta res => /= [_ _ res |i l IH alpha beta res].
  by apply: leqnn.
have [E1|E1] := leqP res _; first by apply: IH.
have {}E1 : eval alpha beta i <= res by case: (eval _ _) E1; case: res.
have [E2|E2] := leqP beta _.
  by apply: leq_trans E1; apply: IH.
have [E3|E3] := leqP _ alpha.
  by case: (eval _ _) E1; case: res; case: (l).
by apply: leq_trans E1; apply: IH.
Qed.

Fixpoint eval_rec4 n t alpha beta b := 
  if ieval t b is some v then s2es v else
  if n is n1.+1 then 
     esflip (process_eval_rec4 (eval_rec4 n1 (flip t)) 
                (esflip beta) (esflip alpha) win (moves t b))
  else edraw.

Section ProcessEvalRec4.

Variable f1 : board -> state.
Variable f2 : estate -> estate -> board -> estate.


(** loss draw                                                                 *)

Hypothesis Hloss_draw_loss : 
  forall i, f1 i = loss -> f2 eloss edraw i = eloss.
Hypothesis Hloss_draw_draw : 
  forall i, f1 i = draw -> edraw <= f2 eloss edraw i <= drawwin.
Hypothesis Hloss_draw_win : 
  forall i, f1 i = win -> drawwin <= f2 eloss edraw i.

Lemma Hloss_draw_ge i : draw <= f1 i -> edraw <= f2 eloss edraw i.
Proof.
case: f1 (@Hloss_draw_draw i) (@Hloss_draw_win i) => //.
  by move=> _ /(_ (refl_equal _)) /(leq_trans _) H _; rewrite H.
by move=> /(_ (refl_equal _)) /andP[].
Qed.

Lemma Hloss_draw_le i : f1 i <= draw -> f2 eloss edraw i <= drawwin.
Proof.
case: f1 (@Hloss_draw_loss i) (@Hloss_draw_draw i) => //.
  by move=> /(_ (refl_equal _))->.
by move=> _ /(_ (refl_equal _)) /andP[].
Qed.

Lemma process_eval_rec4_loss_draw_ge (res : estate) l :
  draw <= res ->
  draw <= \smin_(i <- l) f1 i ->
  draw <= process_eval_rec4 f2 eloss edraw res l.
Proof.
elim: l res => [|i l IH] res; first by rewrite big_nil.
rewrite big_cons [process_eval_rec4 _ _ _ _ _]/= => H1 H2.
have [E1|E1] := leqP res (f2 _ _ _).
  by apply: IH => //; apply: leq_trans H2 (ge_sminr _ _).
rewrite ifT; last first.
  by apply: Hloss_draw_ge; apply: leq_trans H2 (ge_sminl _ _).
apply: IH => //.
  by apply: Hloss_draw_ge; apply: leq_trans H2 (ge_sminl _ _).
by apply: leq_trans H2 (ge_sminr _ _).
Qed.

Lemma process_eval_rec4_loss_draw_le (res : estate) l :
  \smin_(i <- l) f1 i <= draw ->
   process_eval_rec4 f2 eloss edraw res l <= drawwin.
Proof.
elim: l res => [|i l IH] res; first by rewrite big_nil.
rewrite big_cons [process_eval_rec4 _ _ _ _ _]/= => H.
have [E1|E1] := leqP res (f2 _ _ _).
  have [E2|E2] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    apply: leq_trans (le_process_eval_rec4 _ _ _ _ _) _.
    by apply: leq_trans E1 (Hloss_draw_le _).
  rewrite smin_ler // in H; last by apply: ltnW.
  by apply: IH.
have [E2|E2] := leqP edraw (f2 _ _ _).
  have [E3|E3] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    apply: leq_trans (le_process_eval_rec4 _ _ _ _ _) _.
    by apply: leq_trans _ (Hloss_draw_le _).
  rewrite smin_ler // in H; last by apply: ltnW.
  by apply: IH.
have [E3|E3] := leqP (f2 eloss edraw i) eloss.
  by rewrite (le_elossE E3).
apply: leq_trans (le_process_eval_rec4 _ _ _ _ _) _.
by apply: leq_trans (ltnW E2) _.
Qed.

Lemma process_eval_rec4_loss_draw_loss (res : estate) l :
  \smin_(i <- l) f1 i = loss ->
   process_eval_rec4 f2 eloss edraw res l = eloss.
Proof.
elim: l res => [|i l IH] res; first by rewrite big_nil.
rewrite big_cons [process_eval_rec4 _ _ _ _ _]/= => H.
have [E1|E1] := leqP res (f2 _ _ _).
  have [E2|E2] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    apply: le_elossE.
    have -> : res = eloss by apply: le_elossE; rewrite -(Hloss_draw_loss H).
    by apply: le_process_eval_rec4.
  rewrite smin_ler // in H; last by apply: ltnW.
  by apply: IH.
have [E2|E2] := leqP _ (f2 _ _ _).
  have [E3|E3] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    rewrite Hloss_draw_loss //.
    apply: le_elossE.
    by apply: le_process_eval_rec4.
  rewrite smin_ler // in H; last by apply: ltnW.
  by apply: IH.
rewrite Hloss_draw_loss //=.
by case: f1 (@Hloss_draw_draw i) (@Hloss_draw_win i) => // [_|];
   move=> /(_ (refl_equal _)); case: f2 E2.
Qed.

Lemma process_eval_rec4_loss_draw_draw (res : estate) l :
  \smin_(i <- l) f1 i = draw -> draw <= res ->
   draw <= process_eval_rec4 f2 eloss edraw res l <= drawwin.
Proof.
move=> H1 H2.
rewrite process_eval_rec4_loss_draw_ge ?H1 //.
by rewrite process_eval_rec4_loss_draw_le ?H1.
Qed.

Lemma process_eval_rec4_loss_draw_win (res : estate) l :
  \smin_(i <- l) f1 i = win -> drawwin <= res ->
   drawwin <= process_eval_rec4 f2 eloss edraw res l.
Proof.
elim: l res => [|i l IH] res; first by rewrite big_nil.
rewrite big_cons [process_eval_rec4 _ _ _ _ _]/= => H1 H2.
have [H3 H4] : f1 i = win /\ \smin_(j <- l) f1 j = win.
  have [E1|/ltnW E1] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H1 *; split => //.
    by apply: ge_winE; rewrite -{1}H1.
  rewrite smin_ler // in H1 *; split => //.
  by apply: ge_winE; rewrite -{1}H1.
have [E1|E1] := leqP res (f2 _ _ _).
  by apply: IH.
have [E2|E2] := leqP _ (f2 _ _ _).
  apply: IH => //.
  by apply: Hloss_draw_win.
rewrite ifN.
  rewrite ltnNge in E2; case/negP: E2.
  by apply: leq_trans (Hloss_draw_win _).
rewrite -ltnNge.
by apply: leq_trans (Hloss_draw_win _).
Qed.

(** draw win *)

Hypothesis Hdraw_win_win : 
  forall i, f1 i = win -> f2 edraw ewin i = ewin.
Hypothesis Hdraw_win_draw : 
  forall i, f1 i = draw -> lossdraw <= f2 edraw ewin i <= edraw.
Hypothesis Hdraw_win_loss: 
  forall i, f1 i = loss -> f2 edraw ewin i <= lossdraw.

Lemma Hdraw_win_le i : f1 i <= draw -> f2 edraw ewin i <= edraw.
Proof.
case: f1 (@Hdraw_win_loss i) (@Hdraw_win_draw i) => //.
  by move=> /(_ (refl_equal _)) /leq_trans->.
by move=>  _ /(_ (refl_equal _)) /andP[].
Qed.

Lemma Hdraw_win_ge i : draw <= f1 i -> lossdraw <= f2 edraw ewin i.
Proof.
case: f1 (@Hdraw_win_draw i) (@Hdraw_win_win i) => //.
  by move=> _ /(_ (refl_equal _))->.
by move=> /(_ (refl_equal _)) /andP[].
Qed.

Lemma process_eval_rec4_draw_win_le (res : estate) l :
  \smin_(i <- l) f1 i <= draw ->
  process_eval_rec4 f2 edraw ewin res l <= draw.
Proof.
elim: l res => [|i l IH] res; first by rewrite big_nil.
rewrite big_cons [process_eval_rec4 _ _ _ _ _]/= => H.
have [E1|E1] := leqP res (f2 _ _ _).
  have [E2|E2] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    apply: leq_trans (le_process_eval_rec4 _ _ _ _ _) _.
    by apply: leq_trans E1 (Hdraw_win_le _).
  rewrite smin_ler // in H; last by apply: ltnW.
  by apply: IH.
have [E2|E2] := leqP ewin (f2 edraw ewin i).
  have [E3|E3] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    rewrite leqNgt in E2; case/negP: E2.
    by apply: leq_ltn_trans (Hdraw_win_le _) _.
  rewrite smin_ler // in H; last by apply: ltnW.
  by apply: IH.
have [E3|E3] := leqP (f2 _ _ i) draw.
  by case: f2 E3 => //; case: (l).
have [E4|E4] := leqP (f1 i) draw.
  rewrite ltnNge in E3; case/negP: E3.
  by apply: Hdraw_win_le.
rewrite Hdraw_win_win // in E2.
apply: ge_winE.
by case: f1 E4.
Qed.

Lemma process_eval_rec4_draw_win_ge (res : estate) l :
  lossdraw <= res ->
  draw <= \smin_(i <- l) f1 i ->
  lossdraw <= process_eval_rec4 f2 edraw ewin res l.
Proof.
elim: l res => [|i l IH] res; first by rewrite big_nil.
rewrite big_cons [process_eval_rec4 _ _ _ _ _]/= => H1 H2.
have [E1|E1] := leqP res (f2 _ _ _).
  apply: IH => //.
  by apply: leq_trans H2 (ge_sminr _ _).
have [E2|E2] := leqP ewin (f2 _ _ _).
  apply: IH => //.
    apply: Hdraw_win_ge.
    by apply: leq_trans H2 (ge_sminl _ _).
  by apply: leq_trans H2 (ge_sminr _ _).
have [E3|E3] := leqP (f2 edraw ewin i) edraw.
  have : lossdraw <= (f2 edraw ewin i).
    apply: Hdraw_win_ge (leq_trans H2 (ge_sminl _ _)).
  by case: f2 => //=; case: (l).
have [E4|E4] := leqP (f1 i) draw.
  rewrite ltnNge in E3; case/negP: E3.
  by apply: Hdraw_win_le.
rewrite Hdraw_win_win // in E2.
apply: ge_winE.
by case: f1 E4.
Qed.

Lemma process_eval_rec4_draw_win_win (res : estate) l :
  res = win ->
  \smin_(i <- l) f1 i = win ->
   process_eval_rec4 f2 edraw ewin res l = ewin.
Proof.
elim: l res => [|i l IH] res; first by rewrite big_nil.
rewrite big_cons [process_eval_rec4 _ _ _ _ _]/= => H1 H2.
have [H3 H4] : f1 i = win /\ \smin_(j <- l) f1 j = win.
  have [E1|/ltnW E1] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H2; split => //.
    by apply: ge_winE; rewrite -{1}H2.
  rewrite smin_ler // in H2; split => //.
  by apply: ge_winE; rewrite -{1}H2.
rewrite Hdraw_win_win // H1 /=.
by apply: IH.
Qed.

Lemma process_eval_rec4_draw_win_draw (res : estate) l :
  \smin_(i <- l) f1 i = draw -> lossdraw <= res ->
   lossdraw <= process_eval_rec4 f2 edraw ewin res l <= edraw.
Proof.
move=> H1 H2.
rewrite process_eval_rec4_draw_win_ge ?H1 //.
by rewrite process_eval_rec4_draw_win_le ?H1.
Qed.

Lemma process_eval_rec4_draw_win_loss (res : estate) l :
  \smin_(i <- l) f1 i = loss ->
   process_eval_rec4 f2 edraw ewin res l <= lossdraw.
Proof.
elim: l res => [|i l IH] res; first by rewrite big_nil.
rewrite big_cons [process_eval_rec4 _ _ _ _ _]/= => H.
have [E1|E1] := leqP res (f2 _ _ _).
  have [E2|E2] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    apply: leq_trans (le_process_eval_rec4 _ _ _ _ _) _.
    apply: leq_trans E1 _.
    by apply: Hdraw_win_loss.
  rewrite smin_ler // in H; last by apply: ltnW.
  by apply: IH.
have [E2|E2] := leqP ewin (f2 _ _ _).
  have [E3|E3] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    have := Hdraw_win_loss H.
    by rewrite leqNgt (leq_trans _ E2).
  rewrite smin_ler // in H; last by apply: ltnW.
  by apply: IH.
have [E3|E3] := leqP (f1 i) (\smin_(j <- l) f1 j).
  rewrite smin_lel // in H.
  by case: f2 (Hdraw_win_loss H).
rewrite smin_ler // in H; last by apply: ltnW.
have [E4|E4] := leqP (f2 _ _ _) edraw.
  have : lossdraw <= f2 edraw ewin i.
    apply: Hdraw_win_ge.
    by move: E3; rewrite H; case: f1.
  case: f2 E4 => //=.
  by case: (l) H => //; rewrite big_nil.
move: E3 E2; rewrite H.
case: f1 (@Hdraw_win_draw i) (@Hdraw_win_win i) => //.
  by move=> _ -> //.
move=> /(_ (refl_equal _)).
by rewrite [_ <= edraw]leqNgt E4 andbF.
Qed.

(* loss win *)

Hypothesis Hloss_win : forall i, f2 eloss ewin i = f1 i.

Lemma process_eval_rec4_loss_win_lt (a res : estate) l :
  a <= res ->
  a < \smin_(i <- l) f1 i -> 
  a <= process_eval_rec4 f2 eloss ewin res l .
Proof.
elim: l res => [|i l IH] res aLr; first by rewrite big_nil.
rewrite big_cons => /= aLs; rewrite Hloss_win.
have [E1|E1] := leqP res _.
  apply: IH => //.
  by apply: leq_trans aLs (ge_sminr _ _).
have [E2|E2] := leqP ewin _.
  apply: IH => //.
    by rewrite (ge_ewinE E2) // le_ewin.
  by apply: leq_trans aLs (ge_sminr _ _).
rewrite ifN; last first.
  rewrite -ltnNge es2ns2esK.
  apply: leq_ltn_trans _ (leq_trans aLs (ge_sminl _ _)).
  by case: (a).
have [E3|E3] := leqP (f1 i) (\smin_(j <- l) f1 j).
  rewrite smin_lel // in aLs *.
  have H : f1 i = draw.
    by case: f1 E2 E3 aLs => //; case: (\smin_(_ <- _) _) => //; case: (a).
  rewrite H in E1 E3 aLs *.
  apply: leq_trans (process_eval_rec4_loss_draw_ge _ _) =>//. 
  by apply: ltnW.
rewrite smin_ler // in aLs *; last by apply: ltnW.
suff -> : f1 i = win.
  by apply: IH => //; apply: le_ewin.
by case: f1 E3 aLs => //; case: (\smin_(_ <- _) _) => //; case: (a).
Qed.


Lemma process_eval_rec4_loss_win (res : estate) l :
  \smin_(i <- l) f1 i <= res ->
  process_eval_rec4 f2 eloss ewin res l = \smin_(i <- l) f1 i.
Proof.
elim: l res => [|i l IH] res; first by rewrite big_nil; apply: ge_ewinE.
rewrite big_cons [process_eval_rec4 _ _ _ _ _]/= => H.
rewrite Hloss_win !es2ns2esK.
have [E1|E1] := leqP res (f1 i).
  have [E2|E2] := leqP (\smin_(j <- l) f1 j) (f1 i).
    rewrite smin_ler // in H *.
    by apply: IH.
  rewrite smin_lel // in H *; last by apply: ltnW.
  apply: esle_antisym.
    rewrite es2ns2esK.
    apply: leq_trans E1.
    by apply: le_process_eval_rec4.
  by apply: process_eval_rec4_loss_win_lt; rewrite es2ns2esK.
rewrite ifN; last first.
  by rewrite -leqNgt -ltnS (leq_trans E1) // le_ewin.
have [E2|E2] := leqP (f1 i) loss.
  by rewrite (le_lossE E2) /= sminln.
have H3 : f1 i = draw.
  apply: sle_antisym.
    by case: f1 E1; case: (res).
  by case: f1 E2.
rewrite H3 in H E1 *.
have [E3|E3] := leqP draw (\smin_(j <- l) f1 j).
  rewrite smin_lel // in H *.
  apply: esle_antisym.
    by apply: le_process_eval_rec4.
  by apply: process_eval_rec4_loss_draw_ge.
suff H4 : \smin_(j <- l) f1 j = loss.
  rewrite H4.
  by apply: process_eval_rec4_loss_draw_loss.
apply: sle_antisym.
  by case: (\smin_(_ <- _) _) E3.
by apply: ge_loss.
Qed.

End ProcessEvalRec4.

Lemma eval_rec4_correct n t i :
  let f1 := eval_rec n t in
  let f2 := eval_rec4 n t in
  [/\ 
    [/\
      f1 i = loss -> f2 eloss edraw i = eloss,
      f1 i = draw -> edraw <= f2 eloss edraw i <= drawwin &
      f1 i = win -> drawwin <= f2 eloss edraw i],
    [/\
      f1 i = win -> f2 edraw ewin i = ewin,
      f1 i = draw -> lossdraw <= f2 edraw ewin i <= draw &
      f1 i = loss -> f2 edraw ewin i <= lossdraw] &
      f2 eloss ewin i = f1 i].
Proof.
elim: n t i => /= [|n IH] t i;
  case: ieval => //; try by case.
repeat split => //.
- rewrite -(sflipK loss) => /sflip_inj H.
  rewrite -(esflipK eloss); congr esflip.
  apply: process_eval_rec4_draw_win_win H => // i1.
  by case:  (IH (flip t) i1) => _ [].
- rewrite -(sflipK draw) => /sflip_inj H.
  rewrite -[3]/(es2n (esflip edraw)) -[4]/(es2n (esflip lossdraw)).
  rewrite !esflip_le andbC.
  by apply: process_eval_rec4_draw_win_draw H _ => // i1;
     case:  (IH (flip t) i1) => _ [].
- rewrite -(sflipK win) => /sflip_inj H.
  rewrite -[3]/(es2n (esflip edraw)) !esflip_lt.
  by apply: process_eval_rec4_draw_win_loss H => // i1;
     case:  (IH (flip t) i1) => _ [].
- rewrite -(sflipK win) => /sflip_inj H.
  rewrite -[ewin]/(esflip eloss); congr esflip.
  by apply: process_eval_rec4_loss_draw_loss H => i1;
     case:  (IH (flip t) i1) => [] [].
- rewrite -(sflipK draw) => /sflip_inj H.
  rewrite -[1]/(es2n (esflip ewin)) -[3]/(es2n (esflip edraw)).
  rewrite esflip_lt esflip_le andbC.
  by apply: process_eval_rec4_loss_draw_draw H _ => // i1;
     case:  (IH (flip t) i1) => [] [].
- rewrite -(sflipK loss) => /sflip_inj H.
  rewrite -[2]/(es2n (esflip drawwin)) esflip_le.
  by apply: process_eval_rec4_loss_draw_win H _ => // i1;
     case:  (IH (flip t) i1) => [] [].
rewrite s2es_flip; congr esflip.
apply: process_eval_rec4_loss_win => //.
- by move=> i1; case: (IH (flip t) i1) => [] [].
- by move=> i1; case: (IH (flip t) i1) => [] [].
- by move=> i1; case: (IH (flip t) i1) => [] [].
- by move=> i1; case: (IH (flip t) i1) => [] [].
by rewrite -es2ns2esK; apply: le_ewin.
Qed.

End Board.

