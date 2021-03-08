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

Lemma le_antisym s1 s2 : s1 <= s2 -> s2 <= s1 -> s1 = s2.
Proof. by case: s1; case: s2. Qed.

Lemma sflip_le s1 s2 : (sflip s1 <= sflip s2) = (s2 <= s1).
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
     sflip (process_eval_rec1 (eval_rec n1 (flip t)) win (moves t b))
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
case: ieval => //.
have /process_eval_rec1_correct : 
  win = \smin_(i <- [::]) (eval_rec n (flip t)) i by rewrite big_nil.
by move=> /(_ (moves t b)); rewrite cats0 => ->.
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
have [E1|E1] := boolP (res <= _); first by apply: IH.
have {}E1 : eval alpha beta i <= res by case: (eval _ _) E1; case: res.
have [E2|E2] := boolP (beta <= _).
  by apply: leq_trans E1; apply: IH.
have [E3|E3] := boolP (_ <= alpha); first by case: (eval _ _) E1; case: res.
by apply: leq_trans E1; apply: IH.
Qed.

Fixpoint eval_rec3 n t alpha beta b := 
  if ieval t b is some v then v else
  if n is n1.+1 then 
     sflip (process_eval_rec3 (eval_rec3 n1 (flip t)) 
                (sflip beta) (sflip alpha) win (moves t b))
  else draw.

Lemma process_eval_rec3_correct_a (f1 : _ -> state) (f2 : _ -> _ -> _ -> state) 
                                   res (alpha beta : state) l :
  alpha <= beta ->
  (forall i (b : state),  alpha <= b -> 
      f1 i <= alpha -> f2 alpha b i <= alpha) ->
  \smin_(i <- l) f1 i <= alpha ->
  process_eval_rec3 f2 alpha beta res l <= alpha.
Proof.
elim: l res beta => [|i l IH] res beta aLb Hf.
  by rewrite big_nil // => /ge_winE->; apply: le_win.
rewrite big_cons /= => H.
have [E1|E1] := leqP res (f2 _ _ _). 
  have [E2|E2] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    apply: leq_trans (le_process_eval_rec3 _ _ _ _ _) _ => //.
    by apply: leq_trans E1 (Hf _ _ _ _).
  rewrite smin_ler in H; last by apply: ltnW.
  by apply: IH.
have [E2|E2] := leqP beta (f2 _ _ _).
  have [E3|E3] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H.
    apply: leq_trans (le_process_eval_rec3 _ _ _ _ _) _ => //.
    by apply: Hf.
  rewrite smin_ler in H; last by apply: ltnW.
  by apply: IH.
have [E3|E3] := leqP (f2 _ _ _) alpha => //.
apply: IH => //; first by apply: ltnW.
have [E4|E4] := leqP (f1 i) (\smin_(j <- l) f1 j).
  rewrite ltnNge in E3; case/negP: E3.
  by apply: Hf => //; move: H; rewrite smin_lel //.
by move: H; rewrite smin_ler // ltnW.
Qed.

Lemma process_eval_rec3_correct_b (f1 : _ -> state) (f2 : _ -> _ -> _ -> state)
                                (res alpha beta : state) l :
  alpha <= beta ->
  (forall i (b : state),  alpha <= b -> b <= f1 i -> b <= f2 alpha b i) ->
  beta <= \smin_(i <- l) f1 i ->
  smin res beta <= process_eval_rec3 f2 alpha beta res l.
Proof.
elim: l res beta => /= [| i l IH] res beta aLb Hf.
  by move=> _; apply: ge_sminl.
rewrite big_cons /= => H.
have [E1|E1] := leqP res _.
  apply: IH => //.
  by apply: leq_trans H (ge_sminr _ _).
have [E2|E2] := leqP beta (f2 _ _ _).
  rewrite smin_ler; last by apply: leq_trans E2 (ltnW _).
  rewrite -{1}(smin_ler E2).
  apply: IH => //.
  by apply: leq_trans H (ge_sminr _ _).
rewrite ltnNge in E2; case/negP: E2.
apply: Hf => //.
by apply: leq_trans H (ge_sminl _ _).
Qed.

Lemma process_eval_rec3_correct (f1 : _ -> state) (f2 : _ -> _ -> _ -> state)
                                (res alpha beta : state) l :
  (forall i (a b : state) , a <= b -> f1 i <= a -> f2 a b i <= a) ->
  (forall i (a b : state) , a <= b -> b <= f1 i -> b <= f2 a b i) ->
  (forall i (a b : state),
     a <= f1 i <= b -> f2 a b i = f1 i) ->
  alpha <= beta ->
  let res1 := \smin_(i <- l) f1 i in
  let res2 := process_eval_rec3 f2 alpha beta res l in
    alpha <= res1 <= beta -> res2 = smin res res1.
Proof.
move=> Hf1 Hf2 Hf3.
elim: l res beta => [|i l IH] res beta aLb; lazy zeta.
  by rewrite big_nil sminnw.
rewrite big_cons /= => H; have /andP[H1 H2] := H.
have [E1|E1] := leqP res _.
  have [E2|E2] := leqP (\smin_(j <- l) f1 j) (f1 i).
    rewrite smin_ler // in H H1 H2 *.
    by apply: IH.
  rewrite smin_lel // in H H1 H2 *; try by apply: ltnW.
  rewrite Hf3 // in E1.
  rewrite smin_lel //.
  have [E3|E3] := leqP (\smin_(j <- l) f1 j) beta.
    rewrite IH //; last first.
      by rewrite E3 andbT; apply: leq_trans (ltnW E2).
    by rewrite !smin_lel // (leq_trans _ (ltnW E2)).
  apply: le_antisym => //.
    by rewrite le_process_eval_rec3.
  rewrite -{1}(smin_lel (leq_trans E1 H2)).  
  apply: process_eval_rec3_correct_b (ltnW E3) => //.
  by move=> *; apply: Hf2.
have [E2|E2] := leqP beta _.
  have [E3|E3] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite smin_lel // in H H1 H2 *.
    rewrite Hf3 // in E1 E2 *.
    rewrite smin_ler; last by apply: ltnW.
    have [E4|E4] := leqP (\smin_(j <- l) f1 j) beta.
      rewrite IH //; first by apply: smin_lel.
      by rewrite E4 andbT; apply: leq_trans E3.
    apply: le_antisym.
      by rewrite le_process_eval_rec3.
    have -> : f1 i = beta by apply: le_antisym.
    rewrite -{1}(smin_lel (leqnn beta)).
    apply: process_eval_rec3_correct_b (ltnW E4) => //.
    by move=> *; apply: Hf2.
  rewrite (smin_ler (ltnW E3)).
  rewrite smin_ler in H H1 H2; last by apply: ltnW.
  rewrite IH // !smin_ler //.
    by apply: leq_trans H2 (leq_trans E2 (ltnW _)).
  by apply: leq_trans H2 _.
have [E3|E3] := leqP (f2 _ _ _) alpha => //.
  have [E4|E4] := leqP (f1 i) (\smin_(j <- l) f1 j).
    rewrite (smin_lel E4) in H H1 H2 *.
    rewrite (Hf3 _ _ _ H) in E1 E2 E3 *.
    by rewrite smin_ler // ltnW.
  rewrite (smin_ler (ltnW E4)) in H H1 H2 *.
  have H3 : alpha < f1 i by apply: leq_ltn_trans H1 E4.
  have H4 : alpha <= f1 i by apply: ltnW.
  have [E5|E5] := leqP (f1 i) beta.
    have H4E5 : alpha <= f1 i <= beta by rewrite H4.
    rewrite (Hf3 _ _ _ H4E5) in E1 E2 E3 *.
    by rewrite ltnNge in H3; case/negP: H3.
  rewrite ltnNge in E2; case/negP: E2.
  by apply/Hf2/ltnW.
have [E4|E4] := leqP (f1 i) (\smin_(j <- l) f1 j).
  rewrite (smin_lel E4) in H H1 H2 *.
  rewrite (Hf3 _ _ _ H) in E1 E2 E3 *.
  rewrite smin_ler; last by apply: ltnW.
  apply: le_antisym; first by rewrite le_process_eval_rec3.
  rewrite -{1}(smin_ler (leqnn (f1 i))).
  apply: process_eval_rec3_correct_b E4 => //.
  by move=> *; apply: Hf2.
rewrite (smin_ler (ltnW E4)) in H H1 H2 *.
have [E5|E5] := leqP (f1 i) beta.
  have H3 : alpha < f1 i by apply: leq_ltn_trans H1 E4.
  have H4 : alpha <= f1 i by apply: ltnW.
  have H4E5 : alpha <= f1 i <= beta by rewrite H4.
  rewrite (Hf3 _ _ _ H4E5) in E1 E2 E3 *.
  rewrite IH //; last by rewrite H1 ltnW.
  rewrite !smin_ler //; last by apply: ltnW.
  by apply: ltnW; apply: ltn_trans E1.
rewrite ltnNge in E2; case/negP: E2.
by apply/Hf2/ltnW.
Qed.

Lemma eval_rec3_correct n t (alpha beta : state) b :
  alpha <= beta ->
  [/\ 
    eval_rec n t b <= alpha -> eval_rec3 n t alpha beta b <= alpha,
    beta <= eval_rec n t b  -> beta <= eval_rec3 n t alpha beta b &
    alpha <= eval_rec n t b -> eval_rec n t b <= beta ->
    eval_rec3 n t alpha beta b = eval_rec n t b].
Proof.
elim: n t alpha beta b => //= n IH t alpha beta b aLb.
case: ieval => //; split.
- rewrite -{1 3}(sflipK alpha) !sflip_le => H.
  rewrite -{1}[sflip alpha]sminwn.
  apply: process_eval_rec3_correct_b H.
    by rewrite sflip_le.
  move=> b1 s1 H1 H2.
  by have [_ /(_ H2)-> _] := (IH (flip t) (sflip beta) s1 b1 H1).
- rewrite -{1 2}(sflipK beta) !sflip_le => H.
  apply: process_eval_rec3_correct_a H => //.
    by rewrite sflip_le.
  move=> b1 s1 H1 H2.
  by have [/(_ H2)-> _ _] := (IH (flip t) (sflip beta) s1 b1 H1).
rewrite -{1}(sflipK alpha) -{1}(sflipK beta) !sflip_le => H1 H2.
congr (sflip _).
rewrite -[RHS]sminwn.
apply: process_eval_rec3_correct => //.
- move=> i a1 b1 a1Lb1.
  by have [] := IH (flip t) a1 b1 i a1Lb1.
- move=> i a1 b1 a1Lb1.
  by have [] := IH (flip t) a1 b1 i a1Lb1.
- move=> i a1 b1 /andP[aL bL].
  by have [_ _ ->//]:= IH (flip t) a1 b1 i (leq_trans aL bL).
- by rewrite sflip_le.
by rewrite H2.
Qed. 

Definition eval3 t b := eval_rec3 (depth b) t loss win b.

Lemma eval3_correct t b : eval3 t b = eval t b.
Proof.
have [_ _ H] := eval_rec3_correct (depth b) t b (isT : loss <= win).
apply: H => //; first by apply: ge_loss.
by apply: le_win.
Qed.


End Board.

