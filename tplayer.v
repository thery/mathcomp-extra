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

Inductive state := win | lost | draw.

Definition eqs s1 s2 := 
  match s1 with
  | win => if s2 is win then true else false
  | draw => if s2 is draw then true else false
  | lost => if s2 is lost then true else false
  end.

Lemma eqsP : Equality.axiom eqs.
Proof. by do 2!case; constructor. Qed.

Canonical state_eqMixin := EqMixin eqsP.
Canonical state_eqType := Eval hnf in EqType state state_eqMixin.


Definition smin s1 s2 := 
  match s1 with 
  | win => s2
  | lost => lost 
  | draw  => if s2 is win then draw else s2 
  end.

Lemma sminC : commutative smin.
Proof. by do 2 case. Qed.

Lemma sminA : associative smin.
Proof. by do 3 case. Qed.

Lemma sminwn : left_id win smin.
Proof. by case. Qed.
Lemma sminnw : right_id win smin.
Proof. by case. Qed.

Lemma sminln : left_zero lost smin.
Proof. by case. Qed.
Lemma sminnl : right_zero lost smin.
Proof. by case. Qed.

Canonical smin_monoid := Monoid.Law sminA sminwn sminnw.
Canonical smin_comoid := Monoid.ComLaw sminC.

Definition smax s1 s2 := 
  match s1 with 
  | lost => s2
  | win => win 
  | draw  => if s2 is lost then draw else s2 
  end.

Lemma smaxC : commutative smax.
Proof. by do 2 case. Qed.

Lemma smaxA : associative smax.
Proof. by do 3 case. Qed.

Lemma smaxln : left_id lost smax.
Proof. by case. Qed.
Lemma smaxnl : right_id lost smax.
Proof. by case. Qed.

Lemma smaxwn : left_zero win smax.
Proof. by case. Qed.
Lemma smaxnw : right_zero win smax.
Proof. by case. Qed.

Canonical smax_monoid := Monoid.Law smaxA smaxln smaxnl.
Canonical smax_comoid := Monoid.ComLaw smaxC.

Definition osmin s1 s2 := 
  if s1 is some v1 then
    if s2 is some v2 then some (smin v1 v2)
    else if v1 is lost then s1 else None
  else 
  if s2 is some lost then s2 else None.

Lemma osminC : commutative osmin.
Proof. by do 2 case => [[]|]. Qed.

Lemma osminA : associative osmin.
Proof. by do 3 case => [[]|]. Qed.

Lemma osminln : left_id (some win) osmin.
Proof. by case => [[]|]. Qed.
Lemma osminnl : right_id (some win) osmin.
Proof. by case => [[]|]. Qed.

Lemma osminwn : left_zero (some lost) osmin.
Proof. by case => [[]|]. Qed.
Lemma osminnw : right_zero (some lost) osmin.
Proof. by case => [[]|]. Qed.

Canonical osmin_monoid := Monoid.Law osminA osminln osminnl.
Canonical osmin_comoid := Monoid.ComLaw osminC.

Notation "\smin_ ( i <- l ) F" := (\big[smin/win]_(i <- l) F)
 (at level 41, F at level 41, i, l at level 50,
  format "\smin_ ( i  <-  l )  F").
Notation "\osmin_ ( i <- l ) F" := (\big[osmin/some win]_(i <- l) F)
 (at level 41, F at level 41, i, l at level 50,
  format "\osmin_ ( i  <-  l )  F").

Definition osmax s1 s2 := 
  if s1 is some v1 then
    if s2 is some v2 then some (smax v1 v2)
    else if v1 is win then s1 else None
  else 
  if s2 is some win then s2 else None.

Lemma osmaxC : commutative osmax.
Proof. by do 2 case => [[]|]. Qed.

Lemma osmaxA : associative osmax.
Proof. by do 3 case => [[]|]. Qed.

Lemma osmaxln : left_id (some lost) osmax.
Proof. by case => [[]|]. Qed.
Lemma osmaxnl : right_id (some lost) osmax.
Proof. by case => [[]|]. Qed.

Lemma osmaxwn : left_zero (some win) osmax.
Proof. by case => [[]|]. Qed.
Lemma osmaxnw : right_zero (some win) osmax.
Proof. by case => [[]|]. Qed.

Canonical osmax_monoid := Monoid.Law osmaxA osmaxln osmaxnl.
Canonical osmax_comoid := Monoid.ComLaw osmaxC.

Notation "\smax_ ( i <- l ) F" := (\big[smax/lost]_(i <- l) F)
 (at level 41, F at level 41, i, l at level 50,
  format "\smax_ ( i  <-  l )  F").
Notation "\osmax_ ( i <- l ) F" := (\big[osmax/some lost]_(i <- l) F)
 (at level 41, F at level 41, i, l at level 50,
  format "\osmax_ ( i  <-  l )  F").

Definition sflip x := 
  if x is win then lost else if x is lost then win else draw.

Lemma sflipK : involutive sflip.
Proof. by case. Qed.

Lemma sflip_max s1 s2 : sflip (smax s1 s2) = smin (sflip s1) (sflip s2).
Proof. by case: s1; case: s2. Qed.

Lemma sflip_min s1 s2 : sflip (smin s1 s2) = smax (sflip s1) (sflip s2).
Proof. by case: s1; case: s2. Qed.

Definition osflip := omap sflip.

Lemma osflip_max s1 s2 : osflip (osmax s1 s2) = osmin (osflip s1) (osflip s2).
Proof.  by case: s1 => [[]|]; case: s2 => [[]|]. Qed.

Lemma osflip_min s1 s2 : osflip (osmin s1 s2) = osmax (osflip s1) (osflip s2).
Proof.  by case: s1 => [[]|]; case: s2 => [[]|]. Qed.

Definition sle := [rel x y | 
  match x with 
  | lost => true 
  | draw => if y is lost then false else true
  | win => if y is win then true else false 
  end].
Notation " a <= b " := (sle a b).

Lemma sle_refl : reflexive sle.
Proof. by case. Qed.

Lemma sle_trans : transitive sle.
Proof. by do 3 case. Qed.

Lemma sle_antisym : antisymmetric sle.
Proof. by do 2 case. Qed.

Lemma sge_minr s1 s2 : smin s1 s2 <= s2.
Proof. by case: s1; case: s2. Qed.

Lemma sge_minl s1 s2 : smin s1 s2 <= s1.
Proof. by case: s1; case: s2. Qed.

Lemma sle_maxr s1 s2 : s2 <= smax s1 s2.
Proof. by case: s1; case: s2. Qed.

Lemma sle_maxl s1 s2 : s1 <= smax s1 s2.
Proof. by case: s1; case: s2. Qed.

Variable ieval : turn -> board -> option state.

Parameter liveness : forall t b, (ieval t b == None) = (moves t b != nil).

Fixpoint neval n t b :=
   if ieval t b is some v then some v else
   if n is n1.+1 then 
     let t1 := flip t in
     osflip (\osmin_(i <- moves t b) neval n1 t1 i)
   else None.

Lemma nevalE n t b : 
  neval n t b =
   if ieval t b is some v then some v else
   if n is n1.+1 then 
     let t1 := flip t in
     osflip (\osmin_(i <- moves t b) neval n1 t1 i)
   else None.
Proof. by case: n. Qed.

Lemma nevalS n t b v : 
  neval n t b = some v -> neval n.+1 t b = some v.
Proof.
elim: n t b v => [|n IH] t b v.
  by rewrite /=; case: ieval.
rewrite !nevalE; case: ieval => //.
elim: moves v => [|b1 bs IH1] v; first by rewrite  /= !big_nil.
lazy zeta in IH1 |- *; rewrite !big_cons !osflip_min.
case E1 : neval => [v1|];
  case E2 : (\osmin_(_ <- _) _)  => [v2|]; rewrite ?(IH _ _ _ E1) //.
- by rewrite (IH1 (sflip v2)) // E2.
- by case: (v1) => //=; case: osflip.
rewrite (IH1 (sflip v2)) ?E2 //.
by case: (v2) => //=; case: osflip => //= a; case: a; case: (v).
Qed.

Lemma neval_stable m n t b v : (m <= n)%N ->
  neval m t b = some v -> neval n t b = some v.
Proof.
move=> /subnK<-; elim: (_ - _) {-2}m => // {m}k IH m H.
by rewrite addSnnS IH // (nevalS H).
Qed.

Definition peval t b v := exists n, neval n t b = some v.

Lemma peval_fun t b v1 v2 : peval t b v1 -> peval t b v2 -> v1 = v2.   
Proof.
case => n1 Hn1 [n2 Hn2].
wlog H : n1 n2 v1 v2 Hn1 Hn2 / (n1 <= n2)%N => [H|].
  have [n1Ln2|n2Ln1] := leqP n1 n2; first by apply: H n1Ln2.
  by apply: sym_equal; apply: H Hn2 Hn1 _; apply/ltnW.
by rewrite (neval_stable H Hn1) in Hn2; case: Hn2.
Qed.

Lemma i_peval t b v : ieval t b = some v -> peval t b v.
Proof. by move=> H; exists 0; rewrite /= H. Qed.

Lemma osmaxE s1 s2 s3 : (osmax s1 s2 == s3) -> ((s1 == s3) || (s2 == s3)).
Proof.
by case E1 : s1 => [[]|]; case E2 : s2 => [[]|]; case E3 : s3 => [[]|].
Qed.

(* we get a maximal *)
Lemma le_peval t b1 b2 v1 v2 :
  b2 \in moves t b1 -> peval t b1 v1 -> peval (flip t) b2 v2 -> sflip v2 <= v1.
Proof.
move=> b2I [n1 n1H] [n2 n2H].
have n2H1 := neval_stable (leq_maxr n1 _) n2H.
have := nevalS (neval_stable (leq_maxl _ n2) n1H).
rewrite nevalE (_ : ieval t b1 = None); last first.
  by apply/eqP; rewrite liveness; case: moves b2I.
lazy zeta.
elim: moves {n1H}v1 b2I => // b3 bs IH v1; rewrite in_cons => /orP[/eqP<-| /IH];
    rewrite big_cons osflip_min.
  rewrite n2H1.
  by case: (v1); case: (v2) => //=; case: osflip => // [[]].
case: osflip => [s sH sH1|_]; last first.
  by case: osflip => // [[]] // [<-]; case: (v2).
apply: sle_trans (_ : s <= _) => //; first by apply: sH.
case: osflip sH1; last by case: (s); case: (v1).
by case; case: (s) ; case: (v1).
Qed.


(* and the maximum is reached in the sons *)
Lemma peval_next t b v : 
  ieval t b = None -> peval t b v ->
  exists2 b1, b1 \in moves t b & peval (flip t) b1 (sflip v).
Proof.
(move=> H [[|n]]; rewrite nevalE) => [|]; rewrite H //=.
have := liveness t b; rewrite H eqxx => /(@sym_equal _ _ _) /idP.
elim: moves => //= b1 [|b2 l].
  rewrite big_cons ?big_nil.
  rewrite osminnl => _ _ H1; exists b1; first by rewrite in_cons eqxx.
  by exists n; case: neval H1 => //= a [<-]; rewrite sflipK.
move => /(_ isT) IH _; rewrite big_cons osflip_min.
move=> /eqP/osmaxE/orP[] /eqP H1.
  exists b1; first by rewrite in_cons eqxx.
  by exists n; case: neval H1 => //= v1 [<-]; rewrite sflipK.
case: (IH H1) => b3 b3I pevalH; exists b3 => //.
by rewrite in_cons b3I orbT.
Qed.

(* inversion theorem for win *)
Lemma peval_win t b1 b2 :
  b2 \in moves t b1 -> peval (flip t) b2 lost -> peval t b1 win.
Proof.
move=> b2I [n H].
have iH : ieval t b1 = None.
  case: ieval (liveness t b1) b2I => // v /(@sym_equal _ _ _) /negbT.
  by rewrite negbK => /eqP->.
exists n.+1; rewrite nevalE iH /=.
elim: moves b2I => // b3 bs IH.
rewrite big_cons in_cons osflip_min => /orP[/eqP<-|/IH->].
  by rewrite H osmaxwn.
by rewrite osmaxnw.
Qed.

(* inversion theorem for lost *)
Lemma peval_lost t b1 :
  ieval t b1 = None -> 
  (forall b, b \in moves t b1 -> peval (flip t) b win) -> 
  peval t b1 lost.
Proof.
move=> iH lH.
have [n H] : exists n, 
            forall b2, b2 \in moves t b1 -> neval n (flip t) b2 = Some win.
  elim: moves lH => [|b3 bs IH] lH; first by exists 0.
  have [n1 b3H] : peval (flip t) b3 win by apply: lH; rewrite in_cons eqxx.
  case: IH => [b bH | n2 n2H]; first by apply: lH; rewrite in_cons bH orbT.
  exists (maxn n1 n2) => b2; rewrite in_cons => /orP[/eqP->|b2H].
    apply: neval_stable b3H.
    by apply: leq_maxl.
  apply: neval_stable (n2H _ _) => //.
  by apply: leq_maxr.
exists n.+1.
rewrite nevalE iH /=.
elim: moves H => [H | b3 bs IH H]; first by rewrite big_nil.
rewrite big_cons osflip_min H ?in_cons ?eqxx // IH // => b4 b2Ibs.
by apply: H; rewrite in_cons b2Ibs orbT.
Qed.

(* Inversion theorem for draw *)
Lemma peval_draw t b1 b2 :
  b2 \in moves t b1 -> peval (flip t) b2 draw -> 
  (forall b, b \in moves t b1 -> 
             peval (flip t) b draw \/ peval (flip t) b win) -> 
  peval t b1 draw.
Proof.
move=> b2Im [n2 n2H] lH.
have iH : ieval t b1 = None.
  by apply/eqP; rewrite liveness; case: moves b2Im.
have [n H] : exists n, 
            forall b2, b2 \in moves t b1 -> 
                   neval n (flip t) b2 = Some draw \/ 
                   neval n (flip t) b2 = Some win.
  elim: moves lH => [|b3 bs IH] lH; first by exists 0.
  have [[n1 b3H] | [n1 b3H]] : peval (flip t) b3 draw \/ peval (flip t) b3 win.
  - by apply: lH; rewrite in_cons eqxx.
  - case: IH => [b bH | n3 n3H].
      by apply: lH; rewrite in_cons bH orbT.
    exists (maxn n1 n3) => b4.
    rewrite in_cons => /orP[/eqP->|/n3H[b4H|b4H]].
    - left; apply: neval_stable b3H.
      by apply: leq_maxl.
    - left; apply: neval_stable b4H.
      by apply: leq_maxr.
    right; apply: neval_stable b4H.
    by apply: leq_maxr.
  case: IH => [b bH | n3 n3H].
    by apply: lH; rewrite in_cons bH orbT.
  exists (maxn n1 n3) => b4.
  rewrite in_cons => /orP[/eqP->|/n3H[b4H|b4H]].
  - right; apply: neval_stable b3H.
    by apply: leq_maxl.
  - left; apply: neval_stable b4H.
    by apply: leq_maxr.
  right; apply: neval_stable b4H.
  by apply: leq_maxr.
exists (maxn n n2).+1.
rewrite nevalE iH /=.
have bsH bs : 
  (forall b2 : board,
    b2 \in bs ->
    neval n (flip t) b2 = Some draw \/ neval n (flip t) b2 = Some win) ->
  osflip (\osmin_(i <- bs) neval (maxn n n2) (flip t) i) = Some draw
  \/
  osflip (\osmin_(i <- bs) neval (maxn n n2) (flip t) i) = Some lost.
  elim: bs => [bsH | b3 bs IH bsH]; first by rewrite big_nil; right.
  rewrite big_cons osflip_min.
  case: IH => [b4 b4H|->|->].
  - by apply: bsH; rewrite in_cons b4H orbT.
  - case: (bsH b3); rewrite ?in_cons ?eqxx // => /neval_stable->; first by left.
    - by apply: leq_maxl.
    - by left.
    by apply: leq_maxl.
  rewrite osmaxnl.
  case: (bsH b3); rewrite ?in_cons ?eqxx // => /neval_stable->; first by left.
  - by apply: leq_maxl.
  - by right.
  by apply: leq_maxl.
elim: moves b2Im H => // b3 bs IH b2Im H.
rewrite big_cons osflip_min.
move: b2Im; rewrite in_cons => /orP[/eqP<-|].
  rewrite (neval_stable (leq_maxr _ _) n2H).
  have [|->|->] // := (bsH bs).
  by move=> b4 b4I; apply: H; rewrite in_cons b4I orbT.
move=> /IH-> //.
  case: (H b3); first by rewrite in_cons eqxx.
    by move=> /(neval_stable (leq_maxl _ n2)) ->.
  by move=> /(neval_stable (leq_maxl _ n2)) ->.
move=> b4 b4I.
by apply: H; rewrite in_cons b4I orbT.
Qed.  

End Board.
