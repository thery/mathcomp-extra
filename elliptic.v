(* A version of Coqprime Elliptic for mathcomp *)
From mathcomp Require Import all_ssreflect all_algebra ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section ELLIPTIC.

(* Field elements                                                             *)
Variable K : fieldType.

Variable (A B : K).

Open Scope ring_scope.

Record ell_theory: Prop := mk_ell_theory {

 (* field properties *)
    NonSingular : 4%:R * A ^+ 3 + 27%:R * B ^+ 2 != 0;
 (* Characteristic greater than 2 *)
    two_not_zero : 2%:R != 0 :> K;
  }.


Variable Eth : ell_theory.

Theorem K2D0: 2%:R != 0 :> K.
Proof. by apply: two_not_zero Eth. Qed.

(******************************************************************************)
(*                                                                            *)
(*      Definition of the elements of the curve                               *)
(*                                                                            *)
(******************************************************************************)


Inductive elt: Type :=
  (* The infinity point *)
  inf_elt : elt
  (* A point of the curve *)
| curve_elt : forall x y : K, y ^+ 2 = x ^+ 3 +  A * x + B -> elt.

Theorem curve_elt_irr x1 x2 y1 y2 e1 e2 :
  x1 = x2 -> y1 = y2 -> @curve_elt x1 y1 e1 = @curve_elt x2 y2 e2.
Proof.
move=> x1E y1E; move: e1 e2; rewrite x1E y1E => e1 e2.
congr curve_elt.
apply: Eqdep_dec.eq_proofs_unicity => x y.
by case: (x =P y); [left | right].
Qed.

Theorem curve_elt_irr1 x1 x2 y1 y2 e1 e2 :
  x1 = x2 -> (x1 = x2 -> y1 = y2) -> @curve_elt x1 y1 e1 = @curve_elt x2 y2 e2.
Proof. by move=> x1E y1E; apply: curve_elt_irr (y1E _). Qed.

Definition eq_elt p1 p2 :=
  if p1 is @curve_elt x1 y1 _ then
    if p2 is @curve_elt x2 y2 _ then (x1 == x2) && (y1 == y2)
    else false
  else 
    if p2 is @curve_elt x2 y2 _ then false else true.

Lemma eq_eltP : Equality.axiom eq_elt.
Proof.
case => [[|x2 y2 e2]| x1 y1 e1 [|x2 y2 e2]] /=; try by apply: (iffP idP).
apply: (iffP andP) => [[/eqP x1E /eqP x2E]| [-> ->]//].
by apply: curve_elt_irr.
Qed.

Canonical elt_eqMixin := EqMixin eq_eltP.
Canonical elt_eqType := Eval hnf in EqType elt elt_eqMixin.

Lemma oppe_lem x y :
  y ^+ 2 = x ^+ 3 + A * x + B -> (- y) ^+ 2 = x ^+ 3 + A * x + B.
Proof. by rewrite sqrrN. Qed.

(******************************************************************************)
(*                                                                            *)
(*      Opposite function                                                     *)
(*                                                                            *)
(******************************************************************************)

Definition oppe (p : elt) : elt :=
  if p is @curve_elt x y e then @curve_elt x (-y) (oppe_lem e)
  else inf_elt.

Theorem oppeK p : oppe (oppe p) = p.
Proof. by case p  => //= x y e; apply curve_elt_irr; ring. Qed.

Theorem curve_elt_oppe x1 x2 y1 y2 e1 e2 (x1E : x1 = x2) :
     @curve_elt x1 y1 e1 = @curve_elt x2 y2 e2
  \/ 
     @curve_elt x1 y1 e1 = oppe (@curve_elt x2 y2 e2).
Proof.
have /eqP : (y1 - y2) * (y1 + y2) = 0 by move: x1E e1 e2; ring.
rewrite mulf_eq0 => /orP[] /eqP Hy.
  left; apply: curve_elt_irr => //.
  by rewrite -[y1](subrK y2) Hy; ring.
right.
apply: curve_elt_irr => //.
by rewrite -[y1](addrK y2) Hy; ring.
Qed.

Lemma adde_lem1 x1 y1 :
  y1 != 0 ->
  y1 ^+ 2 = x1 ^+ 3 + A * x1 + B ->
  let l := (3%:R * x1 ^+2 + A) / (2%:R * y1) in
  let x3 := l ^+ 2 - 2%:R * x1  in
  (- y1 - l * (x3 - x1)) ^+ 2 = x3 ^+ 3 + A * x3 + B.
Proof.
move=> y1D0 y1E l x3; rewrite /x3 /l. move: y1E; field.
by rewrite y1D0 K2D0.
Qed.

Lemma adde_lem2 x1 y1 x2 y2 :
  x1 <> x2 ->
  y1 ^ 2 = x1 ^ 3 + A * x1 + B ->
  y2 ^ 2 = x2 ^ 3 + A * x2 + B ->
  let l := (y2 - y1) / (x2 - x1) in
  let x3 := l ^ 2 - x1 - x2 in
  (- y1 - l * (x3 - x1)) ^ 2 = x3 ^ 3 + A * x3 + B.
Proof.
move=> /eqP x1Dx2 y1E y2E l x3; rewrite /x3 /l.
Time move: y1E y2E; field.
apply: contra_neq x1Dx2 => x2Bx1.
by rewrite -[x2](subrK x1) x2Bx1; ring.
Qed.

Lemma adde_zero x1 x2 y1 y2 :
  x1 = x2 ->
  y1 ^+ 2 = x1 ^+ 3 + A * x1 + B ->
  y2 ^+ 2 = x2 ^+ 3 + A * x2 + B ->
  y1 != - y2 -> y1 = y2.
Proof.
move=> x1E e1 e2 y1DNy2.
have /eqP : (y1 - y2) * (y1 + y2) = 0 by move: x1E e1 e2; ring.
rewrite mulf_eq0 => /orP[] /eqP Hy.
  by rewrite -[y1](subrK y2) Hy; ring.
case/eqP: y1DNy2.
by rewrite -[y1](addrK y2) Hy; ring.
Qed.

Lemma adde_zero_diff x1 x2 y1 y2 :
  x1 = x2 ->
  y1 ^+ 2 = x1 ^+ 3 + A * x1 + B ->
  y2 ^+ 2 = x2 ^+ 3 + A * x2 + B ->
  y1 <> - y2 -> y1 != 0.
Proof.
move=> x1E e1 e2 /eqP y1DNy2.
have y1E := adde_zero x1E e1 e2 y1DNy2.
apply: contra_neq y1DNy2.
by rewrite -y1E; ring.
Qed.

(******************************************************************************)
(*                                                                            *)
(*      Addition                                                              *)
(*                                                                            *)
(******************************************************************************)

Definition adde (p1 p2 : elt) : elt :=
  if p1 is curve_elt x1 y1 e1 then
    if p2 is curve_elt x2 y2 e2 then
      match x1 =P x2 with
      | ReflectT x1Ex2 =>
        (* we have p1 = p2 or p1 = - p2 *)
        match y1 =P - y2 with
        | ReflectT _ => (* we do p - p *) inf_elt
        | ReflectF y1DNy2 => 
          (* we do the tangent *)
          let l := (3%:R * x1 ^+ 2  + A) / (2%:R * y1) in
          let x3 := l ^+ 2 - 2%:R * x1 in
          @curve_elt x3 (-y1 - l * (x3 - x1)) 
            (adde_lem1 (adde_zero_diff x1Ex2 e1 e2 y1DNy2) e1)
        end
      | ReflectF x1Dx2 =>
        (* general case *)
        let l := (y2 - y1) / (x2 - x1) in
        let x3 := l ^+ 2 - x1 -x2 in
        @curve_elt x3 (- y1 - l * (x3 - x1)) (adde_lem2 x1Dx2 e1 e2)
      end
    else p1
  else p2.

(******************************************************************************)
(*                                                                            *)
(*      Direct case predicate for adde                                         *)
(*                                                                            *)
(******************************************************************************)

Theorem adde_case P :
  (forall p, P inf_elt p p) ->
  (forall p, P p inf_elt p) ->
  (forall p, P p (oppe p) inf_elt) ->
  (forall p1 x1 y1 e1 p2 x2 y2 e2 l
    (p1E : p1 = (@curve_elt x1 y1 e1)) 
    (p2E : p2 = (@curve_elt x2 y2 e2))
    (p2E1 : p2 = adde p1 p1)
    (y1NZ : y1 != 0)
    (lE : l = (3 %:R* x1 ^+2 + A) / (2%:R * y1))
    (x2E : x2 = l ^+ 2 - 2%:R * x1)
    (y2E : y2 = - y1 - l * (x2 - x1)),
    P p1 p1 p2) ->
  (forall p1 x1 y1 e1 p2 x2 y2 e2 p3 x3 y3 e3 l
    (p1E : p1 = (@curve_elt x1 y1 e1))
    (p2E : p2 = (@curve_elt x2 y2 e2))
    (p3E : p3 = (@curve_elt x3 y3 e3))
    (p3E1 : p3 = adde p1 p2)
    (x1Dx2 : x1 != x2)
    (lE : l = (y2 - y1) / (x2 - x1))
    (x3E : x3 = l ^+ 2 - x1 - x2)
    (y3E : y3 = -y1 - l * (x3 - x1)),
    P p1 p2 p3)->
  forall p q, P p q (adde p q).
Proof.
move=> Hip Hpi HpNp Ht Hg [|x1 y1 e1] [|x2 y2 e2] //.
rewrite /adde.
case: (x1 =P x2) => [x1Ex2 | x1Ex2].
  case: (y1 =P - y2) => [y1Ey2 | y1Ey2].
    have ->// : curve_elt e2 = oppe (curve_elt e1).
    by apply: curve_elt_irr => //; move: y1Ey2; ring.
  have y1NZ : y1 != 0 by apply: adde_zero_diff e1 e2 _.
  have -> : curve_elt e2 = curve_elt e1.
    apply: curve_elt_irr; apply/sym_equal => //.
    by apply: adde_zero e1 e2 _ => //; apply/eqP.
  pose e3 := adde_lem1 (adde_zero_diff x1Ex2 e1 e2 y1Ey2) e1.
  apply: (Ht (curve_elt e1) x1 y1 e1 (curve_elt e3) _ _ e3) => //.
  rewrite /adde; (do 2 case: eqP => //) => y1E x1E; last first.
    by apply: curve_elt_irr.
  have /eqP : 2%:R * y1 = 0 by rewrite mulr_natl mulr2n {1}y1E; ring.
  by rewrite mulf_eq0 (negPf K2D0) (negPf y1NZ).
pose e3 := adde_lem2 x1Ex2 e1 e2.
apply: (Hg (curve_elt e1) x1 y1 e1 (curve_elt e2) x2 y2 e2
           (curve_elt e3) _ _ e3) => //; last by apply/eqP.
rewrite /adde; case: eqP => // x1Dx2.
by apply: curve_elt_irr.
Qed.

Theorem adde_casew P :
  (forall p, P inf_elt p p) ->
  (forall p, P p inf_elt p) ->
  (forall p, P p (oppe p) inf_elt) ->
  (forall p1 x1 y1 e1 p2 x2 y2 e2 p3 x3 y3 e3 l
    (p1E : p1 = (@curve_elt x1 y1 e1))
    (p2E : p2 = (@curve_elt x2 y2 e2))
    (p3E : p3 = (@curve_elt x3 y3 e3))
    (p3E1 : p3 = adde p1 p2)
    (p1DNp2 : p1 != oppe p2)
    (HC : [/\ x1 = x2, y1 = y2 & l = (3%:R * x1 ^+ 2 + A) / (2%:R * y1)] \/
      (x1 != x2 /\ l = (y2 - y1) / (x2 - x1))
    )
    (x3E : x3 = l ^+ 2 - x1 - x2)
    (y3E : y3 = -y1 - l * (x3 - x1)), 
     P p1 p2 p3)->
  forall p q, P p q (adde p q).
Proof.
move=> Hip Hpi HpNp Hg p q; apply: adde_case => //.
  move=> p1 x1 y1 e1 p2 x2 y2 e2 l p1E p2E p2E1 y1NZ lE x2E y2E.
  apply: (Hg p1 x1 y1 e1 p1 x1 y1 e1 p2 x2 y2 e2 l) => //.
  - apply/eqP; rewrite p1E /= => [] [y1E].
    have /eqP : 2%:R * y1 = 0  by rewrite mulr_natl mulr2n {1}y1E; ring.
    by rewrite mulf_eq0 (negPf K2D0) (negPf y1NZ).
  - by left.
  by move: x2E; ring.
move=> p1 x1 y1 e1 p2 x2 y2 e2 p3 x3 y3 e3 l p1E p2E p3E p3E1 x1Dx2 lE x3E y3E.
apply: (Hg p1 x1 y1 e1 p2 x2 y2 e2 p3 x3 y3 e3 l) => //.
  apply/eqP; rewrite p1E p2E => [] [] x1Ex2.
  by case/eqP: x1Dx2.
by right; split.
Qed.

(* Tangent                                                                    *)
Definition is_tangent p1 p2 := [&& p1 != inf_elt, p1 == p2 & p1 != oppe p2].

(* Generic                                                                    *)
Definition is_generic p1 p2 := [&& p1 != inf_elt, p2 != inf_elt,
                                   p1 != p2 & p1 != oppe p2].

(* Generic or Tangent                                                         *)
Definition is_gotan p1 p2 := [&& p1 != inf_elt, p2 != inf_elt & p1 != oppe p2].

Lemma is_generic_inf p : is_generic p inf_elt = false.
Proof. by apply/negP => /and4P[_ /eqP[]]. Qed.

Lemma is_generic_irr p : is_generic p p = false.
Proof. by apply/negP => /and4P[]; rewrite eqxx. Qed.

Lemma is_generic_oppe p : is_generic p (oppe p) = false.
Proof. by apply/negP => /and4P[]; rewrite oppeK eqxx. Qed.

Lemma is_tangent_inf p : is_tangent p inf_elt = false.
Proof. by apply/negP => /and3P[ _ /eqP->]. Qed.

Lemma is_tangent_oppe p : is_tangent p (oppe p) = false.
Proof. by apply/negP => /and3P[]; rewrite oppeK eqxx. Qed.

(******************************************************************************)
(*                                                                            *)
(*      Generic case for associativity                                        *)
(*       (A + B) + C = A + (B + C)                                            *)
(*                                                                            *)
(******************************************************************************)

Theorem spec1_assoc p1 p2 p3 :
   is_generic p1 p2 ->
   is_generic p2 p3 ->
   is_generic (adde p1 p2) p3 ->
   is_generic  p1 (adde p2 p3) ->
   adde p1 (adde p2 p3) = adde (adde p1 p2) p3.
Proof.
elim/adde_case: (adde p1 p2) => {p1 p2} //.
  move=> p1 x1 y1 e1 p2 x2 y2 e2 l p1E p2E p2E1 y1NZ lE x2E y2E.
  by rewrite is_generic_irr.
move=> p1 x1 y1 e1 p2 x2 y2 e2 p4 x4 y4 e4 l p1E p2E p4E p4E1 x1Dx2 lE x4E y4E.
elim/adde_case: (adde p2 p3) p2E p4E1 => {p2 p3}// [p|p|p|].
- by rewrite is_generic_inf.
- by rewrite is_generic_oppe.
- by rewrite is_generic_irr.
move=> p2 x2b y2b e2b p3 x3 y3 e3 p5 x5 y5 e5 l1 p2E.
rewrite {}[in p2 = _]p2E.
move=> p3E p5E p5E1 x2bDx3 l1E x5E y5E [x2bE y2bE] ; subst y2b x2b => {e2b}//.
move: p1E p5E p5E1; elim/adde_case: (adde p1 p5) => {p1 p5}// [p|p|].
- by rewrite is_generic_oppe.
- by rewrite is_generic_irr.
move=> p1 x1b y1b e1b.
move=> p5b x5b y5b e5b p6 x6 y6 e6 l2 p1E p5bE.
rewrite {}[in p1 = _]p1E {}[in p5b = _]p5bE.
move=> p6E _ x1bDx5b l2E x6E y6E [x1bE y1bE] [x5bE y5bE]; 
  subst y1b x1b y5b x5b => {e1b e5b}// _ p4E1 _.
elim/adde_case: (adde p4 p3) p3E p4E p4E1 => {p3 p4}// [p|p|].
- by rewrite is_generic_oppe.
- by rewrite is_generic_irr.
intros p4b x4b y4b H4b p3b x3b y3b e3b p7 x7 y7 H7
       l3 p4bE p3bE p7E p7E1 x4bDx4b l3E x7E y7E.
rewrite [in p3b = _]p3bE [in p4b = _]p4bE => [] [x3bE y3bE] [x4bE y4bE].
subst y3b x3b y4b x4b => {p3bE p4bE}// _ _ _ _.
have x2Bx1NZ : x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
have x3Bx2NZ : x3 - x2 != 0 by rewrite subr_eq0 eq_sym.
rewrite p6E p7E; apply: curve_elt_irr; subst.
  move: e1 e2 e3b; field => //.
  apply/and4P; split => //.
    apply: contra x4bDx4b=> /eqP x3E.
    rewrite -subr_eq0 (_ : 0 = 0 / -((x2 - x1) ^+ 2)); last by rewrite mul0r.
    apply/eqP; rewrite -x3E; field.
    by rewrite oppr_eq0 sqrf_eq0 x2Bx1NZ.
  apply: contra x1bDx5b => /eqP x3E.
  rewrite -subr_eq0 (_ : 0 = 0 / -((x3 - x2) ^+ 2)); last by rewrite mul0r.
  apply/eqP; rewrite -x3E; field.
  by rewrite oppr_eq0 sqrf_eq0 x3Bx2NZ.
move: e1 e2 e3b; field => //.
apply/and4P; split => //.
apply: contra x4bDx4b => /eqP x3E.
  rewrite -subr_eq0 (_ : 0 = 0 / -((x2 - x1) ^+ 2)); last by rewrite mul0r.
  apply/eqP; rewrite -x3E; field.
  by rewrite oppr_eq0 sqrf_eq0 x2Bx1NZ.
apply: contra x1bDx5b => /eqP x3E.
rewrite -subr_eq0 (_ : 0 = 0 / -((x3 - x2) ^+ 2)); last by rewrite mul0r.
apply/eqP; rewrite -x3E; field.
by rewrite oppr_eq0 sqrf_eq0 x3Bx2NZ.
Qed.

(******************************************************************************)
(*                                                                            *)
(*      Tangent case for associativity                                        *)
(*       A + (B + B) = (A + B) + B                                            *)
(*                                                                            *)
(******************************************************************************)

Theorem spec2_assoc p1 p2 p3 :
  is_generic p1 p2 ->
  is_tangent p2 p3 ->
  is_generic (adde p1 p2) p3 ->
  is_generic  p1 (adde p2 p3) ->
  adde p1 (adde p2 p3) = adde (adde p1 p2) p3.
Proof.
elim/adde_case: (adde p1 p2) => {p1 p2}// [p|].
  by rewrite is_generic_irr.
move=> p1 x1 y1 e1 p2 x2 y2 e2 p4 x4 y4 e4 l
       p1E p2E p4E p4E1 x1Dx2 lE x4E y4E.
elim/adde_case: (adde p2 p3) p2E p4E1 => {p2 p3}// [p|p||]; first 3 last.
- move=> p3 x3 y3 e3 p5 x5 y5 e5 p6 x6 y6 e6 l1 -> -> _ _ x3Dx5 _ _ _ _ _ _.
  by case/and3P=> [_ /eqP[x3Ex5]]; case/eqP: x3Dx5.
- by rewrite is_generic_inf.
- by rewrite is_generic_inf.
move=> p2 x2b y2b e2b p5 x5 y5 e5 l1 p2E p5E p5E1 y2bNZ l1E x5E y5E.
rewrite [in p2 = _]p2E => [] [x2bE y2bE].
subst x2b y2b.
elim/adde_case: (adde p1 p5) p1E p5E p5E1 => {p1 p5}// [p|p|]; last 3 first.
- by rewrite is_generic_oppe.
- by rewrite is_generic_irr.
move=> p1 x1b y1b e1b p5b x5b y5b e5b p6 x6 y6 e6 l2
       p1E p5bE p6E p6E1 x1bDx5b l2E x6E y6E.
rewrite [in p1 = _]p1E [in p5b = _]p5bE => [] [x1bE y1bE] [x5bE y5bE].
subst x1b y1b x5b y5b => {p1E p5bE}// _ p4E1 _ _.
elim/adde_case: (adde p4 p2) p2E p4E p4E1 => // [p|p|].
- by rewrite is_generic_oppe.
- by rewrite is_generic_irr.
move=> p4b x4b y4b e4b p3b x3b y3b e3b p7 x7 y7 e7 l3
       p4bE p3bE p7E p7E1 x4bDx3b l3E x7E y7E.
rewrite [in p3b = _]p3bE [in p4b = _]p4bE => [] [x3bE y3bE] [x4bE y4bE].
subst x3b y3b x4b y4b => {p3bE p4bE}// _ _ _.
have x2Bx1NZ : x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
subst; apply: curve_elt_irr.
  move: e1 e2; field.
  apply/and5P; split => //.
  - apply: contra x4bDx3b => /eqP polE.
    rewrite -subr_eq0 (_ : 0 = 0 / -((x2 - x1) ^+ 2)); last by rewrite mul0r.
    apply/eqP; rewrite -polE; field.
    by rewrite oppr_eq0 sqrf_eq0 x2Bx1NZ.
  - by apply: K2D0.
  apply: contra x1bDx5b => /eqP polE.
  rewrite -subr_eq0 (_ : 0 = 0 / -((2%:R * y2) ^+ 2)); last by rewrite mul0r.
  apply/eqP; rewrite -polE; field.
  by rewrite oppr_eq0 sqrf_eq0 mulf_eq0 negb_or !y2bNZ !K2D0.
move: e1 e2; field.
apply/and5P; split => //.
- apply: contra x4bDx3b => /eqP polE.
  rewrite -subr_eq0 (_ : 0 = 0 / -((x2 - x1) ^+ 2)); last by rewrite mul0r.
  apply/eqP; rewrite -polE; field.
  by rewrite oppr_eq0 sqrf_eq0 x2Bx1NZ.
- by apply: K2D0.
apply: contra x1bDx5b => /eqP x3E.
rewrite -subr_eq0 (_ : 0 = 0 / -((2%:R * y2) ^+ 2)); last by rewrite mul0r.
apply/eqP; rewrite -x3E; field.
by rewrite oppr_eq0 sqrf_eq0 mulf_eq0 negb_or !y2bNZ !K2D0.
Time Qed.

(******************************************************************************)
(*                                                                            *)
(*      Identity case for associativity                                       *)
(*       (A + A) + (A + A) = A + (A + (A + A))                                *)
(*                                                                            *)
(******************************************************************************)

Theorem spec3_assoc p1 p2 p3 :
  is_generic p1 p2 ->
  is_tangent p2 p3 ->
  is_generic (adde p1 p2) p3 ->
  is_tangent  p1 (adde p2 p3) ->
  adde p1 (adde p2 p3) = adde (adde p1 p2) p3.
Proof.
elim/adde_case: (adde p1 p2) => {p1 p2}// [p|].
  by rewrite is_generic_irr.
intros p1 x1 y1 e1 p2 x2 y2 e2 p4 x4 y4 e4 l
       p1E p2E p4E p4E1 x1Dx2 lE x4E y4E.
elim/adde_case: (adde p2 p3) p2E p4E1 => [p|p|p||] {p2 p3} //; first 3 last.
- move=> p2b x2b y2b e2b p3 x3 y3 e3 p5 x5 y5 e5 l2 p2bE p3E p3E1 p5E p5E1
         l2E x5E y5E.
  rewrite [in p2b = _]p2bE => [] [x2bE y2bE] p4E1.
  subst x2b y2b; rewrite p2bE p3E => _ /and3P[_ /eqP[]x2Ex3 _].
  by case/eqP : p5E1.
- by rewrite is_generic_inf.
- by rewrite is_tangent_oppe.
move=> p2 x2b y2b e2b p5 x5 y5 e5 l1 p2E
       p5E p5E1 y2bNZ l1E x5E y5E p2E1 p4E1.
rewrite p2E in p2E1; have [x2bE y2bE] := p2E1.
subst y2b x2b => {p2E1}//.
elim/adde_case: (adde p1 p5) p1E p4E1 p5E p5E1 => {p1 p5}// [p||]; first 2 last.
- move=> p1b x1b y1b e1b p5b x5b y5b e5b p3 x3 y3 e3 l2 p1bE p5bE p3E p3E1.
  move=> x1bDx5b l2E x3E y3R.
  rewrite [in p1b = _]p1bE [in p5b =_]p5bE => [] [x1bE y1bE] p4E1 [x5bE y5bE].
  subst x1b y1b x5b y5b => _ _ _ _ /and3P[_ /eqP] //.
  by rewrite p1bE p5bE => [] [x1Ex5]; case/eqP: x1bDx5b.
- by rewrite is_tangent_oppe.
intros p1 x1b y1b e1b p6 x6 y6 e6 l2 p1E p6E p6E1 y1bNZ l2E x6E y6E.
rewrite ![in p1 = _]p1E => [] [x1bE y1bE] p4E1.
subst x1b y1b => {p1E}//.
case => x1E y1E; subst x5 y5.
elim/adde_case: (adde p4 p2) p4E p4E1 p2E => // [p|p|].
- by rewrite is_generic_oppe.
- by rewrite is_generic_irr.
move=> p4b x4b y4b e4b p2b x2b y2b e2b1 p7 x7 y7 e7 l4
       p4bE p2bE p7E p7E1 x4bDx2b l4E x7E y7E.
rewrite [in p4b = _]p4bE [in p2b = _]p2bE => [] [x4bE y4bE] p4b1 [x2bE y2bE].
subst x4b y4b x2b y2b.
(* we don't have field_simplify *)
pose pol := -(2%:R ^+ 2  * (2%:R * y2) ^+ 2) *
             ((3%:R * x2) * (4%:R * y2 ^+ 2) - (3%:R * x2 ^+ 2 + A) ^+ 2)^+2.
pose pol1 := x2 * (4%:R * y2 ^+ 2) -
       ((3%:R * x2 ^+ 2 + A) ^+ 2 + - (2%:R * x2) * (4%:R * y2 ^+ 2)).
have pol1NZ : pol1 != 0.
  apply: contra x1Dx2 => /eqP pol1E.
  rewrite -subr_eq0 (_ : 0 = 0 / -((2%:R * y2) ^+ 2)); last by rewrite mul0r.
  apply/eqP; rewrite -pol1E /pol1 x1E l1E; field.
  by rewrite oppr_eq0 sqrf_eq0 mulf_eq0 negb_or K2D0 y2bNZ.
pose pol2 := 3%:R * x2 * (4%:R * y2 ^+ 2) - (3%:R * x2 ^+ 2 + A) ^+ 2.
have pol2NZ : pol2 != 0.
  apply: contra x1Dx2 => /eqP polE.
  rewrite -subr_eq0 (_ : 0 = 0 / -((2%:R * y2) ^+ 2)); last by rewrite mul0r.
  apply/eqP; rewrite -polE x1E l1E /pol2; field.
  by rewrite oppr_eq0 sqrf_eq0 mulf_eq0 negb_or K2D0 y2bNZ.
move=> _ _ _ _ _; rewrite p6E p7E; apply: curve_elt_irr.
  rewrite !(x6E, x7E, l2E, l4E, y4E, x4E,  x1E, y1E, l1E, lE).
  move: e2; field.
  rewrite K2D0; apply/and5P; split => //.
    apply: contra x4bDx2b => /eqP polE.
    rewrite -subr_eq0 (_ : 0 =  0 / pol); last by rewrite mul0r.
    apply/eqP; rewrite -polE x4E lE x1E y1E l1E /pol.
    field.
    rewrite y2bNZ K2D0; apply/and4P; split => //.
    have -> : 4%:R = 2%:R ^+ 2 :> K by rewrite expr2 -natrM.
    by rewrite !(oppr_eq0, mulf_eq0, negb_or, K2D0, y2bNZ).
  apply: contra_neq y1bNZ => polE.
  rewrite y1E l1E; apply/eqP.
  rewrite (_ : 0 = 0 / ((2%:R * y2) ^+ 3)); last by rewrite mul0r.
  apply/eqP; rewrite -polE.
  by field; rewrite y2bNZ K2D0.
rewrite !(y6E, y7E, l2E, l4E, x6E, x7E, y4E, x4E, y1E, x1E, l1E, lE).
move: e2; field.
rewrite y2bNZ K2D0; apply/and5P; split => //.
  apply: contra x4bDx2b => /eqP polE.
  rewrite -subr_eq0 (_ : 0 =  0 / pol); last by rewrite mul0r.
  apply/eqP; rewrite -polE x4E lE x1E y1E l1E /pol.
  field.
  rewrite y2bNZ K2D0; apply/and4P; split => //.
  have -> : 4%:R = 2%:R ^+ 2 :> K by rewrite expr2 -natrM.
  by rewrite !(oppr_eq0, mulf_eq0, negb_or, K2D0, y2bNZ).
apply: contra_neq y1bNZ => polE.
rewrite y1E l1E; apply/eqP.
rewrite (_ : 0 = 0 / ((2%:R * y2) ^+ 3)); last by rewrite mul0r.
apply/eqP; rewrite -polE.
by field; rewrite y2bNZ K2D0.
Qed.

(******************************************************************************)
(*                                                                            *)
(*      inf_elt is the zero                                                   *)
(*                                                                            *)
(******************************************************************************)

Theorem add0e p : adde inf_elt p = p.
Proof. by []. Qed.

Theorem adde0 p : adde p inf_elt = p.
Proof. by case: p. Qed.

(******************************************************************************)
(*                                                                            *)
(*      oppe is the opposite                                                  *)
(*                                                                            *)
(******************************************************************************)

Theorem addeN p : adde p (oppe p) = inf_elt.
Proof.
case: p; rewrite //= => x y e.
by (do 2 case: eqP => //) => [] []; rewrite opprK.
Qed.


(******************************************************************************)
(*                                                                            *)
(*      Addition is commutative                                               *)
(*                                                                            *)
(******************************************************************************)

Theorem addeC p1 p2 : adde p1 p2 = adde p2 p1.
Proof.
case: p1 => /= [|x1 y1 e1]; first by rewrite adde0.
case: p2 => //= x2 y2 e2.
case: eqP => [x1Ex2 | x1Dx2].
  case: eqP => [y1ENy2|y1DNy2].
    case: eqP => [x1E1x2| []//].
    by case: eqP => // [] []; rewrite y1ENy2 opprK.
  case: eqP => [x2Ex1 | []//].
  case: eqP => [y2ENy1|y2DNy1]; first by case: y1DNy2; rewrite y2ENy1 opprK.
  by apply curve_elt_irr; rewrite x1Ex2 (adde_zero _ e1 e2) //; apply/eqP.
case: eqP => [x2Ex1|x2Dx1]; first by case: x1Dx2.
by apply curve_elt_irr; field; 
   rewrite !subr_eq0; have /eqP-> := x1Dx2; have /eqP-> := x2Dx1.
Qed.

Theorem adde_aux1 x1 y1 x2 y2 :
  y1 ^+ 2 = x1 ^+ 3 + A * x1 + B -> y2 ^+ 2 = x2 ^+ 3 + A * x2 + B ->
  x1 != x2 ->  y2 = 0 -> ((y2 - y1) / (x2 - x1)) ^+ 2 - x1 - x2 != x2.
Proof.
move=> e1 e2 x1Dx2 y2Z; rewrite -subr_eq0; apply/eqP=> polE.
have x23E : x2 ^+ 3 = -(A * x2 + B).
  by apply/eqP; rewrite -subr_eq0 opprK addrA -e2 y2Z expf_eq0 eqxx.
have : (x2 - x1) * (2%:R * A * x2 + 3%:R * B) == 0 .
  rewrite (_ : 0 = 0 * (((x2 - x1) ^+ 2) * x2)); last by rewrite mul0r.
  rewrite -polE; apply/eqP; move: y2Z e1 x23E.
  by field; rewrite subr_eq0 eq_sym.
rewrite mulf_eq0 subr_eq0 eq_sym (negPf x1Dx2) /= addr_eq0 => /eqP Ax2E.
have BZ : B = 0.
  rewrite -[LHS]opprK.
  have : - B * (4%:R * A ^+ 3 + 27%:R * B ^+ 2) == 0.
    apply/eqP.
    have :  (2%:R * A * x2) ^+ 3 + 4%:R * A ^+ 3 * (2%:R * A * x2) + 
            8%:R * A ^+ 3 * B = 8%:R * A ^+ 3 * y2 ^+ 2.
      by rewrite e2; ring.
    by rewrite y2Z expr0n mulr0 Ax2E => <-; ring.
  rewrite mulf_eq0 (negPf (NonSingular Eth)) orbF => /eqP->.
  by rewrite oppr0.
have : 2%:R * A * x2 == 0 by rewrite Ax2E BZ mulr0 oppr0.
rewrite !mulf_eq0 (negPf K2D0) /= => /orP[/eqP AZ|/eqP x2Z].
  by case/eqP: (NonSingular Eth); rewrite AZ BZ !expr0n !mulr0 addr0.
have : A * x1 == 0.
  apply/eqP; rewrite (_ : 0 = 0 * (x2 - x1) ^+ 2); last by rewrite mul0r.
  rewrite -polE y2Z x2Z !subr0 !sub0r.
  by move: e1 BZ; field; rewrite oppr_eq0 -x2Z.
rewrite !mulf_eq0 => /orP[/eqP AZ|/eqP x1Z].
  by case/eqP: (NonSingular Eth); rewrite AZ BZ !expr0n !mulr0 addr0.
by case/eqP: x1Dx2; rewrite x2Z.
Qed.

(******************************************************************************)
(*                                                                            *)
(*      There is only one zero                                                *)
(*                                                                            *)
(******************************************************************************)

Theorem uniq_zeroe p1 p2 : adde p1 p2 = p2 -> p1 = inf_elt.
Proof.
elim/adde_case: (adde p1 p2) => {p1 p2}//=; first by case.
  move=> p1 x1 y1 e1 p2 x2 y2 e2 l -> -> p2E y1NZ lE x2E y2E [x2E1 y2E1].
  have : 2%:R * y1 == 0.
    by apply/eqP; rewrite -(subrr y2) [in - _]y2E y2E1 x2E1; ring.
  rewrite mulf_eq0 (negPf K2D0) => /eqP y1Z.
  by case/eqP: y1NZ.
move=> p1 x1 y1 e1 p2 x2 y2 e2 p3 x3 y3 e3 l p1E p2E p3E p3E1 x1Dx2 lE
       x3E y3E.
rewrite p2E p3E=> [] [x3E1 y3E1].
suff y2Z : y2 = 0.
  have /eqP[] := adde_aux1 e1 e2 x1Dx2 y2Z.
  by rewrite -lE -x3E.
suff : 2%:R * y2 == 0.
  by rewrite mulf_eq0 (negPf K2D0) => /eqP.
apply/eqP.
have /eqP := y3E; rewrite x3E1 y3E1 lE -subr_eq0 => /eqP <-.
by field; rewrite subr_eq0 eq_sym.
Qed.

(******************************************************************************)
(*                                                                            *)
(*      There is only one opposite                                            *)
(*                                                                            *)
(******************************************************************************)

Theorem uniq_oppe p1 p2 : adde p1 p2 = inf_elt -> p2 = oppe p1.
Proof.
elim/adde_case: (adde p1 p2) => {p1 p2}// [p -> //||].
  by move=> p1 x1 y1 e1 p2 x2 y2 e2 l _  ->.
by move=> p1 x1 y1 e1 p2 x2 y2 e2 p3 x3 y3 e3 l _  _ ->.
Qed.

(******************************************************************************)
(*                                                                            *)
(*      Opposite of zero is zero                                              *)
(*                                                                            *)
(******************************************************************************)

Theorem oppe0 : oppe (inf_elt) = inf_elt.
Proof. by []. Qed.


(******************************************************************************)
(*                                                                            *)
(*      Opposite of a sum is the sum of opposite                              *)
(*                                                                            *)
(******************************************************************************)

Theorem oppe_adde p1 p2 : oppe (adde p1 p2) = adde (oppe p1) (oppe p2).
Proof.
case: p1 => [|x1 y1 e1]; first by rewrite oppe0 !add0e.
case p2 => [|x2 y2 e2/=]; first by rewrite !adde0.
case: eqP => [x1Ex2|x1Dx2]; last first.
  by apply: curve_elt_irr; field; rewrite subr_eq0 eq_sym; apply/eqP.
case: eqP => [y1ENy2|y1DNy2].
  by case: eqP => [//|[]]; rewrite y1ENy2.
case: eqP => [Ny1ENNy2|Ny1DNNy2].
  by case: y1DNy2; rewrite -(opprK y1) Ny1ENNy2 opprK.
have y1NZ : y1 != 0 by apply: adde_zero_diff x1Ex2 e1 e2 y1DNy2.
by apply: curve_elt_irr; field; rewrite oppr_eq0 (negPf K2D0) y1NZ.
Qed.

Theorem addeI_oppe p1 p2 :
  adde p1 p2 = adde p1 (oppe p2) ->  p1 != oppe p1 -> p2 = oppe p2.
Proof.
elim/adde_case: (adde p1 p2) => {p1 p2}// [p infE /eqP[]||].
- by apply: uniq_oppe; rewrite -[X in adde _ X]oppeK.
- intros p1 x1 y1 e1 p2 x2 y2 e2 l p1E p2E p2E1 y1NZ lE x2E y2E p2E2 p1ENp1.
  by apply uniq_oppe; rewrite -p2E1 p2E2 addeN.
move=> p1 x1 y1 e1 p2 x2 y2 e2 p3 x3 y3 e3 l p1E p2E p3E p3E1 x1Dx2
       lE x3E y3E p3E2 p1DN1.
move: p3E2; rewrite p1E p2E p3E /=.
case: eqP => [x1Ex2 //|x1Dx21 [/eqP]]; first by case/eqP: x1Dx2.
rewrite x3E lE -subr_eq0 => /eqP polE _.
have : - 4%:R * y2 * y1 == 0.
  apply/eqP; rewrite (_ : 0 = 0 * (x2 - x1) ^+ 2); last by rewrite mul0r.
  by rewrite -polE; field; rewrite subr_eq0 eq_sym.
rewrite (natrM _ 2 2) !(mulf_eq0, oppr_eq0) (negPf K2D0) /=.
case/orP=> [/eqP y2Z| /eqP y1Z].
  by apply: curve_elt_irr; rewrite ?y2Z ?oppr0.
by case/eqP: p1DN1; rewrite p1E; apply: curve_elt_irr; rewrite ?y1Z ?oppr0.
Qed.

Theorem compat_addeK p :
 p != oppe p -> adde p p != oppe p -> adde (adde p p) (oppe p) = p.
Proof.
set p1 := adde p p; set p2 := oppe p.
have : p1 = adde p p by []; have : p2 = oppe p by [].
elim/adde_case: (adde p1 p2) => {p1 p2}// [p1 -> inE pDNp infDNp|
                                           p1 Np1ENp _ /eqP[]|
                                           p1 Np1ENp p1E pDNp1 p1DNp1||].
- by apply/sym_equal/uniq_oppe.
- by rewrite -(oppeK p) -Np1ENp.
- have pE : p = p1 by rewrite -(oppeK p) -Np1ENp oppeK.
- apply/sym_equal/(uniq_zeroe (_ : _ = p)).
  by rewrite [RHS]pE.
- by move=> p1 x1 y1 e1 p2 x2 y2 e2 l _ _ _ _ _ _ _ _ _ _ /eqP[].
move=> p1 x1 y1 e1 p2 x2 y2 e2 p3 x3 y3 e3 l p1E p2E p3E p3E1 x1Dx2 lE x3E y3E
       p2E1 p1E1 pDp2 p1Dp2.
case: p p2E1 p1E1 pDp2 => [-> //|x y e p2E1 p1E1 eE].
move: (p2E1); rewrite p2E => [] [x2E y2E].
subst x2 y2; rewrite p3E.
have [] // := curve_elt_oppe e3 e; last first.
  rewrite -p3E => p3E2.
  have /eqP[] : p1 != inf_elt by rewrite p1E.
  apply: (uniq_zeroe (_ : _ = p2)).
  by rewrite -p3E1 p2E1.
rewrite x3E lE; move: p1E1 => /=.
case: eqP => // xEx.
case: eqP => [_|yDNy]; first by rewrite p1E => /eqP.
rewrite p1E => [] [x1E y1E]; subst x1 y1.
set l1 := (3%:R * x ^+2 + A) / (2%:R * y).
by field; rewrite subr_eq0 eq_sym.
Qed.

Theorem adde_oppe_double_opp p1 p2 :
  adde p1 p2 = oppe p1 -> p2 = adde (oppe p1) (oppe p1).
Proof.
move=> p1Dp2E.
have [p1ENp1 | /eqP p1DNp1] := (p1 =P oppe p1).
  rewrite -[X in adde X]p1ENp1 addeN.
  apply: uniq_zeroe (_ : _ = p1).
  by rewrite addeC p1Dp2E.
rewrite -oppe_adde.
suff [] : 
    p2 = adde (oppe p1) (oppe p1) \/ p2 = oppe (adde (oppe p1) (oppe p1)).
- by rewrite <- oppe_adde.
- rewrite oppe_adde !oppeK => p2E.
  have [p1Dp1E|/eqP p1Dp1DNp1] := adde p1 p1 =P oppe p1.
    by rewrite p2E p1Dp1E -p1Dp2E p2E p1Dp1E addeN.
  rewrite -p2E.
  apply: addeI_oppe (_ : _ != oppe p1) => //.
  apply: etrans (_ : oppe (adde (adde p1 p1) (oppe p1)) = _).
    by rewrite compat_addeK //.
  by rewrite -p2E oppe_adde oppeK addeC.
rewrite -oppe_adde oppeK.
elim/adde_case: (adde p1 p2) p1Dp2E p1DNp1 => {p1 p2}// [p pE /eqP[]//|
                                                         p pE _||].
- by rewrite oppe_adde -pE; left.                                                        
- move=> p1 x1 y1 e1 p2 x2 y2 e2 l p1E p2E p2E1 p1NZ lE x2E y2E p2E2 p1DNp1.
  by rewrite -p2E1 p2E2 oppeK; left.
move=> p1 x1 y1 e1 p2 x2 y2 e2 p3 x3 y3 e3 l p1E p2E p3E p3E1 x1Dx2 lE 
      x3E y3E p3E2 p1DNp1.
have [y1Z | /eqP y1NZ] := y1 =P 0.
  by case/eqP: p1DNp1; rewrite p1E; apply:  curve_elt_irr; rewrite ?y1Z ?oppr0.
have Ny1NZ : - y1 != 0 by rewrite oppr_eq0.
have := p3E2.
rewrite p1E p2E p3E /=.
case: eqP => [x1Ex1 | //].
case: eqP => [/eqP | y1DNy1].
  by rewrite -subr_eq0 opprK -mulr2n -mulr_natl mulf_eq0 
     (negPf K2D0) (negPf y1NZ).
case => x3E1 y3E1; subst x3 y3.
have : forall P Q, P \/ Q -> Q \/ P by move=> P Q []; [right|left].
apply; apply: curve_elt_oppe.
move/eqP: x3E1; rewrite lE -subr_eq0 =>  /eqP polE.
suff :
    (x2 - (((3%:R * x1 ^+ 2  + A) / (2%:R * y1))^+ 2 - 2%:R * x1)) * 
    (x2 - x1) ^+ 2 == 0.
  rewrite mulf_eq0 expf_eq0 /= !subr_eq0 [_ == x1]eq_sym (negPf x1Dx2) orbF.
  by move/eqP.
apply/eqP.
suff pol1E :  (2%:R * y2  * y1) ^+ 2 -
      (x2 * A + 3%:R * x2 * x1 ^ 2 + A * x1 - x1 ^+ 3 + 2%:R * B) ^+ 2 = 0.
  rewrite (_ : 0 = 0 / (2%:R * y1) ^+ 2); last first.
    by rewrite mul0r.
  rewrite -pol1E; move: (e1) (e2).
  by field; rewrite y1NZ K2D0.
apply/eqP; rewrite subr_eq0; apply/eqP.
congr (_ ^+ _).
apply/eqP; rewrite -subr_eq0; apply/eqP.
rewrite (_ : 0 = 0 * -(x2 - x1) ^+ 2); last by rewrite mul0r.
rewrite -polE; move: (e1) (e2).
by field; rewrite subr_eq0 eq_sym.
Qed.


(******************************************************************************)
(*                                                                            *)
(*      Cancellation rule                                                     *)
(*                                                                            *)
(******************************************************************************)

Theorem addeI p1 p2 p3 : adde p1 p2 = adde p1 p3 -> p2 = p3.
Proof.
elim/adde_casew : (adde p1 p2) => {p1 p2}// [p pE|p infE|].
- apply/sym_equal/(uniq_zeroe (_ : _ p)).
  by rewrite addeC.
- by apply/sym_equal/uniq_oppe.
move=> p1 x1 y1 e1 p2 x2 y2 e2 p4 x4 y4 e4 l
       p1E p2E p4E p4E1 p1DNp2 H x4E y4E.
move: p1E p4E1 p1DNp2; rewrite p4E.
elim/adde_casew : (adde p1 p3) => {p1 p3}// [p pE p4E1 pDNp2 p4E2|].
  apply: uniq_zeroe (_ : _ = p).
  by rewrite -addeC -p4E1.
move=> p1 x1b y1b e1b p3 x3 y3 e3 p5 x5 y5 e5 l'.
move=> p1bE p3E p5E p5bE p1DNp3 H' x5E y5E p1E p4E1 p1DNp2 p4E2.
rewrite p4E2 p5bE in p4E1.
move: p1bE; rewrite p1E => [] [x1E y1E]; subst x1b y1b.
move: (p4E2); rewrite p5E => [] [x4E1 y4E1].
rewrite p5bE in p4E2.
have : (l' - l) * (x4 - x1) == 0.
  move: y5E; rewrite -{}x4E1 -y4E1 {}y4E => /eqP; rewrite -subr_eq0 => /eqP <-.
  apply/eqP; ring.
(rewrite mulf_eq0 => /orP[]; rewrite subr_eq0 => /eqP) => [l'E|x4E2].
- move: x4E1; rewrite x4E x5E l'E => /subrI x2Ex3.
  have [] := curve_elt_oppe e2 e3 x2Ex3; first by rewrite p2E p3E.
  rewrite -p2E -p3E => p2E1.
  have [p1ENp1|/eqP p1DNp1] := p1 =P oppe p1.
    have [[x1E y1E lE]|[x1Dx2 lE]] := H.
      case/eqP: p1DNp3.
      rewrite -p2E1 p1E p2E.
      by apply: curve_elt_irr.
    rewrite lE in l'E.
    have [[x1E y1E l'E1]|[x1Dx3 l'E1]] := H'.
      case/eqP: p1DNp2; rewrite p2E1 oppeK.
      by rewrite p1E p3E; apply: curve_elt_irr.
    rewrite l'E1 in l'E.
    move: p2E1; rewrite p2E p3E => [] [x2E y2E].
    apply: curve_elt_irr => //.
    subst x3 y2.
    apply/eqP; rewrite -subr_eq0; apply/eqP.
    move/eqP: l'E; rewrite -subr_eq0 => /eqP polE.
    rewrite (_ : 0 = 0 * (x1 - x2)); last by rewrite mul0r.
    by rewrite -polE; field; rewrite subr_eq0 eq_sym.
  rewrite -(oppeK p3) -p2E1.
  apply: addeI_oppe (_ : p1 != _) => //.
  by rewrite [in RHS]p2E1 oppeK.
case: (curve_elt_oppe e4 e1); rewrite ?p4E2 -?p1E // => p1Dp3E.
  apply: etrans (_ : inf_elt = _); last apply: sym_equal;
  by apply: (uniq_zeroe (_ : _ = p1)); rewrite addeC // -p4E1.
by apply: etrans (_ : adde (oppe p1) (oppe p1) = _); last apply: sym_equal;
   apply: adde_oppe_double_opp; rewrite -?p4E1.
Qed.

Theorem addeK p1 p2 : adde (adde p1 p2) (oppe p2) = p1.
Proof.
have [p1Dp2ENp2 | /eqP] := adde p1 p2 =P oppe p2.
  rewrite p1Dp2ENp2; apply/sym_equal/adde_oppe_double_opp.
  by rewrite addeC.
elim/adde_case: (adde p1 p2) => {p1 p2}// [p pDNp|p pDNp|p infDNNp||].
- by rewrite addeN.
- by rewrite adde0.
- by rewrite oppeK.
- move=> p1 x1 y1 e1 p2 x2 y2 e2 l p1E p2E p2E1 y1NZ lE x2E y2E p2DNp1.
  rewrite p2E1.
  apply: compat_addeK => //.
  rewrite p1E /=; apply/eqP => [] [y1E].
  suff: 2%:R * y1 == 0 by rewrite mulf_eq0 (negPf K2D0) (negPf y1NZ).
  by rewrite mulr_natl mulr2n [X in _ + X]y1E addrN.
- by rewrite -p2E1.
move=> p1 x1 y1 e1 p2 x2 y2 e2 p3 x3 y3 e3 l p1E
       p2E p3E p3E1 x1Dx2 lE x3E y3E.
move: p2E p3E p3E1; rewrite -[in p2 = _](oppeK p2) -[in adde _ p2](oppeK p2).
elim/adde_case: (adde p3 (oppe p2)) => {p3}// [p *||].
- apply/sym_equal/(uniq_zeroe (_ : _ = p)) => //.
  by rewrite -[in LHS](oppeK p).
- by move=> ? ? ? ? ? ? ? ? ?; rewrite eqxx.
move=> p4 x4 y4 e4 p5 x5 y5 e5 p6 x6 y6 e6 l0 -> -> -> _.
move=> x4Dx5 l0E x6E y6E [x5E Ny5E] [x4E y4E] _ _.
have y5E : y5 = - y2 by rewrite -Ny5E opprK.
rewrite p1E.
by apply: curve_elt_irr;
   rewrite ?y6E ?x6E ?l0E ?y5E ?y4E ?x5E ?x4E ?y3E ?x3E ?lE;
   move: (e1) (e2); field;
   rewrite subr_eq0 [in x2 != _]eq_sym ?x1Dx2 /=;
   apply/eqP => polE;
   case/eqP: x4Dx5;
   rewrite x4E x3E lE x5E;
   apply/eqP; rewrite -subr_eq0; apply/eqP;
   (rewrite (_ : 0 = 0 / -(x2 - x1) ^+ 2); last by rewrite mul0r);
   rewrite -polE; move: (e1) (e2); field;
   rewrite oppr_eq0 expf_eq0 /= subr_eq0 eq_sym (negPf x1Dx2).
Qed.

Theorem adde_shiftB p1 p2 p3 : adde p1 p2 = p3 -> p1 = adde p3 (oppe p2).
Proof.
move=> p1Dp2E; apply: addeI (_ : adde (oppe (oppe p2)) _ = _).
rewrite ![adde (oppe (oppe _)) _]addeC.
by rewrite addeK oppeK.
Qed.

Theorem degen_assoc p1 p2 p3 :
  [\/
    [\/ p1 = inf_elt, p2 = inf_elt | p3 = inf_elt],
    p1 = oppe p2 \/ p2 = oppe p3 |
    oppe p1 = adde p2 p3 \/ oppe p3 = adde p1 p2] ->
     adde p1 (adde p2 p3) = adde (adde p1 p2) p3.
Proof.
case=> [[->|->|->]|[->|->]|[Np1E|Np3E]];
    rewrite ?(adde0, add0e, addeN) //.
- rewrite ![adde (oppe p2) _]addeC addeN add0e.
  by rewrite [adde p2 _]addeC addeK. 
- rewrite -[X in _ = adde _ X]oppeK addeK.
  by rewrite [adde _ p3]addeC addeN adde0.
rewrite -Np1E addeN -(oppeK p1) Np1E oppe_adde.
  rewrite [adde (oppe p2) _]addeC -[X in _ = adde (adde _ X) _]oppeK addeK.
  by rewrite addeC addeN.
rewrite -[in LHS](oppeK p3) Np3E [adde p2 _]addeC.
rewrite oppe_adde -[X in adde _ (adde _ X)]oppeK addeK addeN.
by rewrite -(oppeK p3) Np3E addeN.
Qed.

Theorem spec4_assoc p1 p2 : adde p1 (adde p2 p2) = adde (adde p1 p2) p2.
Proof.
have [->|/eqP p1Dinf] := p1 =P inf_elt.
  by apply/degen_assoc/Or31/Or31.
have [->|/eqP p2Dinf] := p2 =P inf_elt.
  by apply/degen_assoc/Or32; right.
have [p2E|/eqP p2DNp2] := p2 =P oppe p2.
  by apply/degen_assoc/Or32; right.
have [p1E|/eqP p1DNp2] := p1 =P oppe p2.
  by apply/degen_assoc/Or32; left.
have [Np1E|/eqP Np1Dp2Dp2] := oppe p1 =P adde p2 p2.
  by apply/degen_assoc/Or33; left.
have [Np2E|/eqP Np2Dp1Dp2] := oppe p2 =P adde p1 p2.
  by apply/degen_assoc/Or33; right.
have [p1E|/eqP Np2Dp2Dp2] := p1 =P adde p2 p2.
  subst p1.
  apply: spec3_assoc.
  - apply/and4P; split => //.
    apply/eqP => p2Dp2Ep2; case/eqP : p2Dinf.
    by apply: uniq_zeroe (_ : _ = p2).
  - by apply/and3P; split.
  - apply/and4P; split => //.
    - apply/eqP => p2Dp2Dp2Einf; case/eqP : p1DNp2.
      by apply: uniq_oppe; rewrite addeC.
    - apply/eqP => p2Dp2Dp2Ep2; case/eqP : p1Dinf.
      by apply: uniq_zeroe (_ : _ p2).
    by rewrite eq_sym.
  apply/and3P; split => //.
  by rewrite eq_sym.
have [p2E|/eqP p2Dp1Dp2] := p2 =P adde p1 p2.
  rewrite [in LHS](uniq_zeroe (sym_equal p2E)).
  by rewrite -p2E.
have [->|/eqP p1Dp2] := p1 =P p2; first by rewrite addeC.
apply: spec2_assoc.
- by apply/and4P; split.
- by apply/and3P; split.
- apply/and4P; split => //.
  - apply/eqP => p1Dp2Einf; case/eqP: p1DNp2.
    by apply: uniq_oppe; rewrite addeC.
  - by rewrite eq_sym.
  by rewrite eq_sym.
apply/and4P; split => //.
  apply/eqP => p2Dp2Einf; case/eqP: p2DNp2.
  by apply: uniq_oppe.
apply/eqP => p1DNp2p2; case/eqP: Np1Dp2Dp2.
by rewrite p1DNp2p2 oppeK.
Qed.

(******************************************************************************)
(*                                                                            *)
(*       Associativity  for adde                                              *)
(*                                                                            *)
(******************************************************************************)


Theorem addeA p1 p2 p3 : adde p1 (adde p2 p3) = adde (adde p1 p2) p3.
Proof.
have [->|/eqP p1Dinf] := p1 =P inf_elt; first by apply/degen_assoc/Or31/Or31.
have [->|/eqP p2Dinf] := p2 =P inf_elt; first by apply/degen_assoc/Or31/Or32.
have [->|/eqP p3Dinf] := p3 =P inf_elt; first by apply/degen_assoc/Or31/Or33.
have [->|/eqP p1Dp2] := p1 =P p2.
  by rewrite ![adde p2 _]addeC -spec4_assoc addeC.
have [p1E|/eqP p1DNp2] := p1 =P oppe p2; first by apply/degen_assoc/Or32; left.
have [->|/eqP p2Dp3] := p2 =P p3; first by apply: spec4_assoc.
have [p2E|/eqP p2DNp3] := p2 =P oppe p3; first by apply/degen_assoc/Or32; right.
have [Np1E|/eqP Np1Dp2Dp3] := oppe p1 =P adde p2 p3.
  by apply/degen_assoc/Or33; left.
have [Np3E|/eqP Np3Dp1Dp2] := oppe p3 =P adde p1 p2.
  by apply/degen_assoc/Or33; right.
have [->|/eqP p1Dp2Dp3] := p1 =P adde p2 p3.
  apply: addeI (_ : adde (oppe p3) _ = _).
  rewrite spec4_assoc ![adde (oppe p3) _]addeC.
  by rewrite !addeK addeC.
have [->|/eqP p3Dp1Dp2] := p3 =P adde p1 p2.
  apply: addeI (_ : adde (oppe p1) _ = _).
  by rewrite spec4_assoc ![adde (oppe p1) _]addeC ![adde p1 _]addeC !addeK.
apply: spec1_assoc.
- apply/and4P; split => //.
- apply/and4P; split => //.
- apply/and4P; split => //.
  - apply/eqP => p1Dp2Dinf; case/eqP: p1DNp2.
    by apply: uniq_oppe; rewrite addeC.
  - by rewrite eq_sym.
  by rewrite eq_sym.
apply/and4P; split => //.
  apply/eqP=> p2Dp3Dinf; case/eqP: p2DNp3; apply: uniq_oppe.
  by rewrite addeC.
apply/eqP=> p1DNp2Dp3; case/eqP: Np1Dp2Dp3.
by rewrite p1DNp2Dp3 oppeK.
Qed.

Lemma addNe p : adde (oppe p) p = inf_elt.
Proof. by rewrite addeC addeN. Qed.

Definition elt_g (c : option (K * K)) : option elt :=
  if c is Some (x, y) then
     match y ^+ 2 =P x ^+ 3 + A * x + B with
      | ReflectT e => Some (curve_elt e)
      | ReflectF _ => None
     end else Some (inf_elt).

Definition elt_f e :  option (K * K) :=
  if e is curve_elt x y e then Some (x, y) else None.

Lemma elt_pcancel : pcancel elt_f elt_g.
Proof.
move=> [|x y e] //=; case: eqP => // p1.
by congr (Some _); apply: curve_elt_irr.
Qed.

Definition elt_choiceMixin := PcanChoiceMixin elt_pcancel.
Canonical elt_choiceType := 
   Eval hnf in ChoiceType elt elt_choiceMixin.

Definition elt_zmodMixin := ZmodMixin addeA addeC add0e addNe.
Canonical elt_zmodType := Eval hnf in ZmodType elt elt_zmodMixin.

End ELLIPTIC.

Section ELLIPTIC_FINE.

(******************************************************************************)
(*                                                                            *)
(*      K is finite                                                           *)
(*                                                                            *)
(******************************************************************************)

Variable K : finFieldType.
Variable A B : K.
Variable Eth : ell_theory A B.

Canonical felt_choiceType := elt_choiceType A B.
Canonical felt_zmodType := elt_zmodType Eth.

Open Scope ring_scope.

(******************************************************************************)
(*                                                                            *)
(*      Exact square root function                                            *)
(*                                                                            *)
(******************************************************************************)

Definition Kroot (r : K) := [pick r1 : K | r1 ^+ 2 == r].

Theorem Kroot_spec r :
  if Kroot r is Some r1 then r1 ^+ 2 = r else forall k, k ^+2 != r.
Proof.
by rewrite /Kroot; case: pickP => [x /eqP//| P k]; rewrite (P k).
Qed.

(******************************************************************************)
(*                                                                            *)
(*      List of elements of the curve                                         *)
(*                                                                            *)
(******************************************************************************)

Definition elt_enum := 
  pmap (elt_g A B) (enum [finType of option (K * K)%type]).

Lemma elt_enum_uniq : uniq elt_enum.
Proof.
have oK : ocancel (elt_g A B) (@elt_f K A B).
  by move=> [[x y]|] //=; case: eqP.
by apply: pmap_uniq oK _ (enum_uniq _).
Qed.

Lemma mem_elt_enum p : p \in elt_enum.
Proof.
rewrite mem_pmap; apply/mapP.
case: p => [|x y e]; first by exists None; rewrite ?mem_enum.
exists (Some (x, y)) => /=; first by rewrite mem_enum.
by case: eqP => // e1; congr (Some _); apply: curve_elt_irr.
Qed.

Definition elt_countMixin := PcanCountMixin (@elt_pcancel K A B).
Canonical elt_countType := 
   Eval hnf in CountType (elt A B) elt_countMixin.

Definition elt_finMixin :=
  Eval hnf in UniqFinMixin elt_enum_uniq mem_elt_enum.
Canonical elt_finType := Eval hnf in FinType (elt A B) elt_finMixin.

Lemma card_elt : (#|[finType of elt A B]| <= #|K|.*2.+1)%N.
Proof.
rewrite !cardT.
pose ff b x := if Kroot (x ^+ 3 +  A * x + B) is Some y 
             then elt_g A B (Some (x , if b then y else - y))
             else None.
pose l := inf_elt A B :: pmap (ff true) (enum K) ++ pmap (ff false) (enum K). 
apply: leq_trans (_ : size l <= _)%N; last first.
  by rewrite /= ltnS size_cat !size_pmap -addnn leq_add // count_size.
apply: uniq_leq_size (enum_uniq _) _ => [] [|x y e] iE.
  by rewrite in_cons eqxx.
rewrite in_cons mem_cat.
have := Kroot_spec (x ^+ 3 + A * x + B).
case E : Kroot => [y1|]; last by move=> /(_ y); rewrite -e eqxx.
move=> y1E.
have /eqP : (y ^+ 2 = y1 ^+ 2) by rewrite e.
rewrite !mem_pmap eqf_sqr => /orP[] /eqP y1E1.
  suff -> : Some (curve_elt e) = ff true x by rewrite map_f ?orbT ?mem_enum.
  rewrite /ff E /=; case: eqP => [p|[]//].
  by congr (Some _); apply: curve_elt_irr.
suff -> : Some (curve_elt e) = ff false x by rewrite map_f ?orbT ?mem_enum.
rewrite /ff E /=; case: eqP => [p|[]]; last by rewrite sqrrN.
by congr (Some _); apply: curve_elt_irr.
Qed.

End  ELLIPTIC_FINE.

(******************************************************************************)
(*                                                                            *)
(*      Projective version                                                    *)
(*                                                                            *)
(******************************************************************************)

Section PROJECTIVE.

Variable K : finFieldType.
Variable A B : K.
Variable Eth : ell_theory A B.

Open Scope ring_scope.

Local Notation elt := (elt A B).
Local Notation adde := (adde Eth).

Record pelt := mk_pelt {
  x: K;
  y: K;
  z: K;
  on_curve: y ^+ 2 * z = x ^+ 3 +  A * x * z ^+ 2 + B * z ^+ 3
}.

Theorem curve_pelt_irr x1 x2 y1 y2 z1 z2 e1 e2 :
 x1 = x2 -> y1 = y2 -> z1 = z2 -> @mk_pelt x1 y1 z1 e1 = @mk_pelt x2 y2 z2 e2.
Proof.
move=> x1E y1E z1E; subst x1 y1 z1.
congr mk_pelt.
apply: Eqdep_dec.eq_proofs_unicity => x y.
by case: (x =P y); [left | right].
Qed.

Lemma poppe_lem x y z :
  y ^+ 2 * z = x ^+ 3 + A * x * z ^+ 2 + B * z ^+ 3 ->
  (- y) ^+ 2 * z = x ^+ 3 + A * x * z ^+ 2 + B * z ^+ 3.
Proof. by rewrite sqrrN. Qed.

Definition eq_pelt p1 p2 :=
  let: mk_pelt x1 y1 z1 _ := p1 in
  let: mk_pelt x2 y2 z2 _ := p2 in [&& x1 == x2, y1 == y2 & z1 == z2].

Lemma eq_peltP : Equality.axiom eq_pelt.
Proof.
case => x y z e [x1 y1 z1 e1].
apply: (iffP idP) => [/and3P[/eqP xE /eqP yE /eqP zE]| 
                     /= [/eqP -> /eqP -> /eqP ->]] //.
by subst x y z; apply: curve_pelt_irr.
Qed.

Canonical pelt_eqMixin := EqMixin eq_peltP.
Canonical pelt_eqType := Eval hnf in EqType pelt pelt_eqMixin.

Definition poppe (p: pelt) := 
 let (x, y, z, e) := p in
 {| x := x; y := - y; z := z; on_curve := poppe_lem e |}.

Lemma adde_lem0 : 1 ^+ 2 * 0 = 0 ^+ 3 + A * 0 * 0 ^+ 2 + B * 0 ^+ 3.
Proof. by rewrite !expr0n !(addr0, mulr0, mul0r). Qed.

Lemma adde_lem_gen  x1 x2 y1 y2 z1 z2
  (e1 : y1 ^+ 2 * z1 = x1 ^+ 3 + A * x1 * z1 ^+ 2 + B * z1 ^+ 3)
  (e2 : y2 ^+ 2 * z2 = x2 ^+ 3 + A * x2 * z2 ^+ 2 + B * z2 ^+ 3) :
  let d1 := x2 * z1 in
  let d2 := x1 * z2  in
  let l := d1 - d2 in
  let dl := d1 + d2  in
  let m := y2 * z1 - y1 * z2 in
  let l2 := l * l  in
  let l3 := l2 * l in
  let m2 := m * m  in
  let x3 := z1 * z2 * m2 - l2 * dl in
  (z2 * l2 * (m * x1 - y1 * l) - m * x3) ^+ 2 * (z1 * z2 * l3) =
  (l * x3) ^+ 3 + A * (l * x3) * (z1 * z2 * l3) ^+ 2 + B * (z1 * z2 * l3) ^+ 3.
Proof. by move: e1 e2; ring. Qed.

Lemma adde_lem_tan x1 y1 z1 
                (e1 : y1 ^ 2 * z1 = x1 ^ 3 + A * x1 * z1 ^ 2 + B * z1 ^ 3) : 
  let m := 3%:R * x1 * x1 + A * z1 * z1 in
  let l := 2%:R * y1 * z1  in
  let m2 := m * m in
  let l2 := l * l in
  let l3 := l2 * l in
  let x3 := m2 * z1 - 2%:R * x1 * l2 in
  (l2 * (m * x1 - y1 * l) - m * x3) ^ 2 * (z1 * l3) =
  (l * x3) ^+ 3 + A * (l * x3) * (z1 * l3) ^+ 2 + B * (z1 * l3) ^+ 3.
Proof. by move: e1; ring. Qed.

(** doubling a point *)

Definition pdouble (p1 : pelt) := 
  let (x1, y1, z1, e1) := p1 in
  if z1 == 0 then p1 else
  let m' := 3%:R * x1 * x1 + A * z1 * z1 in
  let l' := 2%:R * y1 * z1 in
  let m'2 := m' * m' in
  let l'2 := l' * l' in
  let l'3 := l'2 * l' in
  let x3 := m'2 * z1 - 2%:R * x1 * l'2 in
  {| x := l' * x3; y := l'2 * (m' * x1 - y1 * l') - m' * x3;
     z := z1 * l'3; on_curve := adde_lem_tan e1 |}.
 
(* Adding two points *)
Definition padde (p1 p2: pelt) :=
  let (x1, y1, z1, e1) := p1 in
  if z1 == 0 then p2 else
  let (x2, y2, z2, e2) := p2 in
  if z2 == 0 then p1 else
  let d1 := x2 * z1 in
  let d2 := x1 * z2 in
  let l := d1 - d2 in
  let dl := d1 + d2 in
  let m := y2 * z1 - y1 * z2 in
  if l == 0 then
   (* we have p1 = p2 o p1 = -p2 *)
   if (m == 0) then
     (* we do 2p *)
    let m' := 3%:R * x1 * x1 + A * z1 * z1 in
    let l' := 2%:R * y1 * z1 in
    let m'2 := m' * m' in
    let l'2 := l' * l' in
    let l'3 := l'2 * l' in
    let x3 := m'2 * z1 - 2%:R * x1 * l'2 in
    @mk_pelt
          (l' * x3)
          (l'2 * (m' * x1 - y1 * l') - m' * x3)
          (z1 * l'3) (adde_lem_tan e1)
   else
     (* p - p *) @mk_pelt 0 1 0 adde_lem0
  else
     let l2 := l * l in
     let l3 := l2 * l in
     let m2 := m * m in
     let x3 := z1 * z2 * m2 - l2 * dl in
      @mk_pelt (l * x3)
             (z2 * l2 * (m * x1 - y1 * l) - m * x3)
             (z1 * z2 * l3)
             (adde_lem_gen e1 e2).

Definition wb (a : bool) : {b : bool | a = b} :=
   match a as b return a = b ->  ({b' : bool | a = b'}) with
      true => fun (h : a = true) => exist (fun b' => a = b') true h
     | false => fun (h : a = false) => exist (fun b' => a = b') false h
   end (refl_equal a).

Lemma pe2e_lem1 x1 y1 z1
      (e1 : y1 ^ 2 * z1 =
           x1 ^ 3 + A * x1 * z1 ^ 2 + B * z1 ^ 3)
      (z1NZ : z1 == 0 = false) :
      (y1 / z1) ^ 2  = (x1 / z1) ^ 3 + A * (x1 / z1) + B.
Proof. by move: e1; field; rewrite z1NZ. Qed.

(* Transfer function from projective to affine *)
Definition pe2e (p : pelt) :=
  let (x, y, z, e) := p in
  let (b, p) := wb (z == 0) in
  (if b  then fun=> inf_elt A B
   else fun p1 : (z == 0) = false => curve_elt (pe2e_lem1 e p1)) p.

(* Doubling is correct with respect to affine *)
Theorem pe2e_double p1 : pe2e (pdouble p1) = adde (pe2e p1) (pe2e p1).
Proof.
case: p1 => x1 y1 z1 e1.
rewrite /pdouble /pe2e.
case: wb => [] [] p; rewrite p.
  case: wb => [] [] p1 //=.
  by case/idP : p1; rewrite p.
have [y1Z|/eqP y1NZ] := y1 =P 0.
  case: wb  => [] [] p1; last first.
    by case/idP: p1; rewrite y1Z !(mul0r, mulr0).
  rewrite /adde.
  case: eqP => [x1z1E| [//]].
  case: eqP => [|[]] => //.
  by rewrite y1Z mul0r oppr0.
case: wb  => [] [] p1.
  move: (p1).
  by rewrite !mulf_eq0 p (negPf y1NZ) (negPf (K2D0 Eth)).
rewrite /adde.
case: eqP => [x1z1E| [//]].
case: eqP => y1z1E.
  have: (2%:R * (y1 / z1) == 0).
    by rewrite mulr_natl mulr2n [X in _ + X == _]y1z1E addrN.
  by rewrite !mulf_eq0 invr_eq0 p (negPf y1NZ) (negPf (K2D0 Eth)).
by apply: curve_elt_irr => /=; field; rewrite y1NZ p (K2D0 Eth).
Qed.

Theorem pe2e_add p1 p2 : pe2e (padde p1 p2) = adde (pe2e p1) (pe2e p2).
Proof.
case: p1 => x1 y1 z1 e1; case: p2 => x2 y2 z2 e2.
rewrite /padde /pe2e.
case: wb => [] [] p; rewrite /= p //.
case: wb => [] [] p1; rewrite /= p1.
  case: wb => [] [|p2]; first by rewrite p.
  by apply: curve_elt_irr.
case: eqP => x1z1E.
  case: eqP => y1z1E.
    case: eqP => [x2z1E|[]]; last first.
      by rewrite -[x2](divfK (_ : z2 != 0)) ?p1 // 
                 -x1z1E mulrAC divfK ?p // subrr.
    case: eqP => y2z1E /=; last first.
      by case: wb => [] [] p2; have := p2; rewrite eqxx.
    case: wb => [] [] p2 //.
    suff : 2%:R * y1 * z2 == 0.
      rewrite !mulf_eq0 (negPf (K2D0 Eth)) p1 orbF /= => /eqP y1Z.
      by case/idP: p2; rewrite y1Z !(mul0r, mulr0).
    apply/eqP.
    apply: etrans (_ : - (y2 * z1 - y1 * z2) + (y2 * z1 + (y1 / z1 * z1 * z2)) = 0).
      by field; rewrite p.
    by rewrite y2z1E oppr0 y1z1E mulrAC !mulNr divfK ?p1 // subrr add0r. 
  case: eqP => [x2z1E | []]; last first.
    by rewrite -[x2](divfK (_ : z2 != 0)) ?p1 // 
               -x1z1E mulrAC divfK ?p // subrr.
  case: eqP => y2z1E.
    have y1NZ : y1 != 0.
      apply/eqP => y1Z; case: y1z1E.
      have/eqP := y2z1E  .
      rewrite y1Z !mul0r subr0 mulf_eq0 p orbF => /eqP->.
      by rewrite mul0r oppr0.
    case: wb => [] [] p3.
      by move: (p3); rewrite !mulf_eq0 p (negPf (K2D0 Eth)) (negPf y1NZ).
    by apply: curve_elt_irr; field; rewrite p y1NZ (negPf (K2D0 Eth)).
  have: (y1 / z1) ^+ 2  == (y2 / z2) ^+ 2.
    apply/eqP.
    apply: etrans (_ : (y1 ^+ 2 * z1 / z1^+ 3 = _)); first by field; rewrite p.
    rewrite e1.
    apply: etrans (_ : (y2 ^+ 2 * z2 / z2^+ 3 = _)); last by field; rewrite p1.
    rewrite e2.
    have/eqP := x2z1E; rewrite subr_eq0 => /eqP.
    by field; rewrite p p1.
  rewrite eqf_sqr.
  have /eqP/negPf-> := y1z1E.
  rewrite GRing.eqr_div ?p ?p1 // -subr_eq0 -opprB oppr_eq0.
  by have /eqP/negPf-> := y2z1E.
case: eqP => [x2z1E|/eqP x2z1E].
  case: x1z1E; apply/eqP.
  by rewrite GRing.eqr_div ?p ?p1 // eq_sym -subr_eq0 x2z1E.
case: wb => [] [|p2].
  by rewrite !mulf_eq0 p p1 (negPf x2z1E).
by apply: curve_elt_irr; field; rewrite p p1 mulNr x2z1E.
Qed.

End PROJECTIVE.
