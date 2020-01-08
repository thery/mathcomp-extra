From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Fixpoint bgcdn (k m n : nat) := 
  if m == 0 then n else
  if m == 1 then 1 else
  if n == 0 then m else
  if n == 1 then 1 else
  if k is k1.+1 then
    if odd m then 
      if odd n then
        let m1 := maxn m n in
        let n1 := minn m n in
        bgcdn k1 (m1 - n1)./2 n1
      else bgcdn k1 m n./2
    else 
      if odd n then bgcdn k1 m./2 n
      else (bgcdn k1 m./2 n./2).*2    
  else 1.

Lemma bgcdnC k m n : bgcdn k m n = bgcdn k n m.
Proof.
elim: k m n => [|k IH] [|[|m]] [|[|n]] //=.
case: odd; case: odd => //=.
  by rewrite maxnC minnC.
by rewrite IH.
Qed.

Lemma bgcdnE k1 k2 m n : 
  m < 2 ^ k1 -> n < 2 ^ k2 -> bgcdn (k1 + k2) m n = gcdn m n.
Proof.
elim: {k1 k2}_.+1 {-2}k1 {-2} k2 (ltnSn (k1 + k2)) m n =>
         // k IH [|k1] [|k2] Hk // [|[|m]] [|[|n]] //= Hm Hn.
- by rewrite gcd1n.
- by rewrite gcdn1.
move: (odd_double_half m) (odd_double_half n).
have [Om|Em] := boolP (odd _); have [On|En] := boolP (odd _);
     rewrite ?add0n ?add1n => //= mE nE.
- rewrite /maxn /minn; case: leqP => [nLm|mLn].
    have mDnE :  m.+2 - n.+2 = (m.+2 - n.+2)./2.*2.
      by rewrite -{1}(odd_double_half (_ - _)) odd_sub //= Om On.
    rewrite IH //.
      rewrite  -{2}[m.+2](subnK nLm) [RHS]gcdnC [RHS]gcdnDr [RHS]gcdnC.
      rewrite {2}mDnE -muln2 [LHS]gcdnC [RHS]gcdnC Gauss_gcdl //.
      by rewrite /coprime -gcdn_modl modn2 /= On gcd1n.
    rewrite -ltn_double -mDnE -mul2n -expnS (leq_trans _ Hm) //.
    by rewrite (leq_trans _ (_ : m.+2 < _)) // ltnS leq_subr.
  have m1Ln : m.+1 < n.+2 by apply: leq_trans mLn.
  have nDmE :  n.+2 - m.+2 = (n.+2 - m.+2)./2.*2.
    by rewrite -{1}(odd_double_half (_ - _)) odd_sub //= Om On.
  rewrite [(_ + _)%Nrec]addnC addSnnS IH //; last first.
  - rewrite -ltn_double -nDmE -mul2n -expnS (leq_trans _ Hn) //.
    by rewrite (leq_trans _ (_ : n.+2 < _)) // ltnS leq_subr.
  - by rewrite addnC addSnnS.
  rewrite  -{2}[n.+2](subnK m1Ln) gcdnDr.
  rewrite {2}nDmE -muln2 Gauss_gcdl 1?gcdnC //.
  by rewrite /coprime -gcdn_modl modn2 /= Om gcd1n.
- rewrite -[(_ + _)%Nrec]addSnnS IH //; last 2 first.
  - by rewrite addSnnS.
  - rewrite -nE expnS mul2n in Hn.
    by rewrite (ltn_double _.+1) in Hn.
  rewrite -{2}nE -doubleS -muln2 Gauss_gcdl //.
  by rewrite /coprime -gcdn_modl modn2 /= Om gcd1n.
- rewrite IH //; last first.
    rewrite -mE expnS mul2n in Hm.
    by rewrite (ltn_double _.+1) in Hm.
  rewrite -{2}mE.
  rewrite -doubleS -muln2 [LHS]gcdnC [RHS]gcdnC Gauss_gcdl //.
  by rewrite /coprime -gcdn_modl modn2 /= On gcd1n.
rewrite IH //; last 2 first.
- by rewrite -mE -doubleS expnS mul2n ltn_double in Hm.
- rewrite -nE -doubleS expnS mul2n ltn_double in Hn.
  by rewrite (leq_trans Hn) // leq_exp2l.
rewrite -{2}mE -{2}nE -!doubleS -!muln2.
by rewrite  muln_gcdl.
Qed.