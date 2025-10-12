<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# mathcomp-extra

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/mathcomp-extra/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/mathcomp-extra/actions/workflows/docker-action.yml





Some extra material for mathcomp

  [Fibonacci and Lucas numbers](./fib.v)

  [Lower bound of lcm(1, 2, ..., n)](./lcm_lbound.v)

  [Definitions and some properties of matroids](./matroid.v)

  [Rsa algorithm](./rsa.v)

  [More lemmas about polynomials](./more_thm.v)

  [Polynomials modulo](./divpoly.v)

  [Binary gcd](./bgcdn.v)

  [Nth root for natural number](./rootn.v)

  [The aks algorithm](./aks_algo.v)  the algorithm as in Hing Lun Chan's PhD thesis

  [The aks correctness proof](./aks.v)  a transcription of Hing Lun Chan's proof

  [The proof of Lucas theorem for binomial](./digitn.v)

  [A formalisation of 2-player games](./tplayer.v) (in progress)

  [A formalisation of Fast Fourier Transform](./fft.v)

  [More theorems about tuples](./more_tuple.v)

  [A formalisation of sorting network](./nsort.v)
  
  [A formalisation of bitonic sort](./bitonic.v) 
  
  [A formalisation of Batcher odd or even sort](./batcher.v) 
  
  [A formalisation of Knuth exchange sort](./bjsort.v) 

  [A fun puzzle about a tricky integer function](./puzzleFF.v)

  [A port to mathcomp of the elliptic curve of CoqPrime](./elliptic.v)

  [A formalisation of some sudoku solvers ](./sudoku.v)
 
  [A formalisation of Montgomery reduction ](./montgomery.v)

  [A formalisation of Residue Number System](./rns.v)
  
  [Euler Criterion](./euler.v)

  [Trivial fact about the ultra hex number](./ultrahex.v)
  
  [Some facts about addition chain](./chain.v)

  [Definition of cycles from list in permutation](./lcycle.v)
  
  [The last digit of n^5 is the same than the one of n](./power5.v)

  [Definition of factorions and how many there are](./factorion.v)

  [Definition of circular primes and some properties](./cprime.v)

  [All prime numbers (except 2 and 3) are next to a multiple of 6](./prime6.v)

A note about sorting network is available [here](https://hal.inria.fr/hal-03585618).

A note about addition chain is available [here](https://hal.science/hal-04971933).

A note about factorions is available [here](https://inria.hal.science/hal-05265618).

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Rocq/Coq versions: 9.0 or later
- Additional dependencies:
  - [ Hierarchy Builder 1.9.1 or later](https://github.com/math-comp/hierarchy-builder)
  - [MathComp ssreflect 2.4.0 or later](https://math-comp.github.io)
  - [MathComp fingroup 2.4.0 or later](https://math-comp.github.io)
  - [MathComp algebra 2.4.0 or later](https://math-comp.github.io)
  - [MathComp field 2.4.0 or later](https://math-comp.github.io)
  - [MathComp zify 1.5.0+2.0+8.16 or later](https://github.com/math-comp/mczify)
  - [MathComp Algebra Tactics 1.2.5 or later](https://github.com/math-comp/algebra-tactics)
- Rocq/Coq namespace: `mathcomp-extra`
- Related publication(s): none

## Building and installation instructions

To build and install manually, do:

``` shell
git clone https://github.com/thery/mathcomp-extra.git
cd mathcomp-extra
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



