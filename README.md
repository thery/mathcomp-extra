<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# mathcomp-extra

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/mathcomp-extra/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/mathcomp-extra/actions?query=workflow:"Docker%20CI"





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

  [A fun puzzle about a tricky integer function ](./puzzleFF.v)

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.15 or later
- Additional dependencies:
  - [MathComp ssreflect 1.14 or later](https://math-comp.github.io)
  - [MathComp ssreflect 1.14 or later](https://math-comp.github.io)
  - [MathComp fingroup 1.14 or later](https://math-comp.github.io)
  - [MathComp algebra 1.14 or later](https://math-comp.github.io)
  - [MathComp field 1.14 or later](https://math-comp.github.io)
  - [MathComp zify 1.2 or later](https://github.com/math-comp/mczify)
- Coq namespace: `mathcomp-extra`
- Related publication(s): none

## Building and installation instructions
To build and install manually, do:

``` shell
git clone https://github.com/thery/mathcomp-extra.git
cd mathcomp-extra
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



