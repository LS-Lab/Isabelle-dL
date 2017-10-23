# dl-fml
Formalization of differential dynamic logic in Isabelle/HOL, including soundness theorem for uniform substitution calculus.
The results in this formalization are described in the paper:

1. Brandon Bohrer, Vincent Rahli, Ivana Vukotic, Marcus Völp and André Platzer.
[Formally verified differential dynamic logic](http://dx.doi.org/10.1145/3018610.3018616).
ACM SIGPLAN Conference on Certified Programs and Proofs, CPP 2017, Jan 16-17, 2017, Paris, France, pages 208-221, ACM, 2017.


Requirements:

Isabelle/HOL 2017:
  https://isabelle.in.tum.de/
  http://isabelle.in.tum.de/repos/isabelle/file/0d31dfa96aba/README_REPOSITORY

Archive of Formal Proofs (AFP) 2017 version:
    http://isabelle.in.tum.de/repos/isabelle/

This formalization relies primarily on the formalization of ordinary
differential equations given in the AFP, which differs from that in published work.
You will want to run Isabelle with the ODE heap image for faster proof-checking times:

$ <isabelle-root>/bin/isabelle jedit -d <afp-root>/thys/  -l HOL-ODE

You will need to build the HOL-ODE image first:

$ <isabelle-root>/bin/isabelle build -d <afp-root>/thys/ -b HOL-ODE 
