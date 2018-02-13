# Integer Interval Arithmetic for Computational Differential Dynamic Logic

This Isabelle theory defines the deep embedding of a fragment of Differential Dynamic Logic (dL), defines a real-valued and integer interval-valued semantics for dL, and shows the interval semantics is a sound overapproximation of the real semantics.

Notes to reviewer:
- This proof uses Isabelle2016. I tested it with a copy of Isabelle2016 obtained through the seL4 installation process, but it should work with the vanilla version as well.
   http://isabelle.in.tum.de/

- The directory Word_Lib is *NOT* a contribution of this paper. It is part of seL4, and I have included it in the review packet so that you do not have to install and build seL4 just for one silly library.

- The file Interval_Arithmetic.thy contains all of the new Isabelle code written for this paper. To check it, open it in Isabelle2016, e.g. launch the IDE with
 $<path-to-isabelle>/bin/isabelle jedit -l HOL and then open it in the GUI.
Scroll to the bottom and you should see the colored bar next to the right-hand side vertical scrollbar start to change. If it gets all the way to the bottom without any red appearing, the proof has checked successfully. This takes 2-3 minutes on my workstation; it is a relatively fast workstation. Purple means it's doing work and orange simply means there is a warning because it used type information to assist with parsing, which happens on almost every line of this proof.