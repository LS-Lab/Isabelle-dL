section \<open>dL Formalization\<close>

text \<open>
  We present a formalization of a uniform substitution calculus for
  differential dynamic logic (dL). In this calculus, the soundness of dL
  proofs is reduced to the soundness of a finite number of axioms, standard
  propositional rules and a central \textit{uniform substitution} rule for
  combining axioms. We present a formal definition for the denotational
  semantics of dL and prove the uniform substitution calculus sound by showing
  that all inference rules are sound with respect to the denotational
  semantics, and all axioms valid (true in every state and interpretation).

  See: Andre Platzer. A uniform substitution calculus for differential
  dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International
  Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings,
  volume 9195 of LNCS, pages 467-481. Springer, 2015.
\<close>

theory "dl" (* Theory names with Capital Letters! *)
imports
  Complex_Main HOL
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  "../afp/thys/Ordinary_Differential_Equations/Ordinary_Differential_Equations"
begin

lemma norm_axis: "norm (axis i x) = norm x"
  unfolding axis_def norm_vec_def
  by (simp add: if_distrib[where f=norm] setL2_def if_distrib[where f="\<lambda>x. x\<^sup>2"] setsum.If_cases)

lemma bounded_linear_axis: "bounded_linear (axis i)"
proof
  show "axis i (x + y) = axis i x + axis i y" "axis i (r *\<^sub>R x) = r *\<^sub>R axis i x" for x y :: "'a" and r
    by (auto simp: vec_eq_iff axis_def)
  show "\<exists>K. \<forall>x::'a. norm (axis i x) \<le> norm x * K"
    by (auto simp add: norm_axis intro!: exI[of _ 1])
qed

lemma has_derivative_vec:
  assumes "\<And>i. ((\<lambda>x. f i x) has_derivative (\<lambda>h. f' i h)) F"
  shows "((\<lambda>x. \<chi> i. f i x) has_derivative (\<lambda>h. \<chi> i. f' i h)) F"
proof -
  have *: "(\<chi> i. f i x) = (\<Sum>i\<in>UNIV. axis i (f i x))" "(\<chi> i. f' i x) = (\<Sum>i\<in>UNIV. axis i (f' i x))" for x
    by (simp_all add: axis_def setsum.If_cases vec_eq_iff)
  show ?thesis
    unfolding *
    by (intro has_derivative_setsum bounded_linear.has_derivative[OF bounded_linear_axis] assms)
qed

locale pointed_finite =
  fixes foo :: "'sv::finite"
  fixes baa :: "'si::finite"
  fixes vid1 :: 'sv
  fixes vid2 :: 'sv
  fixes vid3 :: 'sv
  fixes iid1 :: 'si
  fixes iid2 :: 'si
  fixes iid3 :: 'si
  type_synonym 'a Rvec = "real^('a::finite)"
  type_synonym 'a state = "'a Rvec \<times> 'a Rvec"
  type_synonym 'a simple_state = "'a Rvec"
  type_synonym 'a func_domain = "real^('a::finite)"

record ('a, 'b) interp =
  Functions       :: "'a \<Rightarrow> 'a func_domain \<Rightarrow> real"
  Predicates      :: "'a \<Rightarrow> 'a Rvec \<Rightarrow> bool"
  Contexts        :: "'a \<Rightarrow> 'b state set \<Rightarrow> 'b state set"
  Programs        :: "'a \<Rightarrow> ('b state * 'b state) set"
  ODEs            :: "'a \<Rightarrow> 'b simple_state \<Rightarrow> 'b simple_state"

fun FunctionFrechet :: "('a::finite, 'b::finite) interp \<Rightarrow> 'a \<Rightarrow> 'a Rvec \<Rightarrow> 'a func_domain \<Rightarrow> real"
where "FunctionFrechet I i = (THE f'. \<forall> x. (Functions I i has_derivative f' x) (at x))"

datatype ('a, 'b) trm =
 (* Program variable *)
  Var 'b
(* N.B. This is technically more expressive than true dL since most reals
 can't be written down. *)
| Const real
| Function 'a "'a \<Rightarrow> ('a, 'b) trm" ("$f")
| Plus "('a, 'b) trm" "('a, 'b) trm"
| Times "('a, 'b) trm" "('a, 'b) trm"
| DiffVar 'b ("$'")
| Differential "('a, 'b) trm"

datatype('a, 'b) ODE =
  OVar 'a
| OSing 'b "('a, 'b) trm"
| OProd "('a, 'b) ODE" "('a, 'b) ODE"

datatype ('a, 'b) hp =
 Pvar 'a                           ("$\<alpha>")
| Assign 'b "('a, 'b) trm"                (infixr ":=" 10)
| DiffAssign 'b "('a, 'b) trm"
| Test "('a, 'b) formula"                 ("?")
(* An ODE program is an ODE system with some evolution domain. *)
| EvolveODE "('a, 'b) ODE" "('a, 'b) formula"
| Choice "('a, 'b) hp" "('a, 'b) hp"            (infixl "\<union>\<union>" 10)
| Sequence "('a, 'b) hp"  "('a, 'b) hp"         (infixr ";;" 8)
| Loop "('a, 'b) hp"                      ("_**")

and ('a, 'b) formula =
 Geq "('a, 'b) trm" "('a, 'b) trm"
| Prop 'a "'a \<Rightarrow> ('a, 'b) trm"      ("$\<phi>")
| Not "('a, 'b) formula"            ("!")
| And "('a, 'b) formula" "('a, 'b) formula"    (infixl "&&" 8)
| Forall 'b "('a, 'b) formula"
| Box "('a, 'b) hp" "('a, 'b) formula"         ("([[_]]_)" 10)
(* DiffFormula \<phi> gives us the invariant for proving \<phi> by differential induction. *)
| DiffFormula "('a, 'b) formula"
(* Unary quantifier symbols *)
| InContext 'a "('a, 'b) formula"
| ConstP "'b state set"

fun Predicational :: "'a \<Rightarrow> ('a, 'b) formula"
where "Predicational P = InContext P (ConstP UNIV)"
  
record ('a, 'b) subst =
  (* Free variables introduced by the RHS for a given identifier *)
  SFV              :: "'a \<Rightarrow> ('b + 'b) set" 
  SFunctions       :: "'a \<rightharpoonup> (('a \<Rightarrow> ('a, 'b) trm) \<Rightarrow> ('a, 'b) trm)"
  SPredicates      :: "'a \<rightharpoonup> (('a \<Rightarrow> ('a, 'b) trm) \<Rightarrow> ('a, 'b) formula)"
  SContexts        :: "'a \<rightharpoonup> (('a, 'b) formula \<Rightarrow> ('a, 'b) formula)"
  SPrograms        :: "'a \<rightharpoonup> ('a, 'b) hp"
  SODEs            :: "'a \<rightharpoonup> ('a, 'b) ODE"

context pointed_finite
begin
subsection \<open>States\<close>
text \<open>We formalize a state S as a pair (S_V, S_V') : \<real>^n \<times> \<real>^n , where S_V assigns
  values to the program variables and S_V' assigns values to their
  differentials. Function constants are also formalized as having a fixed arity
  m (func_domain_dim) which may differ from n. If a function does not need to
  have m arguments, any remaining arguments can be uniformly set to 0
  throughout a proof, which simulates the affect of having functions of less
  arguments.

  Due to limitations in the analysis library, we fix n at the beginning of the
  theory, where the intention is that n should be increased to allow checking
  realistic proofs. For this to be a feasible option, the rest of this theory
  needs to be agnostic to n, which it currently is not.
  \<close>

subsection \<open>Syntax\<close>
text \<open>
  We define the syntax of dL terms, formulas and hybrid programs. We deviate
  slightly from the definitions given in CADE'15, which allows arbitrarily
  nested differentials, but with a surprising sem (e.g. (x')' is zero in
  every state). 

  In keeping with the CADE'15 presentation we currently make the simplifying
  assumption that all terms are smooth, and thus division and arbitrary
  exponentiation are absent from the syntax. Several other standard logical
  constructs are implemented as derived forms to reduce the soundness burden.
\<close>

inductive dfree :: "('a, 'b) trm \<Rightarrow> bool"
where
  dfree_Var: "dfree (Var i)"
| dfree_Const: "dfree (Const r)"
| dfree_Fun: "(\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> dfree \<theta>) \<Longrightarrow> dfree (Function i args)"
| dfree_Plus: "dfree \<theta>\<^sub>1 \<Longrightarrow> dfree \<theta>\<^sub>2 \<Longrightarrow> dfree (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dfree_Times: "dfree \<theta>\<^sub>1 \<Longrightarrow> dfree \<theta>\<^sub>2 \<Longrightarrow> dfree (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"

inductive dsafe :: "('a, 'b) trm \<Rightarrow> bool"
where
  dsafe_Var: "dsafe (Var i)"
| dsafe_Const: "dsafe (Const r)"
| dsafe_Fun: "(\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> dsafe \<theta>) \<Longrightarrow> dsafe (Function i args)"
| dsafe_Plus: "dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Times: "dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Diff: "dfree \<theta> \<Longrightarrow> dsafe (Differential \<theta>)"
| dsafe_DiffVar: "dsafe ($' i)"

lemma dfree_is_dsafe: "dfree \<theta> \<Longrightarrow> dsafe \<theta>"
  by (induction rule: dfree.induct) (auto intro: dsafe.intros)

fun ODE_dom::"('a, 'b) ODE \<Rightarrow> 'b set"
where 
  "ODE_dom (OVar c) =  {}"
| "ODE_dom (OSing x \<theta>) = {x}"
| "ODE_dom (OProd ODE1 ODE2) = ODE_dom ODE1 \<union> ODE_dom ODE2"

inductive osafe:: "('a, 'b) ODE \<Rightarrow> bool"
where
  osafe_Var:"osafe (OVar c)"
| osafe_Sing:"dfree \<theta> \<Longrightarrow> osafe (OSing x \<theta>)"
| osafe_Prod:"osafe ODE1 \<Longrightarrow> osafe ODE2 \<Longrightarrow> ODE_dom ODE1 \<inter> ODE_dom ODE2 = {} \<Longrightarrow> osafe (OProd ODE1 ODE2)"

inductive hpfree:: "('a, 'b) hp \<Rightarrow> bool"
and ffree::        "('a, 'b) formula \<Rightarrow> bool"
where
 "hpfree (Pvar x)"
| "dfree e \<Longrightarrow> hpfree (Assign x e)"
(* TODO: Not sure whether this should be allowed  *)
| "dfree e \<Longrightarrow> hpfree (DiffAssign x e)"
| "ffree P \<Longrightarrow> hpfree (Test P)" 
(* TODO: Not sure whether this should be allowed  *)
| "osafe ODE \<Longrightarrow> ffree P \<Longrightarrow> hpfree (EvolveODE ODE P)"
| "hpfree a \<Longrightarrow> hpfree b \<Longrightarrow> hpfree (Choice a b )"
| "hpfree a \<Longrightarrow> hpfree b \<Longrightarrow> hpfree (Sequence a b)"
| "hpfree a \<Longrightarrow> hpfree (Loop a)"
| "ffree f \<Longrightarrow> ffree (InContext C f)"
| "(\<And>arg. arg \<in> range args \<Longrightarrow> dfree arg) \<Longrightarrow> ffree (Prop p args)"
| "ffree p \<Longrightarrow> ffree (Not p)"
| "ffree p \<Longrightarrow> ffree q \<Longrightarrow> ffree (And p q)"
| "ffree p \<Longrightarrow> ffree (Forall x p)"
| "hpfree a \<Longrightarrow> ffree p \<Longrightarrow> ffree (Box a p)"
| "ffree (Predicational P)"
| "dfree t1 \<Longrightarrow> dfree t2 \<Longrightarrow> ffree (Geq t1 t2)"

inductive hpsafe:: "('a, 'b) hp \<Rightarrow> bool"
and fsafe:: "('a, 'b) formula \<Rightarrow> bool"
where
   "hpsafe (Pvar x)"
 | "dsafe e \<Longrightarrow> hpsafe (Assign x e)"
 | "dsafe e \<Longrightarrow> hpsafe (DiffAssign x e)"
 | "fsafe P \<Longrightarrow> hpsafe (Test P)" 
 | "osafe ODE \<Longrightarrow> fsafe P \<Longrightarrow> hpsafe (EvolveODE ODE P)"
 | "hpsafe a \<Longrightarrow> hpsafe b \<Longrightarrow> hpsafe (Choice a b )"
 | "hpsafe a \<Longrightarrow> hpsafe b \<Longrightarrow> hpsafe (Sequence a b)"
 | "hpsafe a \<Longrightarrow> hpsafe (Loop a)"

 | "dsafe t1 \<Longrightarrow> dsafe t2 \<Longrightarrow> fsafe (Geq t1 t2)"
 | "(\<And>arg. arg \<in> range args \<Longrightarrow> dsafe arg) \<Longrightarrow> fsafe (Prop p args)"
 | "fsafe p \<Longrightarrow> fsafe (Not p)"
 | "fsafe p \<Longrightarrow> fsafe q \<Longrightarrow> fsafe (And p q)"
 | "fsafe p \<Longrightarrow> fsafe (Forall x p)"
 | "hpsafe a \<Longrightarrow> fsafe p \<Longrightarrow> fsafe (Box a p)"
 | "ffree p \<Longrightarrow> fsafe (DiffFormula p)"
 | "fsafe f \<Longrightarrow> fsafe (InContext C f)"
 | "fsafe (Predicational P)"
  
lemma hp_induct [case_names Var Assign DiffAssign Test Evolve Choice Compose Star]:
   "(\<And>x. P ($\<alpha> x)) \<Longrightarrow>
    (\<And>x1 x2. P (x1 := x2)) \<Longrightarrow>
    (\<And>x1 x2. P (DiffAssign x1 x2)) \<Longrightarrow>
    (\<And>x. P (? x)) \<Longrightarrow>
    (\<And>x1 x2. P (EvolveODE x1 x2)) \<Longrightarrow>
    (\<And>x1 x2. P x1 \<Longrightarrow> P x2 \<Longrightarrow> P (x1 \<union>\<union> x2)) \<Longrightarrow>
    (\<And>x1 x2. P x1 \<Longrightarrow> P x2 \<Longrightarrow> P (x1 ;; x2)) \<Longrightarrow>
    (\<And>x. P x \<Longrightarrow> P x**) \<Longrightarrow>
     P hp"
by(induction rule: hp.induct) (auto)

type_synonym ('a, 'b) stuple = "('a \<Rightarrow> ('a, 'b) trm)"
type_synonym ('a, 'b) dtuple = "('a \<Rightarrow> ('a, 'b) trm)"

(* Derived forms *)
fun Or :: "('a, 'b) formula \<Rightarrow> ('a, 'b) formula \<Rightarrow> ('a, 'b) formula" (infixl "||" 7)
  where "Or P Q = Not (And (Not P) (Not Q))"

fun Implies :: "('a, 'b) formula \<Rightarrow> ('a, 'b) formula \<Rightarrow> ('a, 'b) formula" (infixr "\<rightarrow>" 10)
  where "Implies P Q = Or Q (Not P)"

fun Equiv :: "('a, 'b) formula \<Rightarrow> ('a, 'b) formula \<Rightarrow> ('a, 'b) formula" (infixl "\<leftrightarrow>" 10)
  where "Equiv P Q = Or (And P Q) (And (Not P) (Not Q))"

fun Exists :: "'b \<Rightarrow> ('a, 'b) formula \<Rightarrow> ('a, 'b) formula"
  where "Exists x P = Not (Forall x (Not P))"

fun Equals :: "('a, 'b) trm \<Rightarrow> ('a, 'b) trm \<Rightarrow> ('a, 'b) formula"
  where "Equals \<theta> \<theta>' = ((Geq \<theta> \<theta>') && (Geq \<theta>' \<theta>))"

fun Diamond :: "('a, 'b) hp \<Rightarrow> ('a, 'b) formula \<Rightarrow> ('a, 'b) formula" ("(\<langle>_\<rangle>_)" 10)
  where "Diamond \<alpha> P = Not(Box \<alpha> (Not P))"

subsection \<open>Denotational Semantics\<close>

text \<open>
  The central definitions for the denotational sem are states \nu,
  interpretations I and the interpretation functions [[\psi]]I, [[\theta]]I\nu,
  [[\alpha]]I, which are represented by the Isabelle functions fml_sem,
  term_sem and prog_sem, respectively.

  The additional functions term_list_sem and loop_sem are
  straightforward helper functions for the definitions of term_sem
  and prog_sem.

  To enable reasoning about derivatives of functions, our interpretations
  include a field FunctionFrechet specifying the Frechet derivative
  (FunctionFrechet f \<nu>) : \<real>^m -> \<real> for every function in every state. The
  proposition (is_interp I) asserts that every function is  differentiable and
  its derivative agrees everywhere with the derivative given by
  FunctionFrechet.
  \<close>

definition is_interp :: "('a::finite, 'b::finite) interp \<Rightarrow> bool"
  where "is_interp I \<equiv>
    \<forall>x. \<forall>i. (FDERIV (Functions I i) x :> (FunctionFrechet I i x))"

(* sterm_sem is the term sem for differential-free terms. *)
primrec sterm_sem :: "('a::finite, 'b::finite) interp \<Rightarrow> ('a, 'b) trm \<Rightarrow> 'b simple_state \<Rightarrow> real"
where
  "sterm_sem I (Var x) v = v $ x"
| "sterm_sem I (Function f args) v = Functions I f (\<chi> i. sterm_sem I (args i) v)"
| "sterm_sem I (Plus t1 t2) v = sterm_sem I t1 v + sterm_sem I t2 v"
| "sterm_sem I (Times t1 t2) v = sterm_sem I t1 v * sterm_sem I t2 v"
| "sterm_sem I (Const r) v = r"
| "sterm_sem I ($' c) v = undefined"
| "sterm_sem I (Differential d) v = undefined"

(* basis_vector i is the i'th basis vector for the standard Euclidean basis. *)
fun basis_vector :: "'a::finite \<Rightarrow> 'a Rvec"
where "basis_vector x = (\<chi> i. if x = i then 1 else 0)"

(* frechet I \<theta> \<nu> gives us the frechet derivative of the term \<theta> in the interpretation
 I at state \<nu> (containing only the unprimed variables). The frechet derivative is a
 linear map from the differential state \<nu> to reals.
 *)
primrec frechet :: "('a::finite, 'b::finite) interp \<Rightarrow> ('a, 'b) trm \<Rightarrow> 'b simple_state \<Rightarrow> 'b simple_state \<Rightarrow> real"
where
  "frechet I (Var x) v = (\<lambda>v'. v' \<bullet> basis_vector x)"
| "frechet I (Function f args) v =
    (\<lambda>v'. FunctionFrechet I f (\<chi> i. sterm_sem I (args i) v) (\<chi> i. frechet I (args i) v v'))"
| "frechet I (Plus t1 t2) v = (\<lambda>v'. frechet I t1 v v' + frechet I t2 v v')"
| "frechet I (Times t1 t2) v =
    (\<lambda>v'. sterm_sem I t1 v * frechet I t2 v v' + frechet I t1 v v' * sterm_sem I t2 v)"
| "frechet I (Const r) v = (\<lambda>v'. 0)"
| "frechet I ($' c) v = undefined"
| "frechet I (Differential d) v = undefined"

definition directional_derivative :: "('a::finite, 'b::finite) interp \<Rightarrow> ('a, 'b) trm \<Rightarrow> 'b state \<Rightarrow> real"
where "directional_derivative I t = (\<lambda>v. frechet I t (fst v) (snd v))"

(* Sem for terms that are allowed to contain differentials.
   Note there is some duplication with sterm_sem (hence the desire to combine the two).*)
primrec dterm_sem :: "('a::finite, 'b::finite) interp \<Rightarrow> ('a, 'b) trm \<Rightarrow> 'b state \<Rightarrow> real"
where
  "dterm_sem I (Var x) = (\<lambda>v. fst v $ x)"
| "dterm_sem I (DiffVar x) = (\<lambda>v. snd v $ x)"
| "dterm_sem I (Function f args) = (\<lambda>v. Functions I f (\<chi> i. dterm_sem I (args i) v))"
| "dterm_sem I (Plus t1 t2) = (\<lambda>v. (dterm_sem I t1 v) + (dterm_sem I t2 v))"
| "dterm_sem I (Times t1 t2) = (\<lambda>v. (dterm_sem I t1 v) * (dterm_sem I t2 v))"
| "dterm_sem I (Differential t) = (\<lambda>v. directional_derivative I t v)"
| "dterm_sem I (Const c) = (\<lambda>v. c)"

(* repv \<nu> x r replaces the value of (unprimed) variable x in the state \<nu> with r *)
fun repv :: "'b::finite state \<Rightarrow> 'b \<Rightarrow> real \<Rightarrow> 'b state"
where "repv v x r = ((\<chi> y. if x = y then r else vec_nth (fst v) y), snd v)"

(* repd \<nu> x' r replaces the value of (primed) variable x' in the state \<nu> with r *)
fun repd :: "'b::finite state \<Rightarrow> 'b \<Rightarrow> real \<Rightarrow> 'b state"
where "repd v x r = (fst v, (\<chi> y. if x = y then r else vec_nth (snd v) y))"  

fun ODE_sem:: "('a::finite,'b::finite) interp \<Rightarrow> ('a, 'b) ODE \<Rightarrow> 'b Rvec \<Rightarrow> 'b Rvec"
  where
  "ODE_sem I (OVar x) = ODEs I x"
| "ODE_sem I (OSing x \<theta>) =  (\<lambda>\<nu>. (\<chi> i. if i = x then sterm_sem I \<theta> \<nu> else 0))"
| "ODE_sem I (OProd ODE1 ODE2) = (\<lambda>\<nu>. ODE_sem I ODE1 \<nu> + ODE_sem I ODE2 \<nu>)"

(* Sem for formulas, differential formulas, programs, initial-value problems and loops.
   Loops and IVP's do not strictly have to have their own notion of sem, but for loops
   it was helpful to describe the sem recursively and for IVP's it was convenient to
   have ivp_sem as a helper function simply because ODE's are a little complicated.

   Differential formulas do actually have to have their own notion of sem, because
   the meaning of a differential formula (\<phi>)' depends on the syntax of the formula \<phi>:
   we can have two formulas \<phi> and \<psi> that have the exact same sem, but where
   (\<phi>)' and (\<psi>)' differ because \<phi> and \<psi> differ syntactically.
*)
definition Vagree :: "'b::finite state \<Rightarrow> 'b state \<Rightarrow> ('b + 'b) set \<Rightarrow> bool"
where "Vagree \<nu> \<nu>' V \<equiv>
   (\<forall>i. Inl i \<in> V \<longrightarrow> fst \<nu> $ i = fst \<nu>' $ i)
 \<and> (\<forall>i. Inr i \<in> V \<longrightarrow> snd \<nu> $ i = snd \<nu>' $ i)"

(* The bound variables of an ODE (which will also be included as free variables) *)
fun ODE_vars :: "('a, 'b) ODE \<Rightarrow> ('b + 'b) set"
where 
  "ODE_vars (OVar c) = UNIV"
| "ODE_vars (OSing x \<theta>) = {Inl x, Inr x}"
| "ODE_vars (OProd ODE1 ODE2) = ODE_vars ODE1 \<union> ODE_vars ODE2"

  
fun fml_sem  :: "('a::finite, 'b::finite) interp \<Rightarrow> ('a, 'b) formula \<Rightarrow> 'b state set" and
  diff_formula_sem  :: "('a::finite, 'b::finite) interp \<Rightarrow> ('a, 'b) formula \<Rightarrow> 'b state set" and
  prog_sem :: "('a::finite, 'b::finite) interp \<Rightarrow> ('a, 'b) hp \<Rightarrow> ('b state * 'b state) set"
where
  "fml_sem I (Geq t1 t2) = {v. dterm_sem I t1 v \<ge> dterm_sem I t2 v}"
| "fml_sem I (Prop P terms) = {\<nu>. Predicates I P (\<chi> i. dterm_sem I (terms i) \<nu>)}"
| "fml_sem I (Not \<phi>) = {v. v \<notin> fml_sem I \<phi>}"
| "fml_sem I (And \<phi> \<psi>) = fml_sem I \<phi> \<inter> fml_sem I \<psi>"
| "fml_sem I (Forall x \<phi>) = {v. \<forall>r. (repv v x r) \<in> fml_sem I \<phi>}"
| "fml_sem I (Box \<alpha> \<phi>) = {\<nu>. \<forall> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<longrightarrow> \<omega> \<in> fml_sem I \<phi>}"
| "fml_sem I (InContext c \<phi>) = Contexts I c (fml_sem I \<phi>)"
| "fml_sem I (DiffFormula p) = diff_formula_sem I p"
| "fml_sem I (ConstP S) = S"

| "diff_formula_sem I (Geq f g) = {v. dterm_sem I (Differential f) v \<ge> dterm_sem I (Differential g) v}"
| "diff_formula_sem I (Not p) = diff_formula_sem I p"
| "diff_formula_sem I (And p q) = diff_formula_sem I p \<inter> diff_formula_sem I p"
| "diff_formula_sem I  p = fml_sem I p"

| "prog_sem I (Pvar p) = Programs I p"
| "prog_sem I (Assign x t) = {(\<nu>, \<omega>). \<omega> = repv \<nu> x (dterm_sem I t \<nu>)}"
| "prog_sem I (DiffAssign x t) = {(\<nu>, \<omega>). \<omega> = repd \<nu> x (dterm_sem I t \<nu>)}"
| "prog_sem I (Test \<phi>) = {(\<nu>, \<nu>) | \<nu>. \<nu> \<in> fml_sem I \<phi>}"
| "prog_sem I (Choice \<alpha> \<beta>) = prog_sem I \<alpha> \<union> prog_sem I \<beta>"
| "prog_sem I (Sequence \<alpha> \<beta>) = prog_sem I \<alpha> O prog_sem I \<beta>"
| "prog_sem I (Loop \<alpha>) = (prog_sem I \<alpha>)\<^sup>*"
| "prog_sem I (EvolveODE ODE \<phi>) =
    (let
      ode = ODE_sem I ODE;
      xode = \<lambda>x. (x, ode x)
    in
    {(\<nu>, \<omega>) | \<nu> \<mu> \<omega> sol t.
      t \<ge> 0 \<and>
      \<mu> = xode (sol t) \<and>
      (Vagree \<nu> \<omega> (-ODE_vars ODE)) \<and>
      (Vagree \<nu> \<mu> (ODE_vars ODE)) \<and> 
      (sol solves_ode (\<lambda>_. ode)) {0 .. t} {x. xode x \<in> fml_sem I \<phi>} \<and>
      sol 0 = fst \<nu>})"

subsection \<open>Trivial Simplification Lemmas\<close>
text \<open>
 We often want to pretend the definitions in the sem are written slightly
 differently than they are. Since the simplifier has some trouble guessing that
 these are the right simplifications to do, we write them all out explicitly as
 lemmas, even though they prove trivially.
\<close>

lemma svar_case:
  "sterm_sem I (Var x) = (\<lambda>v. v $ x)"
  by auto

lemma sconst_case:
  "sterm_sem I (Const r) = (\<lambda>v. r)"
  by auto

lemma sfunction_case:
  "sterm_sem I (Function f args) = (\<lambda>v. Functions I f (\<chi> i. sterm_sem I (args i) v))"
  by auto

lemma splus_case:
  "sterm_sem I (Plus t1 t2) = (\<lambda>v. (sterm_sem I t1 v) + (sterm_sem I t2 v))"
  by auto

lemma stimes_case:
  "sterm_sem I (Times t1 t2) = (\<lambda>v. (sterm_sem I t1 v) * (sterm_sem I t2 v))"
  by auto

subsection \<open>Characterization of Term Derivatives\<close>
text \<open>
 This section builds up to a proof that in well-formed interpretations, all
 terms have derivatives, and those derivatives agree with the expected rules
 of derivatives. In particular, we show the [frechet] function given in the
 denotational sem is the true Frechet derivative of a term. From this
 theorem we can recover all the standard derivative rules as corollaries.
\<close>

lemma inner_prod_eq:
  fixes i::"'a::finite"
  shows "(\<lambda>(v::'a Rvec). v \<bullet> basis_vector i) = (\<lambda>(v::'a Rvec). v $ i)"
  unfolding cart_eq_inner_axis basis_vector.simps axis_def by (simp add: eq_commute)

theorem svar_deriv:
  fixes x:: "'sv::finite" and \<nu>:: "'sv Rvec" and F::"real filter"
  shows "((\<lambda>v. v $ x) has_derivative (\<lambda>v'. v' \<bullet> (\<chi> i. if x = i then 1 else 0))) (at \<nu>)"
proof -
  let ?f = "(\<lambda>v. v)"
  let ?f' = "(\<lambda>v'. v')"
  let ?g = "(\<lambda>v. basis_vector x)"
  let ?g' = "(\<lambda>v. 0)"
  have id_deriv: "(?f has_derivative ?f') (at \<nu>) "
  by (rule has_derivative_ident)
  have const_deriv: "(?g has_derivative ?g') (at \<nu>)"
  by (rule has_derivative_const)
  have inner_deriv:"((\<lambda>x. inner (?f x) (?g x)) has_derivative
                     (\<lambda>h. inner (?f \<nu>) (?g' h) + inner (?f' h) (?g \<nu>))) (at \<nu>)"
  by (intro has_derivative_inner [OF id_deriv const_deriv])

  from inner_prod_eq
  have left_eq: "(\<lambda>x. inner (?f x) (?g x)) = (\<lambda>v. vec_nth v x)"
  by (auto)
  from inner_deriv and inner_prod_eq
  have better_deriv:"((\<lambda>v. vec_nth v x) has_derivative
                     (\<lambda>h. inner (?f \<nu>) (?g' h) + inner (?f' h) (?g \<nu>))) (at \<nu>)"
  by (metis (no_types, lifting) UNIV_I has_derivative_transform)
  have deriv_eq: "(\<lambda>h. inner (?f \<nu>) (?g' h) + inner (?f' h) (?g \<nu>))
    = (\<lambda>v'. inner v' (\<chi> i. if x = i then 1 else 0))"
  by(auto)
  from better_deriv and deriv_eq show ?thesis by (auto)
qed

lemma function_case_inner:
  assumes good_interp:
    "(\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x))"
  assumes IH:"((\<lambda>v. \<chi> i. sterm_sem I (args i) v)
             has_derivative (\<lambda> v. (\<chi> i. frechet I (args i) \<nu> v))) (at \<nu>)"
  shows  "((\<lambda>v. Functions I f (\<chi> i. sterm_sem I (args i) v))
            has_derivative (\<lambda>v. frechet I ($f f args) \<nu> v)) (at \<nu>)"
proof -
  let ?h = "(\<lambda>v. Functions I f (\<chi> i. sterm_sem I (args i) v))"
  let ?h' = "frechet I ($f f args) \<nu>"
  let ?g = "(\<lambda>v. \<chi> i. sterm_sem I (args i) v)"
  let ?g' = "(\<lambda>v. \<chi> i. frechet I (args i) \<nu> v)"
  let ?f = "(\<lambda>y. Functions I f y)"
  let ?f' = "FunctionFrechet I f (?g \<nu>)"
  have hEqFG:  "?h  = ?f  o ?g" by (auto)
  have hEqFG': "?h' = ?f' o ?g'"
    proof -
      have frechet_def:"frechet I (Function f args) \<nu>
          = (\<lambda>v'. FunctionFrechet I f (?g \<nu>) (\<chi> i. frechet I (args i) \<nu> v'))"
      by (auto)
      have composition:
        "(\<lambda>v'. FunctionFrechet I f (?g \<nu>) (\<chi> i. frechet I (args i) \<nu> v'))
      = (FunctionFrechet I f (?g \<nu>)) o (\<lambda> v'. \<chi> i. frechet I (args i) \<nu> v')"
      by (auto)
      from frechet_def and composition show ?thesis by (auto)
    qed
  have fDeriv: "(?f has_derivative ?f') (at (?g \<nu>))"
    using  good_interp is_interp_def by blast
  from IH have gDeriv: "(?g has_derivative ?g') (at \<nu>)" by (auto)
  from fDeriv and gDeriv
  have composeDeriv: "((?f o ?g) has_derivative (?f' o ?g')) (at \<nu>)"
    using diff_chain_at good_interp by blast
  from hEqFG hEqFG' composeDeriv show ?thesis by (auto)
qed

lemma func_lemma2:"\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x) \<Longrightarrow>
    (\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> (sterm_sem I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)) \<Longrightarrow>
    ((\<lambda>v. Functions I f (vec_lambda(\<lambda>i. sterm_sem I (args i) v))) has_derivative frechet I ($f f args) \<nu>) (at \<nu>)"
proof -
  assume a1: "\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x)"
  assume a2: "\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> (sterm_sem I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)"
  have "\<forall>f fa v. (\<exists>fb. \<not> (f (fb::'a) has_derivative fa fb (v::(real, 'a) vec)) (at v)) \<or> ((\<lambda>v. (\<chi> fa. (f fa v::real))) has_derivative (\<lambda>va. (\<chi> f. fa f v va))) (at v)"
    using has_derivative_vec by force
  then have "((\<lambda>v. \<chi> f. sterm_sem I (args f) v) has_derivative (\<lambda>v. \<chi> f. frechet I (args f) \<nu> v)) (at \<nu>)"
    by (auto simp add: a2 has_derivative_vec)
  then show "((\<lambda>v. Functions I f (vec_lambda(\<lambda>f. sterm_sem I (args f) v))) has_derivative frechet I ($f f args) \<nu>) (at \<nu>)"
    using a1 function_case_inner by blast
qed

lemma func_lemma:
  "is_interp I \<Longrightarrow>
  (\<And>\<theta> :: ('a::finite, 'b::finite) trm. \<theta> \<in> range args \<Longrightarrow> (sterm_sem I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)) \<Longrightarrow>
  (sterm_sem I ($f f args) has_derivative frechet I ($f f args) \<nu>) (at \<nu>)"
apply(simp only: sfunction_case is_interp_def function_case_inner)
apply(erule func_lemma2)
apply(auto)
done

lemma dfree_vac1: "\<not> dfree ($' var)"
  by (auto elim: dfree.cases)

lemma dfree_vac2: "\<not> dfree (Differential d)"
  by (auto elim: dfree.cases)

(* Our syntactically-defined derivatives of terms agree with the actual derivatives of the terms.
 Since our definition of derivative is total, this gives us that derivatives are "decidable" for
 terms (modulo computations on reals) and that they obey all the expected identities, which gives
 us the axioms we want for differential terms essentially for free.
 *)
lemma frechet_correctness:
  fixes I :: "('si, 'sv) interp" and \<nu>
  assumes good_interp: "is_interp I"
  shows "dfree \<theta> \<Longrightarrow> FDERIV (sterm_sem I \<theta>) \<nu> :> (frechet I \<theta> \<nu>)"
proof (induct rule: dfree.induct)
  case dfree_Var then show ?case
    by (simp add: svar_case svar_deriv)
next
  case (dfree_Fun args i) with good_interp show ?case
    by (intro func_lemma) auto
qed auto

section \<open>Prerequisites for Substitution\<close>
subsection \<open>Variable Binding Definitions\<close>
text\<open>
  We represent the (free or bound or must-bound) variables of a term as an (id + id) set,
  where all the (Inl x) elements are unprimed variables x and all the (Inr x) elements are
  primed variables x'.
  \<close>

(* Bound variables of a formula
   Bound variables of a program *)
fun BVF :: "('a, 'b) formula \<Rightarrow> ('b + 'b) set"
and BVP :: "('a, 'b) hp \<Rightarrow> ('b + 'b) set"
where
  "BVF (Geq f g) = {}"
| "BVF (Prop p dfun_args) = {}"
| "BVF (Not p) = BVF p"
| "BVF (And p q) = BVF p \<union> BVF q"
| "BVF (Forall x p) = {Inl x} \<union> BVF p"
| "BVF (Box \<alpha> p) = BVP \<alpha> \<union> BVF p"
| "BVF (DiffFormula p) = BVF p"
| "BVF (InContext C p) = UNIV"

| "BVP (Pvar a) = UNIV"
| "BVP (Assign x \<theta>) = {Inl x}"
| "BVP (DiffAssign x \<theta>) = {Inr x}"
| "BVP (Test \<phi>) = {}"
| "BVP (EvolveODE ODE \<phi>) = ODE_vars ODE"
| "BVP (Choice \<alpha> \<beta>) = BVP \<alpha> \<union> BVP \<beta>"
| "BVP (Sequence \<alpha> \<beta>) = BVP \<alpha> \<union> BVP \<beta>"
| "BVP (Loop \<alpha>) = BVP \<alpha>"

(* Must-bound variables (of a program)*)
fun MBV :: "('a, 'b) hp \<Rightarrow> ('b + 'b) set"
where
  "MBV (Pvar a) = {}"
| "MBV (Choice \<alpha> \<beta>) = MBV \<alpha> \<inter> MBV \<beta>"
| "MBV (Sequence \<alpha> \<beta>) = MBV \<alpha> \<union> MBV \<beta>"
| "MBV (Loop \<alpha>) = {}"
| "MBV \<alpha> = BVP \<alpha>"

fun primify :: "('a + 'a) \<Rightarrow> ('a + 'a) set"
where
  "primify (Inl x) = {Inl x, Inr x}"
| "primify (Inr x) = {Inl x, Inr x}"

(* Free variables of a term *)
primrec FVT :: "('a, 'b) trm \<Rightarrow> ('b + 'b) set"
where
  "FVT (Var x) = {Inl x}"
| "FVT (Const x) = {}"
| "FVT (Function f args) = (\<Union>i. FVT (args i))"
| "FVT (Plus f g) = FVT f \<union> FVT g"
| "FVT (Times f g) = FVT f \<union> FVT g"
| "FVT (Differential f) = (\<Union>x \<in> (FVT f). primify x)"
| "FVT (DiffVar x) = {Inr x}"

fun FVDiff :: "('a, 'b) trm \<Rightarrow> ('b + 'b) set"
where "FVDiff f = (\<Union>x \<in> (FVT f). primify x)"

lemma primify_contains:"x \<in> primify x"
by (cases "x") auto

lemma FVDiff_sub:"FVT f \<subseteq> FVDiff f"
by (auto simp add:  primify_contains)

(* Free variables of an ODE includes both the bound variables and the terms *)
fun FVO :: "('a, 'b) ODE \<Rightarrow> ('b + 'b) set"
  where
  "FVO (OVar c) = {}"
| "FVO (OSing x \<theta>) = FVT \<theta>"
| "FVO (OProd ODE1 ODE2) = FVO ODE1 \<union> FVO ODE2"

(* Free variables of a formula *)
(* Free variables of a program *)
fun FVF :: "('a, 'b) formula \<Rightarrow> ('b + 'b) set"
and FVP :: "('a, 'b) hp \<Rightarrow> ('b + 'b) set"
where
   "FVF (Geq f g) = FVT f \<union> FVT g"
 | "FVF (Prop p args) = (\<Union>i. FVT (args i))"
 | "FVF (Not p) = FVF p"
 | "FVF (And p q) = FVF p \<union> FVF q"
 | "FVF (Forall x p) = FVF p - {Inl x}"
 | "FVF (Box \<alpha> p) =   FVF p - MBV \<alpha>"
 | "FVF (DiffFormula p) = FVF p"
 | "FVF (InContext C p) = UNIV"
 | "FVF (ConstP P) = {}"
 | "FVP (Pvar a) = UNIV"
 | "FVP (Assign x \<theta>) = FVT \<theta>"
 | "FVP (DiffAssign x \<theta>) = FVT \<theta>"
 | "FVP (Test \<phi>) = FVF \<phi>"
 | "FVP (EvolveODE ODE \<phi>) = ODE_vars ODE \<union> FVO ODE \<union> FVF \<phi>"
 | "FVP (Choice \<alpha> \<beta>) = FVP \<alpha> \<union> FVP \<beta>"
 | "FVP (Sequence \<alpha> \<beta>) = (FVP \<alpha> \<union> FVP \<beta>) - (MBV \<alpha>)"
 | "FVP (Loop \<alpha>) = FVP \<alpha>"

primrec SIGT :: "('a, 'b) trm \<Rightarrow> 'a set"
where
  "SIGT (Var var) = {}"
| "SIGT (Const r) = {}"
| "SIGT (Function var f) = {var} \<union> (\<Union>i. SIGT (f i))"
| "SIGT (Plus t1 t2) = SIGT t1 \<union> SIGT t2"
| "SIGT (Times t1 t2) = SIGT t1 \<union> SIGT t2"
| "SIGT (DiffVar x) = {}"
| "SIGT (Differential t) = SIGT t"

primrec SIGO   :: "('a, 'b) ODE \<Rightarrow> 'a set"
where
  "SIGO (OVar c) = {c}"
| "SIGO (OSing x \<theta>) = SIGT \<theta>"
| "SIGO (OProd ODE1 ODE2) = SIGO ODE1 \<union> SIGO ODE2"
  
primrec SIGP   :: "('a, 'b) hp      \<Rightarrow> 'a set"
and     SIGF   :: "('a, 'b) formula \<Rightarrow> 'a set"
where
  "SIGP (Pvar var) = {}"
| "SIGP (Assign var t) = SIGT t"
| "SIGP (DiffAssign var t) = SIGT t"
| "SIGP (Test p) = SIGF p"
| "SIGP (EvolveODE ODE p) = SIGF p \<union> SIGO ODE"
| "SIGP (Choice a b) = SIGP a \<union> SIGP b"
| "SIGP (Sequence a b) = SIGP a \<union> SIGP b"
| "SIGP (Loop a) = SIGP a"
| "SIGF (Geq t1 t2) = SIGT t1 \<union> SIGT t2"
| "SIGF (Prop var args) = {var} \<union> (\<Union>i. SIGT (args i))"
| "SIGF (Not p) = SIGF p"
| "SIGF (And p1 p2) = SIGF p1 \<union> SIGF p2"
| "SIGF (Forall var p) = SIGF p"
| "SIGF (Box a p) = SIGP a \<union> SIGF p"
| "SIGF (DiffFormula p) = SIGF p"
| "SIGF (InContext var p) = {var} \<union> SIGF p"
| "SIGF (ConstP S) = {}"

(* TODO: Distinguish identifiers for functions, predicates, etc*)
definition Iagree :: "('a::finite, 'b::finite) interp \<Rightarrow> ('a::finite, 'b::finite) interp \<Rightarrow> 'a set \<Rightarrow> bool"
where "Iagree I J V \<equiv>
  (\<forall>i\<in>V.(Functions I i = Functions J i)
      \<and> (Predicates I i = Predicates J i)
      \<and> (Contexts I i = Contexts J i)
      \<and> (Programs I i = Programs J i))"

lemma agree_nil:"Vagree \<nu> \<omega> {}"
by (auto simp add: Vagree_def)

lemma agree_supset:"A \<supseteq> B \<Longrightarrow> Vagree \<nu> \<nu>' A \<Longrightarrow> Vagree \<nu> \<nu>' B"
by (auto simp add: Vagree_def)

lemma union_supset1:"A \<union> B \<supseteq> A"
by (auto)

lemma fvdiff_plus1:"FVDiff (Plus t1 t2) = FVDiff t1 \<union> FVDiff t2"
by (auto)

lemma agree_func_fvt:"Vagree \<nu> \<nu>' (FVT (Function f args)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVT (args i))"
by (auto simp add: union_supset1 agree_supset Vagree_def)

lemma agree_plus1:"Vagree \<nu> \<nu>' (FVDiff (Plus t1 t2)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff t1)"
proof -
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Plus t1 t2))"
  have agree':"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i) \<union> (\<Union>i\<in>FVT t2. primify i))"
  using fvdiff_plus1 FVDiff.simps agree by (auto)
  have agreeL:"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i))"
  using agree' agree_supset union_supset1 by (blast)
  show "Vagree \<nu> \<nu>' (FVDiff t1)" using agreeL by (auto)
qed

lemma agree_plus2:"Vagree \<nu> \<nu>' (FVDiff (Plus t1 t2)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff t2)"
proof -
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Plus t1 t2))"
  have agree':"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i) \<union> (\<Union>i\<in>FVT t2. primify i))"
  using fvdiff_plus1 FVDiff.simps agree by (auto)
  have agreeR:"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t2. primify i))"
  using agree' agree_supset union_supset1 by (blast)
  show "Vagree \<nu> \<nu>' (FVDiff t2)" using agreeR by (auto)
qed

lemma agree_times1:"Vagree \<nu> \<nu>' (FVDiff (Times t1 t2)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff t1)"
proof -
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Times t1 t2))"
  have agree':"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i) \<union> (\<Union>i\<in>FVT t2. primify i))"
  using fvdiff_plus1 FVDiff.simps agree by (auto)
  have agreeL:"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i))"
  using agree' agree_supset union_supset1 by (blast)
  show "Vagree \<nu> \<nu>' (FVDiff t1)" using agreeL by (auto)
qed

lemma agree_times2:"Vagree \<nu> \<nu>' (FVDiff (Times t1 t2)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff t2)"
proof -
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Times t1 t2))"
  have agree':"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i) \<union> (\<Union>i\<in>FVT t2. primify i))"
  using fvdiff_plus1 FVDiff.simps agree by (auto)
  have agreeR:"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t2. primify i))"
  using agree' agree_supset union_supset1 by (blast)
  show "Vagree \<nu> \<nu>' (FVDiff t2)" using agreeR by (auto)
qed

lemma agree_func:"Vagree \<nu> \<nu>' (FVDiff ($f var args)) \<Longrightarrow> (\<And>i. Vagree \<nu> \<nu>' (FVDiff (args i)))"
proof -
  assume agree:"Vagree \<nu> \<nu>' (FVDiff ($f var args))"
  have agree':"Vagree \<nu> \<nu>' ((\<Union>i. (\<Union>j \<in>(FVT (args i)). primify j)))"
  using fvdiff_plus1 FVDiff.simps agree by (auto)
  fix i :: 'b
  have "\<And>S. \<not> S \<subseteq> (\<Union>f. UNION (FVT (args f)) primify) \<or> Vagree \<nu> \<nu>' S"
    using agree' agree_supset by blast
  then have "\<And>f. f \<notin> UNIV \<or> Vagree \<nu> \<nu>' (UNION (FVT (args f)) primify)"
    by blast
  then show "Vagree \<nu> \<nu>' (FVDiff (args i))"
    by simp
qed

lemma agree_trans:"Vagree \<nu> \<mu> A \<Longrightarrow> Vagree \<mu> \<omega> B \<Longrightarrow> Vagree \<nu> \<omega> (A \<inter> B)"
by (auto simp add: Vagree_def)

lemma agree_refl:"Vagree \<nu> \<nu> A"
by (auto simp add: Vagree_def)


lemma
  has_vector_derivative_zero_constant:
  assumes "convex s"
  assumes "\<And>x. x \<in> s \<Longrightarrow> (f has_vector_derivative 0) (at x within s)"
  obtains c where "\<And>x. x \<in> s \<Longrightarrow> f x = c"
  using has_derivative_zero_constant[of s f] assms
  by (auto simp: has_vector_derivative_def)

lemma
  has_vderiv_on_zero_constant:
  assumes "convex s"
  assumes "(f has_vderiv_on (\<lambda>h. 0)) s"
  obtains c where "\<And>x. x \<in> s \<Longrightarrow> f x = c"
  using has_vector_derivative_zero_constant[of s f] assms
  by (auto simp: has_vderiv_on_def)

lemma constant_when_zero:
  fixes v::"real \<Rightarrow> (real, 'i::finite) vec"
  assumes x0: "(v 0) $ i = x0"
  assumes sol: "(v solves_ode f) UNIV UNIV"
  assumes f0: "\<And>t x. f t x $ i = 0"
  assumes "0 \<le> t"
  shows "v t $ i = x0"
proof -
  from solves_odeD[OF sol]
  have deriv: "(v has_vderiv_on (\<lambda>t. f t (v t))) UNIV" by simp
  then have "((\<lambda>t. v t $ i) has_vderiv_on (\<lambda>t. 0)) UNIV"
    using f0
    by (auto simp: has_vderiv_on_def has_vector_derivative_def cart_eq_inner_axis
      intro!: derivative_eq_intros)
  from has_vderiv_on_zero_constant[OF convex_UNIV this]
  obtain c where "\<And>x. x \<in> UNIV \<Longrightarrow> v x $ i = c" by blast
  with x0 have "c = x0" "v t $ i = c"using \<open>0 \<le> t\<close> by auto
  then show ?thesis by simp
qed

lemma example:
  fixes x t::real and i::'sv
  assumes "t > 0"
  shows "x = (ll_on_open.flow UNIV (\<lambda>t. \<lambda>x. \<chi> (i::'sv). 0) UNIV 0 (\<chi> i. x) t) $ i"
proof -
  let ?T = UNIV
  let ?f = "(\<lambda>t. \<lambda>x. \<chi> i::'sv. 0)"
  let ?X = UNIV
  let ?t0.0 = 0
  let ?x0.0 = "\<chi> i::'sv. x"
  interpret ll: ll_on_open "UNIV" "(\<lambda>t x. \<chi> i::'sv. 0)" UNIV
    apply unfold_locales
    using gt_ex lipschitz_constI
    by (force simp: interval_def continuous_on_def local_lipschitz_def)+
  have foo1:"?t0.0 \<in> ?T" by auto
  have foo2:"?x0.0 \<in> ?X" by auto
  let ?v = "ll.flow  ?t0.0 ?x0.0"
  from ll.flow_solves_ode[OF foo1 foo2]
  have solves:"(ll.flow  ?t0.0 ?x0.0 solves_ode ?f) (ll.existence_ivl  ?t0.0 ?x0.0) ?X"  by (auto)
  then have solves:"(?v solves_ode ?f) (ll.existence_ivl  ?t0.0 ?x0.0) ?X" by auto
  have thex0: "(?v ?t0.0) $ (i::'sv) = x" by auto
  have sol_help: "(?v solves_ode ?f) (ll.existence_ivl  ?t0.0 ?x0.0) ?X" using solves by auto
  have ivl:"ll.existence_ivl ?t0.0 ?x0.0 = UNIV"
    by (rule ll.existence_ivl_eq_domain)
     (auto intro!: exI[where x=0] simp: vec_eq_iff)
  have sol: "(?v solves_ode ?f) UNIV ?X" using solves ivl by auto
  have thef0: "\<And>t x. ?f t x $ i = 0" by auto
  have gre:"0 \<le> t" using \<open>0 < t\<close> by auto
  from constant_when_zero [OF thex0 sol thef0 gre] have "?v t $ i = x"
    by auto
  thus ?thesis by auto
 qed

lemma bound_effect:
fixes I
assumes good_interp:"is_interp I"
shows "\<And>\<nu> :: 'sv state. \<And>\<omega> ::'sv state. (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<Longrightarrow> Vagree \<nu> \<omega> (- (BVP \<alpha>))"
proof (induct rule: hp_induct)
  case Var then show "?case" 
    using agree_nil Compl_UNIV_eq pointed_finite.BVP.simps(1) by fastforce

next
  case Assign then show "?case"
    by (simp add: Vagree_def)

next
  case DiffAssign then show "?case"
    by (simp add: Vagree_def)

next
  case Test then show "?case"
    by auto(simp add: agree_refl Compl_UNIV_eq Vagree_def)

next
  case (Choice a b \<nu> \<omega>)
    assume IH1:"\<And>\<nu>'. \<And>\<omega>'. ((\<nu>', \<omega>') \<in> prog_sem I a \<Longrightarrow> Vagree \<nu>' \<omega>' (- BVP a))"
    assume IH2:"\<And>\<nu>'. \<And>\<omega>'. ((\<nu>', \<omega>') \<in> prog_sem I b \<Longrightarrow> Vagree \<nu>' \<omega>' (- BVP b))"
    assume sem:"(\<nu>, \<omega>) \<in> prog_sem I (a \<union>\<union> b)"
    have sems:"(\<nu>, \<omega>) \<in> prog_sem I (a) \<or> (\<nu>, \<omega>) \<in> prog_sem I (b)" using sem by auto
    have agrees:"Vagree \<nu> \<omega> (- BVP a) \<or> Vagree \<nu> \<omega> (- BVP b)" using IH1 IH2 sems by blast
    have sub1:"-(BVP a) \<supseteq> (- BVP a \<inter> - BVP b)" by auto
    have sub2:"-(BVP a) \<supseteq> (- BVP a \<inter> - BVP b)" by auto
    have res:"Vagree \<nu> \<omega> (- BVP a \<inter> - BVP b)" using agrees sub1 sub2 agree_supset by blast
    then show "?case" by auto

next
  case (Compose a b \<nu> \<omega>) then show "?case" 
    using agree_trans by fastforce

next
fix ODE P \<nu> \<omega>
show "(\<nu>, \<omega>) \<in> prog_sem I (EvolveODE ODE P) \<Longrightarrow> Vagree \<nu> \<omega> (- BVP (EvolveODE ODE P))"
  proof -
  fix \<nu> \<omega>
  assume sem:"(\<nu>, \<omega>) \<in> prog_sem I (EvolveODE ODE P)"
  from sem have agree:"Vagree \<nu> \<omega> (- ODE_vars ODE)" 
    by (auto simp only: prog_sem.simps Let_def)
    (* fstI mem_Collect_eq snd_conv*)
  thus "Vagree \<nu> \<omega> (- BVP (EvolveODE ODE P))" by auto
  qed
(* Var Assign DiffAssign Test Evolve Choice Compose Star *)
next
  case (Star a \<nu> \<omega>) then
    show "?case" 
      apply (simp only: prog_sem.simps)
      apply (erule converse_rtrancl_induct)
      by (auto simp add: Vagree_def)
qed


lemma coincidence_sterm:"Vagree \<nu> \<nu>' (FVT \<theta>) \<Longrightarrow> sterm_sem I  \<theta> (fst \<nu>) = sterm_sem I \<theta> (fst \<nu>')"
  apply(induct "\<theta>")
  apply(auto simp add: Vagree_def)
  by (meson rangeI)

lemma sum_unique_nonzero:
  fixes i::"'sv::finite" and f::"'sv \<Rightarrow> real"
  assumes restZero:"\<And>j. j\<in>(UNIV::'sv set) \<Longrightarrow> j \<noteq> i \<Longrightarrow> f j = 0"
  shows "(\<Sum>j\<in>(UNIV::'sv set). f j) = f i"
proof -
  have "(\<Sum>j\<in>(UNIV::'sv set). f j) = (\<Sum>j\<in>{i}. f j)"
    using restZero by (intro setsum.mono_neutral_cong_right) auto
  then show ?thesis
    by simp
qed

lemma  coincidence_frechet :
  fixes I :: "('si, 'sv) interp" and \<nu> :: "'sv state" and \<nu>'::"'sv state"
  shows "dfree \<theta> \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff \<theta>) \<Longrightarrow> frechet I  \<theta> (fst \<nu>) (snd \<nu>) = frechet I  \<theta> (fst \<nu>') (snd \<nu>')"
 proof (induction rule: dfree.induct)
  case dfree_Var then show ?case
    by (auto simp: inner_prod_eq Vagree_def simp del: basis_vector.simps)
next
  case dfree_Const then show ?case
    by auto
next
  case (dfree_Fun args var)
  assume free:"(\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> dfree \<theta>)"
  assume IH:"(\<And>arg. arg \<in> range args \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff arg) \<Longrightarrow> frechet I arg (fst \<nu>) (snd \<nu>) = frechet I arg (fst \<nu>') (snd \<nu>'))"
  have frees:"(\<And>i. dfree (args i))" using free by (auto simp add: rangeI)
  assume agree:"Vagree \<nu> \<nu>' (FVDiff ($f var args))"
  have agrees:"\<And>i. Vagree \<nu> \<nu>' (FVDiff (args i))" using agree agree_func by metis
  have sterms:"\<And>i. sterm_sem I (args i) (fst \<nu>) = sterm_sem I (args i) (fst \<nu>')" using frees agrees coincidence_sterm by (smt FVDiff_sub Vagree_def mem_Collect_eq subset_eq)
  have frechets:"\<And>i. frechet I (args i) (fst \<nu>) (snd \<nu>) = frechet I (args i) (fst \<nu>') (snd \<nu>')"  using IH agrees frees rangeI by blast
  show  "?case"
  using agrees sterms frechets by (auto)

(* smt chokes on the full IH, so simplify things a bit first *)
next
  case (dfree_Plus t1 t2) 
  assume dfree1:"dfree t1"
  assume IH1:"(Vagree \<nu> \<nu>' (FVDiff t1) \<Longrightarrow> frechet I t1 (fst \<nu>) (snd \<nu>) = frechet I t1 (fst \<nu>') (snd \<nu>'))"
  assume dfree2:"dfree t2"
  assume IH2:"(Vagree \<nu> \<nu>' (FVDiff t2) \<Longrightarrow> frechet I t2 (fst \<nu>) (snd \<nu>) = frechet I t2 (fst \<nu>') (snd \<nu>'))"
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Plus t1 t2))"
  have agree1:"Vagree \<nu> \<nu>' (FVDiff t1)" using agree agree_plus1 by (blast)
  have agree2:"Vagree \<nu> \<nu>' (FVDiff t2)" using agree agree_plus2 by (blast)
  have IH1':"(frechet I t1 (fst \<nu>) (snd \<nu>) = frechet I t1 (fst \<nu>') (snd \<nu>'))"
  using IH1 agree1 by (auto)
  have IH2':"(frechet I t2 (fst \<nu>) (snd \<nu>) = frechet I t2 (fst \<nu>') (snd \<nu>'))"
  using IH2 agree2 by (auto)
  show "?case"
  by (smt FVT.simps(4) IH1' IH2' UnCI Vagree_def coincidence_sterm frechet.simps(3) mem_Collect_eq)

(* smt chokes on the full IH, so simplify things a bit first *)
next
  case (dfree_Times t1 t2) 
  assume dfree1:"dfree t1"
  assume IH1:"(Vagree \<nu> \<nu>' (FVDiff t1) \<Longrightarrow> frechet I t1 (fst \<nu>) (snd \<nu>) = frechet I t1 (fst \<nu>') (snd \<nu>'))"
  assume dfree2:"dfree t2"
  assume IH2:"(Vagree \<nu> \<nu>' (FVDiff t2) \<Longrightarrow> frechet I t2 (fst \<nu>) (snd \<nu>) = frechet I t2 (fst \<nu>') (snd \<nu>'))"
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Times t1 t2))"
  have agree1:"Vagree \<nu> \<nu>' (FVDiff t1)" using agree agree_times1 by blast
  have agree2:"Vagree \<nu> \<nu>' (FVDiff t2)" using agree agree_times2 by blast
  have IH1':"(frechet I t1 (fst \<nu>) (snd \<nu>) = frechet I t1 (fst \<nu>') (snd \<nu>'))"
  using IH1 agree1 by (auto)
  have IH2':"(frechet I t2 (fst \<nu>) (snd \<nu>) = frechet I t2 (fst \<nu>') (snd \<nu>'))"
  using IH2 agree2 by (auto)
  have almost:"Vagree \<nu> \<nu>' (FVT (Times t1 t2)) \<Longrightarrow> frechet I (Times t1 t2) (fst \<nu>) (snd \<nu>) = frechet I (Times t1 t2) (fst \<nu>') (snd \<nu>')"
  by (smt FVT.simps(5) IH1' IH2' UnCI Vagree_def coincidence_sterm frechet.simps(4)  mem_Collect_eq agree )
  show "?case"
  using agree FVDiff_sub almost pointed_finite.agree_supset
  by (metis)
qed

lemma coincidence_dterm:
  fixes I :: "('si::finite, 'sv::finite) interp" and \<nu> :: "'sv state" and \<nu>'::"'sv state"
  shows "dsafe \<theta> \<Longrightarrow> Vagree \<nu> \<nu>' (FVT \<theta>) \<Longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I \<theta> \<nu>'"
proof (induction rule: dsafe.induct)
  case dsafe_Var then show "?case" using Vagree_def rangeI 
    by (smt insert_iff mem_Collect_eq pointed_finite.FVT.simps(1) pointed_finite.dterm_sem.simps(1))

next
  case dsafe_Const then show "?case"
    by (auto)

next
  case (dsafe_Fun args f)
    assume safe:"(\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> dsafe \<theta>)"
    assume IH:"\<And>arg. arg \<in> range args \<Longrightarrow> Vagree \<nu> \<nu>' (FVT arg) \<Longrightarrow> dterm_sem I arg \<nu> = dterm_sem I arg \<nu>'"
    assume agree:"Vagree \<nu> \<nu>' (FVT ($f f args))"
    then have "\<And>i. Vagree \<nu> \<nu>' (FVT (args i))"
      using agree_func_fvt by (metis)
    then show "?case"
      using safe coincidence_sterm IH rangeI by (auto)

next
  case dsafe_Plus then show "?case"
    by (metis FVT.simps(4) UnCI agree_supset dterm_sem.simps(4) subset_eq  union_supset1)

next
  case dsafe_Times then show "?case"
    by (metis FVT.simps(5) UnCI agree_supset dterm_sem.simps(5) subset_eq  union_supset1)

next 
  case dsafe_Diff then show "?case"
    by (auto simp: directional_derivative_def coincidence_frechet)

next
  case dsafe_DiffVar then show "?case"
    by (smt Vagree_def rangeI insert_iff mem_Collect_eq pointed_finite.FVT.simps(7) pointed_finite.dterm_sem.simps(2))

qed

subsection \<open>Axioms\<close>
text \<open>
  The uniform substitution calculus is based on a finite list of concrete
  axioms, which are defined and proved sound in this section. When axioms apply
  to arbitrary programs or formulas, they mention concrete program or formula
  variables, which are then instantiated by uniform substitution, as opposed
  metavariables.
  \<close>

definition valid :: "('si, 'sv) formula \<Rightarrow> bool"
where "valid \<phi> \<equiv> (\<forall> I. \<forall> \<nu>. is_interp I \<longrightarrow> \<nu> \<in> fml_sem I \<phi>)"

(* Arguments for a "nullary" function - a tuple of all-zeros. When we encode
  a function that has less than the maximum allowed number of arguments, we
  do so by making the remaining arguments 0 at every use site. We can't actually
  enforce that the interpretation of the function "doesnt care" about an argument,
  but if we never use that argument at more than one value there's no way to "notice"
  that the extra arguments exist *)
definition empty :: "('si, 'sv) dtuple"
  where "empty \<equiv> \<lambda>i.(Const 0)"

(* Function argument tuple where the first argument is arbitrary and the rest are zero.*)
fun singleton :: "('si, 'sv) trm \<Rightarrow> ('si, 'sv) dtuple"
  where "singleton t i = (if i = iid1 then t else (Const 0))"

(* Equivalents of the above for functions over simple terms. *)
definition sempty :: "('si, 'sv) stuple"
  where "sempty _ \<equiv> (Const 0)"

fun ssingleton :: "('si, 'sv) trm \<Rightarrow> ('si, 'sv) stuple"
  where "ssingleton t var = (if var = iid1 then t else (Const 0))"

definition assign_axiom :: "('si, 'sv) formula"
  where "assign_axiom \<equiv>
    ([[vid1 := ($f iid1 empty)]] (Prop iid1 (singleton (Var vid1))))
      \<leftrightarrow> Prop iid1 (singleton ($f iid1 empty))"

definition loop_iterate_axiom :: "('si, 'sv) formula"
  where "loop_iterate_axiom \<equiv> ([[$\<alpha> iid1**]]Predicational iid1)
    \<leftrightarrow> ((Predicational iid1) && ([[$\<alpha> iid1]][[$\<alpha> iid1**]]Predicational iid1))"

definition test_axiom :: "('si, 'sv) formula"
  where "test_axiom \<equiv>
    ([[?($\<phi> iid2 empty)]]$\<phi> iid1 empty) \<leftrightarrow> (($\<phi> iid2 empty) \<rightarrow> ($\<phi> iid1 empty))"

definition box_axiom :: "('si, 'sv) formula"
  where "box_axiom \<equiv> (\<langle>$\<alpha> iid1\<rangle>Predicational iid1) \<leftrightarrow> !([[$\<alpha> iid1]]!(Predicational iid1))"

definition choice_axiom :: "('si, 'sv) formula"
  where "choice_axiom \<equiv> ([[$\<alpha> iid1 \<union>\<union> $\<alpha> iid2]]Predicational iid1)
    \<leftrightarrow> (([[$\<alpha> iid1]]Predicational iid1) && ([[$\<alpha> iid2]]Predicational iid1))"

definition Kaxiom :: "('si, 'sv) formula"
  where "Kaxiom \<equiv> ([[$\<alpha> iid1]]((Predicational iid1) \<rightarrow> (Predicational iid2)))
    \<rightarrow> ([[$\<alpha> iid1]]Predicational iid1) \<rightarrow> ([[$\<alpha> iid1]]Predicational iid2)"

(*
definition Ibroken :: "('si, 'sv) formula"
  where "Ibroken \<equiv> ([[$$a]]($P [] \<rightarrow> ([[$$a]]$P []))
    \<rightarrow> ($P [] \<rightarrow> ([[($$a)**]]$P [])))"*)

definition Iaxiom :: "('si, 'sv) formula"
  where "Iaxiom \<equiv> 
  ([[($\<alpha> iid1)**]](Predicational iid1 \<rightarrow> ([[$\<alpha> iid1]]Predicational iid1)))
    \<rightarrow>((Predicational iid1 \<rightarrow> ([[($\<alpha> iid1)**]]Predicational iid1)))"

definition Vaxiom :: "('si, 'sv) formula"
  where "Vaxiom \<equiv> ($\<phi> iid1 empty) \<rightarrow> ([[$\<alpha> iid1]]($\<phi> iid1 empty))"

definition G_holds :: "('si, 'sv) formula \<Rightarrow> ('si, 'sv) hp \<Rightarrow> bool"
  where "G_holds \<phi> \<alpha> \<equiv> valid \<phi> \<longrightarrow> valid ([[\<alpha>]]\<phi>)"

definition Skolem_holds :: "('si, 'sv) formula \<Rightarrow> 'sv \<Rightarrow> bool"
  where "Skolem_holds \<phi> var \<equiv> valid \<phi> \<longrightarrow> valid (Forall var \<phi>)"

definition MP_holds :: "('si, 'sv) formula \<Rightarrow> ('si, 'sv) formula \<Rightarrow> bool"
  where "MP_holds \<phi> \<psi> \<equiv> valid (\<phi> \<rightarrow> \<psi>) \<longrightarrow> valid \<phi> \<longrightarrow> valid \<psi>"

definition CT_holds :: "'si \<Rightarrow> ('si, 'sv) trm \<Rightarrow> ('si, 'sv) trm \<Rightarrow> bool"
  where "CT_holds g \<theta> \<theta>' \<equiv> valid (Equals \<theta> \<theta>')
    \<longrightarrow> valid (Equals (Function g (singleton \<theta>)) (Function g (singleton \<theta>')))"

definition CQ_holds :: "'si \<Rightarrow> ('si, 'sv) trm \<Rightarrow> ('si, 'sv) trm \<Rightarrow> bool"
  where "CQ_holds p \<theta> \<theta>' \<equiv> valid (Equals \<theta> \<theta>')
    \<longrightarrow> valid ((Prop p (singleton \<theta>)) \<leftrightarrow> (Prop p (singleton \<theta>')))"

definition CE_holds :: "'si \<Rightarrow> ('si, 'sv) formula \<Rightarrow> ('si, 'sv) formula \<Rightarrow> bool"
  where "CE_holds var \<phi> \<psi> \<equiv> valid (\<phi> \<leftrightarrow> \<psi>)
    \<longrightarrow> valid (InContext var \<phi> \<leftrightarrow> InContext var \<psi>)"

definition diff_const_axiom :: "('si, 'sv) formula"
  where "diff_const_axiom \<equiv> Equals (Differential ($f iid1 sempty)) (Const 0)"

theorem test_valid: "valid test_axiom"
  by (auto simp add: valid_def test_axiom_def)

lemma or_sem [simp]:
  "fml_sem I (Or \<phi> \<psi>) = fml_sem I \<phi> \<union> fml_sem I \<psi>"
  by (auto)

lemma iff_sem [simp]: "(\<nu> \<in> fml_sem I (A \<leftrightarrow> B))
  \<longleftrightarrow> ((\<nu> \<in> fml_sem I A) \<longleftrightarrow> (\<nu> \<in> fml_sem I B))"
  by (auto)

lemma box_sem:"fml_sem I (Box \<alpha> \<phi>) = {\<nu>. \<forall> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<longrightarrow> \<omega> \<in> fml_sem I \<phi>}"
  by (auto)

lemma loop_sem:"prog_sem I (Loop \<alpha>) = (prog_sem I \<alpha>)\<^sup>*"
  by (auto)

lemma impl_sem [simp]: "(\<nu> \<in> fml_sem I (A \<rightarrow> B))
  = ((\<nu> \<in> fml_sem I A) \<longrightarrow> (\<nu> \<in> fml_sem I B))"
  by (auto)

lemma equals_sem [simp]: "(\<nu> \<in> fml_sem I (Equals \<theta> \<theta>'))
  = (dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu>)"
  by (auto)

lemma diamond_sem [simp]: "fml_sem I (Diamond \<alpha> \<phi>)
  = {\<nu>. \<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<and> \<omega> \<in> fml_sem I \<phi>}"
  by (auto)

lemma iff_to_impl: "((\<nu> \<in> fml_sem I A) \<longleftrightarrow> (\<nu> \<in> fml_sem I B))
  \<longleftrightarrow> (((\<nu> \<in> fml_sem I A) \<longrightarrow> (\<nu> \<in> fml_sem I B))
     \<and> ((\<nu> \<in> fml_sem I B) \<longrightarrow> (\<nu> \<in> fml_sem I A)))"
by (auto)

lemma vec_extensionality:"(\<And>i. v$i = w$i) \<Longrightarrow> (v = w)"
  by (simp add: vec_eq_iff)

lemma proj_sing1:"(singleton \<theta> iid1) = \<theta>"
  by (auto simp add: singleton_def)

lemma proj_sing2:"iid1 \<noteq> y  \<Longrightarrow> (singleton \<theta> y) = (Const 0)"
  by (auto simp add: singleton_def)

lemma assign_lem1:
"dterm_sem I (if i = iid1 then Var vid1 else (Const 0))
                   (vec_lambda (\<lambda>y. if vid1 = y then Functions I iid1
  (vec_lambda (\<lambda>i. dterm_sem I (empty i) \<nu>)) else  vec_nth (fst \<nu>) y), snd \<nu>)
=
 dterm_sem I (if i = iid1 then $f iid1 empty else (Const 0)) \<nu>
"
 by (case_tac "i = iid1") (auto simp add: proj_sing1)

lemma assign_lem:
"dterm_sem I (singleton (Var vid1) i)
   (vec_lambda (\<lambda>y. if y = vid1  then Functions I iid1 (vec_lambda (\<lambda>i. dterm_sem I (empty i) \<nu>)) else vec_nth (fst \<nu>) y), snd \<nu>)
                   =
 dterm_sem I (singleton ($f iid1 empty) i) \<nu>"
 by (case_tac "i = iid1 ") (auto simp add: proj_sing1)

theorem assign_valid: "valid assign_axiom"
  apply(simp only: valid_def assign_axiom_def)
  apply(rule allI | rule impI)+
  apply(simp only: iff_sem fml_sem.simps mem_Collect_eq prog_sem.simps)
  apply(simp)
  apply(simp only: assign_lem1)
  done

lemma mem_to_nonempty: "\<omega> \<in> S \<Longrightarrow> (S \<noteq> {})"
  by (auto)

lemma loop_forward: "\<nu> \<in> fml_sem I ([[$\<alpha> id1**]]Predicational id1)
  \<longrightarrow> \<nu> \<in> fml_sem I (Predicational id1&&[[$\<alpha> id1]][[$\<alpha> id1**]]Predicational id1)"
  by (cases \<nu>) (auto intro: converse_rtrancl_into_rtrancl)

lemma nat_case: "\<forall>n::nat. (n = 0) \<or> (\<exists>m. n = Suc m)"
  by (rule Nat.nat.nchotomy)

lemma loop_backward:
 "\<nu> \<in> fml_sem I (Predicational id1 && [[$\<alpha> id1]][[$\<alpha> id1**]]Predicational id1)
  \<longrightarrow> \<nu> \<in> fml_sem I ([[$\<alpha> id1**]]Predicational id1)"
  by (auto elim: converse_rtranclE)

theorem loop_valid: "valid loop_iterate_axiom"
  apply(simp only: valid_def loop_iterate_axiom_def)
  apply(simp only: iff_sem)
  apply(simp only: HOL.iff_conv_conj_imp)
  apply(rule allI | rule impI)+
  apply(rule conjI)
  apply(rule loop_forward)
  apply(rule loop_backward)
done

theorem box_valid: "valid box_axiom"
  apply(simp only: valid_def box_axiom_def)
  apply(rule allI)+
  apply(simp only: iff_sem)
  apply(simp)
done

theorem choice_valid: "valid choice_axiom"
  by (auto simp add: valid_def choice_axiom_def)

theorem K_valid: "valid Kaxiom"
  apply(simp only: valid_def Kaxiom_def)
  apply(rule allI)+
  apply(simp only: impl_sem)
  apply(rule impI)+
  apply(simp only: fml_sem.simps prog_sem.simps
        impl_sem mem_Collect_eq)
  apply(rule allI)
  apply(auto)
done

lemma I_axiom_lemma:
fixes I::"('si,'sv) interp" and \<nu>
assumes "is_interp I"
assumes IS:"\<nu> \<in> fml_sem I ([[$\<alpha> id1**]](Predicational id1 \<rightarrow>
                          [[$\<alpha> id1]]Predicational id1))"
assumes BC:"\<nu> \<in> fml_sem I (Predicational id1)"
shows "\<nu> \<in> fml_sem I ([[$\<alpha> id1**]](Predicational id1))"
proof -
  have IS':"\<And>\<nu>2. (\<nu>, \<nu>2) \<in> (prog_sem I ($\<alpha> id1))\<^sup>* \<Longrightarrow> \<nu>2 \<in> fml_sem I (Predicational id1 \<rightarrow> [[$\<alpha> id1]](Predicational id1))"
    using IS by auto
  have res:"\<And>\<nu>3. ((\<nu>, \<nu>3) \<in> (prog_sem I ($\<alpha> id1))\<^sup>*) \<Longrightarrow> \<nu>3 \<in> fml_sem I (Predicational id1)"
  proof -
    fix \<nu>3 
    show "((\<nu>, \<nu>3) \<in> (prog_sem I ($\<alpha> id1))\<^sup>*) \<Longrightarrow> \<nu>3 \<in> fml_sem I (Predicational id1)"
    apply(induction rule:rtrancl_induct)
    apply(rule BC)
    proof -
      fix y z
      assume vy:"(\<nu>, y) \<in> (prog_sem I ($\<alpha> id1))\<^sup>*"
      assume yz:"(y, z) \<in> prog_sem I ($\<alpha> id1)"
      assume yPP:"y \<in> fml_sem I (Predicational id1)"
      have imp3:"y \<in> fml_sem I (Predicational id1 \<rightarrow> [[$\<alpha> id1 ]](Predicational id1))"
        using IS' vy by (simp)
      have imp4:"y \<in> fml_sem I (Predicational id1) \<Longrightarrow> y \<in> fml_sem I  ([[$\<alpha> id1]](Predicational id1))"
        using imp3 impl_sem by (auto)
      have yaPP:"y \<in> fml_sem I ([[$\<alpha> id1]]Predicational id1)" using imp4 yPP by auto
      have zPP:"z \<in> fml_sem I (Predicational id1)" using yaPP box_sem yz mem_Collect_eq by blast  
      show "
        (\<nu>, y) \<in> (prog_sem I ($\<alpha> id1))\<^sup>* \<Longrightarrow>
        (y, z) \<in> prog_sem I ($\<alpha> id1) \<Longrightarrow>
        y \<in> fml_sem I (Predicational id1) \<Longrightarrow>
        z \<in> fml_sem I (Predicational id1)" using zPP by simp
    qed
  qed
  show "\<nu> \<in> fml_sem I ([[$\<alpha> id1**]]Predicational id1)"
    using res by (simp add: mem_Collect_eq box_sem loop_sem) 
qed

theorem I_valid: "valid Iaxiom" 
  apply(unfold Iaxiom_def valid_def)
  apply(rule impI | rule allI)+
  apply(simp only: impl_sem)
  using I_axiom_lemma by blast

theorem V_valid: "valid Vaxiom"
  apply(simp only: valid_def Vaxiom_def impl_sem)
  apply(rule allI | rule impI)+
  apply(auto simp add: empty_def)
done

theorem G_sound: "G_holds \<phi> \<alpha>"
  by (simp add: G_holds_def valid_def)

theorem Skolem_sound: "Skolem_holds \<phi> var"
  by (simp add: Skolem_holds_def valid_def)

theorem MP_sound: "MP_holds \<phi> \<psi>"
  by (auto simp add: MP_holds_def valid_def)

lemma CT_lemma:"\<And>I a b. \<forall>I::('si,'sv)interp. is_interp I \<longrightarrow> (\<forall>a b. dterm_sem I \<theta> (a, b) = dterm_sem I \<theta>' (a, b)) \<Longrightarrow>
             is_interp I \<Longrightarrow>
             Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = iid1 then \<theta> else  (Const 0)) (a, b))) =
             Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = iid1 then \<theta>' else (Const 0)) (a, b)))"
proof -
  fix I :: "('si::finite, 'sv::finite) interp" and a :: "(real, 'sv) vec" and b :: "(real, 'sv) vec"
  assume a1: "is_interp I"
  assume "\<forall>I. is_interp I \<longrightarrow> (\<forall>a b. dterm_sem I \<theta> (a, b) = dterm_sem I \<theta>' (a, b))"
  then have "\<forall>f. dterm_sem I (if f = iid1 then \<theta>' else (Const 0)) (a, b) = dterm_sem I (if f = iid1 then \<theta> else (Const 0)) (a, b)"
    using a1 by presburger
  then show "Functions I var (vec_lambda (\<lambda>f. dterm_sem I (if f = iid1 then \<theta> else (Const 0)) (a, b)))
 = Functions I var (vec_lambda (\<lambda>f. dterm_sem I (if f = iid1 then \<theta>' else (Const 0)) (a, b)))"
    by presburger
qed

theorem CT_sound: "CT_holds var \<theta> \<theta>'"
  apply(simp only: CT_holds_def valid_def equals_sem vec_extensionality vec_eq_iff)
  apply(simp)
  apply(rule allI | rule impI)+
  apply(simp add: CT_lemma)
done

lemma CQ_lemma:"\<And>I \<nu>. \<forall>I::('si,'sv)interp. \<forall>\<nu>. is_interp I \<longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu> \<Longrightarrow>
           is_interp I \<Longrightarrow>
           Predicates I (var::'si) (vec_lambda(\<lambda>i. dterm_sem I (if i = iid1 then \<theta> else  (Const 0)) \<nu>)) =
           Predicates I var (vec_lambda(\<lambda>i. dterm_sem I (if i = iid1 then \<theta>' else (Const 0)) \<nu>))"
proof -
  fix I :: "('si,'sv) interp" and \<nu> :: "(real, 'sv) vec \<times> (real, 'sv) vec"
  assume a1: "\<forall>I \<nu>. is_interp I \<longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu>"
  assume a2: "is_interp I"
  obtain ff :: "('sv \<Rightarrow> real) \<Rightarrow> ('sv \<Rightarrow> real) \<Rightarrow> 'sv" where
    f3: "\<forall>f fa. f (ff fa f) \<noteq> fa (ff fa f) \<or> vec_lambda f = vec_lambda fa"
    by (meson Cart_lambda_cong)
  have "dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu> "
    using a2 a1 by blast
  then have "dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else  (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>) = vid1 then \<theta> else (Const 0)) \<nu> \<noteq> dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else  (Const 0)) \<nu>) = vid1 then \<theta>' else (Const 0)) \<nu> \<longrightarrow> dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>) = vid1 then \<theta> else (Const 0)) \<nu> = dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>) = vid1 then \<theta>' else (Const 0)) \<nu>"
    by simp
  then have "(vec_lambda(\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>)) = (vec_lambda(\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else  (Const 0)) \<nu>))"
    using f3 by meson
  then show "Predicates I var (vec_lambda(\<lambda>f. dterm_sem I (if f = iid1 then \<theta> else (Const 0)) \<nu>)) = Predicates I var (vec_lambda(\<lambda>f. dterm_sem I (if f = iid1 then \<theta>' else  (Const 0)) \<nu>))"
  (* TODO: Simplify. This subproof used to be a one-line "by presburger" *)
  proof -
    obtain ss :: "('si \<Rightarrow> real) \<Rightarrow> ('si \<Rightarrow> real) \<Rightarrow> 'si" where
      f1: "\<forall>f fa. f (ss fa f) \<noteq> fa (ss fa f) \<or> vec_lambda f = vec_lambda fa"
      by (meson Cart_lambda_cong)
    have "dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = iid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = iid1 then \<theta> else Const 0) \<nu>) = iid1 then \<theta> else Const 0) \<nu> \<noteq> dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = iid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = iid1 then \<theta> else Const 0) \<nu>) = iid1 then \<theta>' else Const 0) \<nu> \<longrightarrow> dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = iid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = iid1 then \<theta> else Const 0) \<nu>) = iid1 then \<theta> else Const 0) \<nu> = dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = iid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = iid1 then \<theta> else Const 0) \<nu>) = iid1 then \<theta>' else Const 0) \<nu>"
      using \<open>dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu>\<close> by presburger
    then have "(\<chi> s. dterm_sem I (if s = iid1 then \<theta> else Const 0) \<nu>) = (\<chi> s. dterm_sem I (if s = iid1 then \<theta>' else Const 0) \<nu>)"
      using f1 by meson
    then show ?thesis
      by simp
  qed
qed

theorem CQ_sound: "CQ_holds var \<theta> \<theta>'"
  apply(simp only: CQ_holds_def valid_def equals_sem vec_extensionality vec_eq_iff)
  apply(rule allI | rule impI)+
  apply(simp only: iff_sem singleton.simps fml_sem.simps mem_Collect_eq)
  apply(simp only: CQ_lemma)
done

theorem CE_sound: "CE_holds var \<phi> \<psi>"
  apply(simp only: CE_holds_def valid_def iff_sem)
  apply(rule allI | rule impI)+
  apply(simp)
  apply(metis subsetI subset_antisym surj_pair)
done

lemma constant_deriv_inner:
 assumes interp:"\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x)"
 shows "FunctionFrechet I id1 (vec_lambda (\<lambda>i. sterm_sem I (sempty i) (fst \<nu>))) (vec_lambda(\<lambda>i. frechet I (sempty i) (fst \<nu>) (snd \<nu>)))= 0"
  proof -
    have empty_zero:"(vec_lambda(\<lambda>i. frechet I (sempty i) (fst \<nu>) (snd \<nu>))) = 0"
    using sempty_def Cart_lambda_cong frechet.simps(5) zero_vec_def
    by fastforce
    let ?x = "(vec_lambda (\<lambda>i. sterm_sem I (sempty i) (fst \<nu>)))"
    from interp
    have has_deriv:"(Functions I id1 has_derivative FunctionFrechet I id1 ?x) (at ?x)"
    by auto
    then have f_linear:"linear (FunctionFrechet I id1 ?x)"
    using Deriv.has_derivative_linear by auto
    then
    show ?thesis using empty_zero f_linear Linear_Algebra.linear_0 by (auto)
  qed

lemma constant_deriv_zero:"is_interp I \<Longrightarrow> directional_derivative I ($f id1 sempty) \<nu> = 0"
  apply(simp only: is_interp_def directional_derivative_def frechet.simps frechet_correctness)
  apply(rule constant_deriv_inner)
  apply(auto)
done

theorem diff_const_axiom_valid: "valid diff_const_axiom"
  apply(simp only: valid_def diff_const_axiom_def equals_sem)
  apply(rule allI | rule impI)+
  apply(simp only: dterm_sem.simps constant_deriv_zero sterm_sem.simps)
done

section Substitution

primrec Tsubst::"('si, 'sv) trm \<Rightarrow> ('si, 'sv) subst \<Rightarrow> ('si, 'sv) trm"
where
  "Tsubst (Var x) \<sigma> = Var x"
| "Tsubst (DiffVar x) \<sigma> = DiffVar x"  
| "Tsubst (Const r) \<sigma> = Const r"  
| "Tsubst (Function f args) \<sigma> = (case SFunctions \<sigma> f of Some f' \<Rightarrow> f' | None \<Rightarrow> Function f) (\<lambda> i. Tsubst (args i) \<sigma>)"  
| "Tsubst (Plus \<theta>1 \<theta>2) \<sigma> = Plus (Tsubst \<theta>1 \<sigma>) (Tsubst \<theta>2 \<sigma>)"  
| "Tsubst (Times \<theta>1 \<theta>2) \<sigma> = Times (Tsubst \<theta>1 \<sigma>) (Tsubst \<theta>2 \<sigma>)"  
| "Tsubst (Differential \<theta>) \<sigma> = Differential (Tsubst \<theta> \<sigma>)"

primrec Osubst::"('si, 'sv) ODE \<Rightarrow> ('si, 'sv) subst \<Rightarrow> ('si, 'sv) ODE"
where
  "Osubst (OVar c) \<sigma> = (case SODEs \<sigma> c of Some c' \<Rightarrow> c' | None \<Rightarrow> OVar c)"
| "Osubst (OSing x \<theta>) \<sigma> = OSing x (Tsubst \<theta> \<sigma>)"
| "Osubst (OProd ODE1 ODE2) \<sigma> = OProd (Osubst ODE1 \<sigma>) (Osubst ODE2 \<sigma>)"
    
fun Psubst::"('si, 'sv) hp \<Rightarrow> ('si, 'sv) subst \<Rightarrow> ('si, 'sv) hp"
and Fsubst::"('si, 'sv) formula \<Rightarrow> ('si, 'sv) subst \<Rightarrow> ('si, 'sv) formula"
where
  "Psubst (Pvar a) \<sigma> = (case SPrograms \<sigma> a of Some a' \<Rightarrow> a' | None \<Rightarrow> Pvar a)"
| "Psubst (Assign x \<theta>) \<sigma> = Assign x (Tsubst \<theta> \<sigma>)"
| "Psubst (DiffAssign x \<theta>) \<sigma> = DiffAssign x (Tsubst \<theta> \<sigma>)"
| "Psubst (Test \<phi>) \<sigma> = Test (Fsubst \<phi> \<sigma>)"
| "Psubst (EvolveODE ODE \<phi>) \<sigma> = EvolveODE (Osubst ODE \<sigma>) (Fsubst \<phi> \<sigma>)"
| "Psubst (Choice \<alpha> \<beta>) \<sigma> = Choice (Psubst \<alpha> \<sigma>) (Psubst \<beta> \<sigma>)"
| "Psubst (Sequence \<alpha> \<beta>) \<sigma> = Sequence (Psubst \<alpha> \<sigma>) (Psubst \<beta> \<sigma>)"
| "Psubst (Loop \<alpha>) \<sigma> = Loop (Psubst \<alpha> \<sigma>)"

| "Fsubst (Geq \<theta>1 \<theta>2) \<sigma> = Geq (Tsubst \<theta>1 \<sigma>) (Tsubst \<theta>2 \<sigma>)"
| "Fsubst (Prop p args) \<sigma> = (case SPredicates \<sigma> p of Some p' \<Rightarrow> p' | None \<Rightarrow> Prop p) (\<lambda>i. Tsubst (args i) \<sigma>)"
| "Fsubst (Not \<phi>) \<sigma> = Not (Fsubst \<phi> \<sigma>)"
| "Fsubst (And \<phi> \<psi>) \<sigma> = And (Fsubst \<phi> \<sigma>) (Fsubst \<psi> \<sigma>)"
| "Fsubst (Forall x \<phi>) \<sigma> = Forall x (Fsubst \<phi> \<sigma>)"
| "Fsubst (Box \<alpha> \<phi>) \<sigma> = Box (Psubst \<alpha> \<sigma>) (Fsubst \<phi> \<sigma>)"
| "Fsubst (DiffFormula \<phi>) \<sigma> = DiffFormula (Fsubst \<phi> \<sigma>)"
| "Fsubst (InContext C \<phi>) \<sigma> = (case SContexts \<sigma> C of Some C' \<Rightarrow> C' | None \<Rightarrow>  InContext C) (Fsubst \<phi> \<sigma>)"
| "Fsubst (ConstP S) \<sigma> = ConstP S"

definition FVA :: "('a \<Rightarrow> ('a, 'b) trm) \<Rightarrow> ('b + 'b) set"
where "FVA args = (\<Union> \<theta> \<in> range args. FVT \<theta>)"
  
definition FVS :: "('a,'b) subst \<Rightarrow> ('b + 'b) set"
where "FVS \<sigma> = (\<Union>i::'a. SFV \<sigma> i)"
  
definition Svalid :: "('a,'b) subst \<Rightarrow> bool"
where "Svalid \<sigma> \<longleftrightarrow>
  (\<forall> i args f. SFunctions \<sigma> i = Some f \<longrightarrow> FVT (f args)  \<subseteq> SFV \<sigma> i \<union> FVA args) \<and>
  (\<forall> i args p. SPredicates \<sigma> i = Some p \<longrightarrow> FVF (p args) \<subseteq> SFV \<sigma> i \<union> FVA args) \<and>
  (\<forall> i \<phi> C.    SContexts \<sigma> i = Some C \<longrightarrow> FVF (C \<phi>)      \<subseteq> SFV \<sigma> i \<union> FVF \<phi>)"

definition SDom :: "('a, 'b) subst \<Rightarrow> 'a set"
where "SDom \<sigma> = dom (SFunctions \<sigma>) \<union> dom (SPredicates \<sigma>) \<union> dom (SContexts \<sigma>) \<union> dom (SPrograms \<sigma>)"
  
definition TUadmit :: "('a, 'b) subst \<Rightarrow> ('a, 'b) trm \<Rightarrow> ('b + 'b) set \<Rightarrow> bool"
where "TUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> (SDom \<sigma> \<inter> SIGT \<theta>).  SFV \<sigma> i) \<inter> U) = {}"

definition FUadmit :: "('a, 'b) subst \<Rightarrow> ('a, 'b) formula \<Rightarrow> ('b + 'b) set \<Rightarrow> bool"
where "FUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> (SDom \<sigma> \<inter> SIGF \<theta>).  SFV \<sigma> i) \<inter> U) = {}"

definition PUadmit :: "('a, 'b) subst \<Rightarrow> ('a, 'b) hp \<Rightarrow> ('b + 'b) set \<Rightarrow> bool"
where "PUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> (SDom \<sigma> \<inter> SIGP \<theta>).  SFV \<sigma> i) \<inter> U) = {}"

inductive Tadmit :: "('a, 'b) subst \<Rightarrow> ('a, 'b) trm \<Rightarrow> bool"
where 
  Tadmit_Diff:"Tadmit \<sigma> \<theta> \<Longrightarrow> TUadmit \<sigma> \<theta> UNIV \<Longrightarrow> Tadmit \<sigma> (Differential \<theta>)"
| Tadmit_Func:"(\<And>i. Tadmit \<sigma> (args i)) \<Longrightarrow> Tadmit \<sigma> (Function f args)"
| Tadmit_Plus:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Tadmit \<sigma> (Plus \<theta>1 \<theta>2)"
| Tadmit_Times:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Tadmit \<sigma> (Times \<theta>1 \<theta>2)"
| Tadmit_DiffVar:"Tadmit \<sigma> (DiffVar x)"
| Tadmit_Var:"Tadmit \<sigma> (Var x)"
| Tadmit_Const:"Tadmit \<sigma> (Const r)"

inductive OUadmit:: "('a, 'b) subst \<Rightarrow> ('a, 'b) ODE \<Rightarrow> ('b + 'b) set \<Rightarrow> bool"
where 
  "OUadmit \<sigma> (OVar c) U"
| "TUadmit \<sigma> \<theta> U \<Longrightarrow> OUadmit \<sigma> (OSing x \<theta>) U"
| "OUadmit \<sigma> ODE1 U \<Longrightarrow> OUadmit \<sigma> ODE2 U \<Longrightarrow> OUadmit \<sigma> (OProd ODE1 ODE2) U"
 
inductive Padmit:: "('a, 'b) subst \<Rightarrow> ('a, 'b) hp \<Rightarrow> bool"
and Fadmit:: "('a, 'b) subst \<Rightarrow> ('a, 'b) formula \<Rightarrow> bool"
where
  "Padmit \<sigma> (Pvar a)"
| "Padmit \<sigma> a \<Longrightarrow> Padmit \<sigma> b \<Longrightarrow> PUadmit \<sigma> b (BVP a)\<Longrightarrow> Padmit \<sigma> (Sequence a b)"  
| "Padmit \<sigma> a \<Longrightarrow> PUadmit \<sigma> a (BVP a) \<Longrightarrow> Padmit \<sigma> (Loop a)"  
| "OUadmit \<sigma> ODE (ODE_vars ODE) \<Longrightarrow> Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> (ODE_vars ODE) \<Longrightarrow> Padmit \<sigma> (EvolveODE ODE \<phi>)"
| "Padmit \<sigma> a \<Longrightarrow> Padmit \<sigma> b \<Longrightarrow> Padmit \<sigma> (Choice a b)"
| "Tadmit \<sigma> \<theta> \<Longrightarrow> Padmit \<sigma> (Assign x \<theta>)"  
| "Tadmit \<sigma> \<theta> \<Longrightarrow> Padmit \<sigma> (DiffAssign x \<theta>)"  
| "Fadmit \<sigma> \<phi> \<Longrightarrow> Padmit \<sigma> (Test \<phi>)"
| "Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Fadmit \<sigma> (Geq \<theta>1 \<theta>2)"
| "(\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> Tadmit \<sigma> \<theta>) \<Longrightarrow> Fadmit \<sigma> (Prop p args)" 
| "Fadmit \<sigma> \<phi> \<Longrightarrow> Fadmit \<sigma> (Not \<phi>)"
| "Fadmit \<sigma> \<phi> \<Longrightarrow> Fadmit \<sigma> \<psi> \<Longrightarrow> Fadmit \<sigma> (And \<phi> \<psi>)"
| "Fadmit \<sigma> \<phi> \<Longrightarrow> Fadmit \<sigma> (DiffFormula \<phi>)"
| "Fadmit \<sigma> (ConstP P)"
| "Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> {Inl x} \<Longrightarrow> Fadmit \<sigma> (Forall x \<phi>)"
| "Fadmit \<sigma> \<phi> \<Longrightarrow> Padmit \<sigma> a \<Longrightarrow> FUadmit \<sigma> \<phi> (BVP a) \<Longrightarrow> Fadmit \<sigma> (Box a \<phi>)"
| "Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> UNIV \<Longrightarrow> Fadmit \<sigma> (InContext C \<phi>)"
  
fun adjoint :: "('si, 'sv) interp \<Rightarrow> ('si, 'sv) subst \<Rightarrow> 'sv state \<Rightarrow> ('si, 'sv) interp" 
where "adjoint I \<sigma> \<nu> =
\<lparr>Functions =       (\<lambda>f. case SFunctions \<sigma> f of Some f' \<Rightarrow> (\<lambda> args. (dterm_sem I (f' (\<lambda> i. Const (args $ i))) \<nu>)) | None => Functions I f),
 Predicates =      (\<lambda>p. case SPredicates \<sigma> p of Some p' \<Rightarrow> (\<lambda> args. \<nu> \<in> (fml_sem I (p' (\<lambda> i. Const (args $ i))))) | None \<Rightarrow> Predicates I p),
 Contexts =        (\<lambda>c. case SContexts \<sigma> c of Some c' \<Rightarrow> (\<lambda> R. fml_sem I (c' (ConstP R))) | None \<Rightarrow> Contexts I c),
 Programs =        (\<lambda>a. case SPrograms \<sigma> a of Some a' \<Rightarrow> prog_sem I a' | None \<Rightarrow> Programs I a),
 ODEs =          (\<lambda>ode. case SODEs \<sigma> ode of Some ode' \<Rightarrow> ODE_sem I ode' | None \<Rightarrow> ODEs I ode)\<rparr>"
  
(* Properties of adjoints *)
lemma adjoint_consequence:" Vagree \<nu> \<omega> (FVS \<sigma>) \<Longrightarrow> adjoint I \<sigma> \<nu> = adjoint I \<sigma> \<omega>"
  sorry

lemma uadmit_sterm_adjoint:"TUadmit \<sigma> \<theta> U \<Longrightarrow> Vagree \<nu> \<omega> U \<Longrightarrow> sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
  sorry

lemma uadmit_dterm_adjoint:"TUadmit \<sigma> \<theta> U \<Longrightarrow> Vagree \<nu> \<omega> U \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
  sorry

lemma uadmit_prog_adjoint:"PUadmit \<sigma> a U \<Longrightarrow> Vagree \<nu> \<omega> U \<Longrightarrow> prog_sem (adjoint I \<sigma> \<nu>) a = prog_sem (adjoint I \<sigma> \<omega>) a"
and   uadmit_fml_sem:"FUadmit \<sigma> \<phi> U \<Longrightarrow> Vagree \<nu> \<omega> U \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
  sorry

lemma usubst_sterm:"Tadmit \<sigma> \<theta> \<Longrightarrow> Svalid \<sigma> \<Longrightarrow> dfree \<theta> \<Longrightarrow> sterm_sem I (Tsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induct rule: Tadmit.induct)
  case Tadmit_Func
    fix \<sigma> :: "('si, 'sv) subst" and args :: "'si \<Rightarrow> ('si, 'sv) trm" and f :: 'si
    assume admit:"\<And>i. Tadmit \<sigma> (args i)"
    assume IH:   "\<And>i. Svalid \<sigma> \<Longrightarrow> dfree (args i) \<Longrightarrow> sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) =
                   sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)"
    assume valid:"Svalid \<sigma>"
    assume free:"dfree (Function f args)"
    hence frees:"\<And>i. dfree (args i)" sorry
    from IH valid frees have IH':"\<And>i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) =
                   sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)" by auto
    
    show "sterm_sem I (Tsubst ($f f args) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) ($f f args) (fst \<nu>)"
    proof (cases "SFunctions \<sigma> f = None")
      show "SFunctions \<sigma> f = None \<Longrightarrow>
        sterm_sem I (Tsubst ($f f args) \<sigma>) (fst \<nu>) = sterm_sem (local.adjoint I \<sigma> \<nu>) ($f f args) (fst \<nu>)"
        by (auto simp add: Case_def IH' )
      assume notNone:"SFunctions \<sigma> f \<noteq> None"
      then obtain \<sigma>f where sf:"SFunctions \<sigma> f = Some \<sigma>f" by auto      
      hence "sterm_sem I (Tsubst ($f f args) \<sigma>) (fst \<nu>) = sterm_sem I (\<sigma>f (\<lambda> i. Tsubst (args i) \<sigma>)) (fst \<nu>)"
        by auto
      (* "\<And>i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) =
                   sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)*)
      (*dterm_sem I
          (y (\<lambda>i. Const (sterm_sem
                          I*
                          (args i) (fst \<nu>))))
          \<nu> =*)
      have "sterm_sem (adjoint I \<sigma> \<nu>) ($f f args) (fst \<nu>) =
        dterm_sem I (\<sigma>f (\<lambda>i. Const (sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)))) \<nu>"
        using notNone by (auto simp add: notNone sf)
      (* This is a lemma that should mostly be true with dfree plus possibly extremely frustrating
side conditions everywhere. *)
      hence "sterm_sem (adjoint I \<sigma> \<nu>) ($f f args) (fst \<nu>) =
        sterm_sem I (\<sigma>f (\<lambda>i. Const (sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)))) (fst \<nu>)" sorry
(* This probably needs to be an assumption, or maybe could be taken care of by better chosing the
   representation. *)
      have \<sigma>f_respects: "\<And>args1 args2. (\<And>i. sterm_sem I (args1 i) (fst \<nu>) = sterm_sem I (args2 i) (fst \<nu>))
        \<Longrightarrow> \<sigma>f args1 = \<sigma>f args2" sorry
      let ?args1 = "(\<lambda>i. Const (sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)))"
      let ?args2 = "(\<lambda>i. Tsubst (args i) \<sigma>)"
      have "\<And>i. sterm_sem I (?args1 i) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)" by auto
      hence "\<And>i. sterm_sem I (?args1 i) (fst \<nu>) = sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>)" using IH' by auto
      hence all_eq:"\<And>i. sterm_sem I (?args1 i) (fst \<nu>) = sterm_sem I (?args2 i) (fst \<nu>)" by auto
      have "\<sigma>f ?args1 = \<sigma>f ?args2" using \<sigma>f_respects[OF all_eq] by simp
      hence "sterm_sem I (\<sigma>f (\<lambda>i. Const (sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)))) (fst \<nu>) =
            sterm_sem I (\<sigma>f (\<lambda>i. Tsubst (args i) \<sigma>)) (fst \<nu>)" by simp
      
(*      hence "sterm_sem I (\<sigma>f (\<lambda>i. Tsubst (args i) \<sigma>)) (fst \<nu>) = "
      have "sterm_sem I (Tsubst ($f f args) \<sigma>) (fst \<nu>) = "
      "sterm_sem I (Tsubst ($f f args) \<sigma>) (fst \<nu>) = sterm_sem (local.adjoint I \<sigma> \<nu>) ($f f args) (fst \<nu>)"*)
    qed
      apply(auto simp del: adjoint.simps)
      apply(cases "SFunctions \<sigma> f = None")
      apply(auto simp add: Case_def IH' del: local.adjoint.simps)
      done
    
qed (auto simp add: frechet_correctness rangeI)  
end
end