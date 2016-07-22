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

lemma has_derivative_vec[derivative_intros]:
  assumes "\<And>i. ((\<lambda>x. f i x) has_derivative (\<lambda>h. f' i h)) F"
  shows "((\<lambda>x. \<chi> i. f i x) has_derivative (\<lambda>h. \<chi> i. f' i h)) F"
proof -
  have *: "(\<chi> i. f i x) = (\<Sum>i\<in>UNIV. axis i (f i x))" "(\<chi> i. f' i x) = (\<Sum>i\<in>UNIV. axis i (f' i x))" for x
    by (simp_all add: axis_def setsum.If_cases vec_eq_iff)
  show ?thesis
    unfolding *
    by (intro has_derivative_setsum bounded_linear.has_derivative[OF bounded_linear_axis] assms)
qed

  type_synonym 'a Rvec = "real^('a::finite)"
  type_synonym 'a state = "'a Rvec \<times> 'a Rvec"
  type_synonym 'a simple_state = "'a Rvec"

(* #Functions, #Predicates, #Other *)
record ('a, 'b, 'c) interp =
  Functions       :: "'a \<Rightarrow> 'c Rvec \<Rightarrow> real"
  Predicates      :: "'c \<Rightarrow> 'c Rvec \<Rightarrow> bool"
  Contexts        :: "'b \<Rightarrow> 'c state set \<Rightarrow> 'c state set"
  Programs        :: "'c \<Rightarrow> ('c state * 'c state) set"
  ODEs            :: "'c \<Rightarrow> 'c simple_state \<Rightarrow> 'c simple_state"

fun FunctionFrechet :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> 'a \<Rightarrow> 'c Rvec \<Rightarrow> 'c Rvec \<Rightarrow> real"
where "FunctionFrechet I i = (THE f'. \<forall> x. (Functions I i has_derivative f' x) (at x))"

datatype ('a, 'c) trm =
 (* Program variable *)
  Var 'c
(* N.B. This is technically more expressive than true dL since most reals
 can't be written down. *)
| Const real
| Function 'a "'c \<Rightarrow> ('a, 'c) trm" ("$f")
| Plus "('a, 'c) trm" "('a, 'c) trm"
| Times "('a, 'c) trm" "('a, 'c) trm"
| DiffVar 'c ("$'")
| Differential "('a, 'c) trm"

datatype('a, 'c) ODE =
  OVar 'c
| OSing 'c "('a, 'c) trm"
| OProd "('a, 'c) ODE" "('a, 'c) ODE"

datatype ('a, 'b, 'c) hp =
 Pvar 'c                           ("$\<alpha>")
| Assign 'c "('a, 'c) trm"                (infixr ":=" 10)
| DiffAssign 'c "('a, 'c) trm"
| Test "('a, 'b, 'c) formula"                 ("?")
(* An ODE program is an ODE system with some evolution domain. *)
| EvolveODE "('a, 'c) ODE" "('a, 'b, 'c) formula"
| Choice "('a, 'b, 'c) hp" "('a, 'b, 'c) hp"            (infixl "\<union>\<union>" 10)
| Sequence "('a, 'b, 'c) hp"  "('a, 'b, 'c) hp"         (infixr ";;" 8)
| Loop "('a, 'b, 'c) hp"                      ("_**")

and ('a, 'b, 'c) formula =
 Geq "('a, 'c) trm" "('a, 'c) trm"
| Prop 'c "'c \<Rightarrow> ('a, 'c) trm"      ("$\<phi>")
| Not "('a, 'b, 'c) formula"            ("!")
| And "('a, 'b, 'c) formula" "('a, 'b, 'c) formula"    (infixl "&&" 8)
| Forall 'c "('a, 'b, 'c) formula"
| Box "('a, 'b, 'c) hp" "('a, 'b, 'c) formula"         ("([[_]]_)" 10)
(* DiffFormula \<phi> gives us the invariant for proving \<phi> by differential induction. *)
| DiffFormula "('a, 'b, 'c) formula"
(* Unary quantifier symbols *)
| InContext 'b "('a, 'b, 'c) formula"

(* Definite predicational as a context with a constant argument (e.g. constant true *)
fun Predicational :: "'b \<Rightarrow> ('a, 'b, 'c) formula"
where "Predicational P = InContext P (Geq (Const 0) (Const 0))"
  
record ('a, 'b, 'c) subst =
  (* The RHS of a function or predicate substitution is a term or formula
   * with extra variables, which are used to refer to arguments. *)
  SFunctions       :: "'a \<rightharpoonup> ('a + 'c, 'c) trm"
  SPredicates      :: "'c \<rightharpoonup> ('a + 'c, 'b, 'c) formula"
  SContexts        :: "'b \<rightharpoonup> ('a, 'b + unit, 'c) formula"
  SPrograms        :: "'c \<rightharpoonup> ('a, 'b, 'c) hp"
  SODEs            :: "'c \<rightharpoonup> ('a, 'c) ODE"

(*Differential dynamic logic can be defined for any finite types, given a 
  few elements of those types (so that we can generate axioms). *)
locale pointed_finite =
  (* NOTE: 'sf, 'sz don't have to be finite *)
  fixes vid1 :: "('sz::finite)"
  fixes vid2 :: 'sz
  fixes vid3 :: 'sz
  fixes fid1 :: "('sf::finite)"
  fixes fid2 :: 'sf
  fixes fid3 :: 'sf
  fixes pid1 :: "('sc::finite)"
  fixes pid2 :: 'sc
  fixes pid3 :: 'sc
  assumes vne12:"vid1 \<noteq> vid2"
  assumes vne23:"vid2 \<noteq> vid3"
  assumes vne13:"vid1 \<noteq> vid3"
  assumes fne12:"fid1 \<noteq> fid2"
  assumes fne23:"fid2 \<noteq> fid3"
  assumes fne13:"fid1 \<noteq> fid3"
  assumes pne12:"pid1 \<noteq> pid2"
  assumes pne23:"pid2 \<noteq> pid3"
  assumes pne13:"pid1 \<noteq> pid3"

context pointed_finite
begin
subsection \<open>States\<close>
text \<open>We formalize a state S as a pair (S_V, S_V') : \<real>^n \<times> \<real>^n , where S_V assigns
  values to the program variables and S_V' assigns values to their
  differentials. Function constants are also formalized as having a fixed arity
  m (Rvec_dim) which may differ from n. If a function does not need to
  have m arguments, any remaining arguments can be uniformly set to 0
  throughout a proof, which simulates the affect of having functions of less
  arguments.
  \<close>

(* TODO: Out of order *)
subsection \<open>Syntax\<close>
text \<open>
  We define the syntax of dL terms, formulas and hybrid programs. As in
  CADE'15, the syntax allows arbitrarily nested differentials. However, 
  the semantics of such terms is very surprising (e.g. (x')' is zero in
  every state), so we define predicates dfree and dsafe to rule out such terms.

  In keeping with the CADE'15 presentation we currently make the simplifying
  assumption that all terms are smooth, and thus division and arbitrary
  exponentiation are absent from the syntax. Several other standard logical
  constructs are implemented as derived forms to reduce the soundness burden.
\<close>

inductive dfree :: "('a, 'c) trm \<Rightarrow> bool"
where
  dfree_Var: "dfree (Var i)"
| dfree_Const: "dfree (Const r)"
| dfree_Fun: "(\<And>i. dfree (args i)) \<Longrightarrow> dfree (Function i args)"
| dfree_Plus: "dfree \<theta>\<^sub>1 \<Longrightarrow> dfree \<theta>\<^sub>2 \<Longrightarrow> dfree (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dfree_Times: "dfree \<theta>\<^sub>1 \<Longrightarrow> dfree \<theta>\<^sub>2 \<Longrightarrow> dfree (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"

inductive_simps
      dfree_Plus_simps[simp]: "dfree (Plus a b)"
  and dfree_Times_simps[simp]: "dfree (Times a b)"
  and dfree_Var_simps[simp]: "dfree (Var x)"
  and dfree_Fun_simps[simp]: "dfree (Function i args)"
  
inductive dsafe :: "('a, 'c) trm \<Rightarrow> bool"
where
  dsafe_Var: "dsafe (Var i)"
| dsafe_Const: "dsafe (Const r)"
| dsafe_Fun: "(\<And>i. dsafe (args i)) \<Longrightarrow> dsafe (Function i args)"
| dsafe_Plus: "dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Times: "dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Diff: "dfree \<theta> \<Longrightarrow> dsafe (Differential \<theta>)"
| dsafe_DiffVar: "dsafe ($' i)"

inductive_simps
      dsafe_Plus_simps[simp]: "dsafe (Plus a b)"
  and dsafe_Times_simps[simp]: "dsafe (Times a b)"
  and dsafe_Var_simps[simp]: "dsafe (Var x)"
  and dsafe_Fun_simps[simp]: "dsafe (Function i args)"
  and dsafe_Diff_simps[simp]: "dsafe (Differential a)"

lemma dfree_is_dsafe: "dfree \<theta> \<Longrightarrow> dsafe \<theta>"
  by (induction rule: dfree.induct) (auto intro: dsafe.intros)

fun ODE_dom::"('a, 'c) ODE \<Rightarrow> 'c set"
where 
  "ODE_dom (OVar c) =  {}"
| "ODE_dom (OSing x \<theta>) = {x}"
| "ODE_dom (OProd ODE1 ODE2) = ODE_dom ODE1 \<union> ODE_dom ODE2"

inductive osafe:: "('a, 'c) ODE \<Rightarrow> bool"
where
  osafe_Var:"osafe (OVar c)"
| osafe_Sing:"dfree \<theta> \<Longrightarrow> osafe (OSing x \<theta>)"
| osafe_Prod:"osafe ODE1 \<Longrightarrow> osafe ODE2 \<Longrightarrow> ODE_dom ODE1 \<inter> ODE_dom ODE2 = {} \<Longrightarrow> osafe (OProd ODE1 ODE2)"

inductive hpfree:: "('a, 'b, 'c) hp \<Rightarrow> bool"
and ffree::        "('a, 'b, 'c) formula \<Rightarrow> bool"
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

inductive hpsafe:: "('a, 'b, 'c) hp \<Rightarrow> bool"
and fsafe:: "('a, 'b, 'c) formula \<Rightarrow> bool"
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

type_synonym ('a, 'c) stuple = "('c \<Rightarrow> ('a, 'c) trm)"
type_synonym ('a, 'c) dtuple = "('c \<Rightarrow> ('a, 'c) trm)"

(* Derived forms *)
definition Or :: "('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" (infixl "||" 7)
  where "Or P Q = Not (And (Not P) (Not Q))"

definition Implies :: "('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" (infixr "\<rightarrow>" 10)
  where "Implies P Q = Or Q (Not P)"

definition Equiv :: "('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" (infixl "\<leftrightarrow>" 10)
  where "Equiv P Q = Or (And P Q) (And (Not P) (Not Q))"

fun Exists :: "'c \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula"
  where "Exists x P = Not (Forall x (Not P))"

definition Equals :: "('a, 'c) trm \<Rightarrow> ('a, 'c) trm \<Rightarrow> ('a, 'b, 'c) formula"
  where "Equals \<theta> \<theta>' = ((Geq \<theta> \<theta>') && (Geq \<theta>' \<theta>))"

definition Diamond :: "('a, 'b, 'c) hp \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" ("(\<langle>_\<rangle>_)" 10)
  where "Diamond \<alpha> P = Not(Box \<alpha> (Not P))"

subsection \<open>Denotational Semantics\<close>

text \<open>
  The central definitions for the denotational semantics are states \nu,
  interpretations I and the interpretation functions [[\psi]]I, [[\theta]]I\nu,
  [[\alpha]]I, which are represented by the Isabelle functions fml_sem,
  term_sem and prog_sem, respectively.

  To enable reasoning about derivatives of functions, our interpretations
  include a field FunctionFrechet specifying the Frechet derivative
  (FunctionFrechet f \<nu>) : \<real>^m -> \<real> for every function in every state. The
  proposition (is_interp I) asserts that every function is  differentiable and
  its derivative agrees everywhere with the derivative given by
  FunctionFrechet.
  \<close>

definition is_interp :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> bool"
  where "is_interp I \<equiv>
    \<forall>x. \<forall>i. (FDERIV (Functions I i) x :> (FunctionFrechet I i x))"

(* sterm_sem is the term sem for differential-free terms. *)
primrec sterm_sem :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a, 'c) trm \<Rightarrow> 'c simple_state \<Rightarrow> real"
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
primrec frechet :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a, 'c) trm \<Rightarrow> 'c simple_state \<Rightarrow> 'c simple_state \<Rightarrow> real"
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

definition directional_derivative :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a, 'c) trm \<Rightarrow> 'c state \<Rightarrow> real"
where "directional_derivative I t = (\<lambda>v. frechet I t (fst v) (snd v))"

(* Sem for terms that are allowed to contain differentials.
   Note there is some duplication with sterm_sem (hence the desire to combine the two).*)
primrec dterm_sem :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a, 'c) trm \<Rightarrow> 'c state \<Rightarrow> real"
where
  "dterm_sem I (Var x) = (\<lambda>v. fst v $ x)"
| "dterm_sem I (DiffVar x) = (\<lambda>v. snd v $ x)"
| "dterm_sem I (Function f args) = (\<lambda>v. Functions I f (\<chi> i. dterm_sem I (args i) v))"
| "dterm_sem I (Plus t1 t2) = (\<lambda>v. (dterm_sem I t1 v) + (dterm_sem I t2 v))"
| "dterm_sem I (Times t1 t2) = (\<lambda>v. (dterm_sem I t1 v) * (dterm_sem I t2 v))"
| "dterm_sem I (Differential t) = (\<lambda>v. directional_derivative I t v)"
| "dterm_sem I (Const c) = (\<lambda>v. c)"

(* repv \<nu> x r replaces the value of (unprimed) variable x in the state \<nu> with r *)
fun repv :: "'c::finite state \<Rightarrow> 'c \<Rightarrow> real \<Rightarrow> 'c state"
where "repv v x r = ((\<chi> y. if x = y then r else vec_nth (fst v) y), snd v)"

(* repd \<nu> x' r replaces the value of (primed) variable x' in the state \<nu> with r *)
fun repd :: "'c::finite state \<Rightarrow> 'c \<Rightarrow> real \<Rightarrow> 'c state"
where "repd v x r = (fst v, (\<chi> y. if x = y then r else vec_nth (snd v) y))"  

fun ODE_sem:: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a, 'c) ODE \<Rightarrow> 'c Rvec \<Rightarrow> 'c Rvec"
  where
  "ODE_sem I (OVar x) = ODEs I x"
| "ODE_sem I (OSing x \<theta>) =  (\<lambda>\<nu>. (\<chi> i. if i = x then sterm_sem I \<theta> \<nu> else 0))"
| "ODE_sem I (OProd ODE1 ODE2) = (\<lambda>\<nu>. ODE_sem I ODE1 \<nu> + ODE_sem I ODE2 \<nu>)"

(* Semantics for formulas, differential formulas, programs.
   Differential formulas do actually have to have their own notion of semantics, because
   the meaning of a differential formula (\<phi>)' depends on the syntax of the formula \<phi>:
   we can have two formulas \<phi> and \<psi> that have the exact same semantics, but where
   (\<phi>)' and (\<psi>)' differ because \<phi> and \<psi> differ syntactically.
*)
definition Vagree :: "'c::finite state \<Rightarrow> 'c state \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "Vagree \<nu> \<nu>' V \<equiv>
   (\<forall>i. Inl i \<in> V \<longrightarrow> fst \<nu> $ i = fst \<nu>' $ i)
 \<and> (\<forall>i. Inr i \<in> V \<longrightarrow> snd \<nu> $ i = snd \<nu>' $ i)"

(* The bound variables of an ODE (which will also be included as free variables) *)
fun ODE_vars :: "('a, 'c) ODE \<Rightarrow> ('c + 'c) set"
where 
  "ODE_vars (OVar c) = UNIV"
| "ODE_vars (OSing x \<theta>) = {Inl x, Inr x}"
| "ODE_vars (OProd ODE1 ODE2) = ODE_vars ODE1 \<union> ODE_vars ODE2"

fun mk_xode::"('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'c::finite) ODE \<Rightarrow> 'c::finite simple_state \<Rightarrow> 'c::finite state"
where "mk_xode I ODE sol = (sol, ODE_sem I ODE sol)"

(* Given an initial state \<nu> and solution to an ODE at some point, construct the resulting state \<omega>.
 * This is defined using the SOME operator because the concrete definition is unwieldy. *)
definition mk_v::"('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'c::finite) ODE \<Rightarrow> 'c::finite state \<Rightarrow> 'c::finite simple_state \<Rightarrow> 'c::finite state"
where "mk_v I ODE \<nu> sol = (SOME \<omega>. 
  Vagree \<omega> \<nu> (- ODE_vars ODE) 
\<and> Vagree \<omega> (mk_xode I ODE sol) (ODE_vars ODE))"

(* Because mk_v is defined with the SOME operator, need to construct a state that satisfies
   Vagree \<omega> \<nu> (- ODE_vars ODE) 
 \<and> Vagree \<omega> (mk_xode I ODE sol) (ODE_vars ODE))"
 to do anything useful *)
fun concrete_v::"('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'c::finite) ODE \<Rightarrow> 'c::finite state \<Rightarrow> 'c::finite simple_state \<Rightarrow> 'c::finite state"
where "concrete_v I ODE \<nu> sol =
((\<chi> i. (if Inl i \<in> ODE_vars ODE then sol else (fst \<nu>)) $ i),
 (\<chi> i. (if Inr i \<in> ODE_vars ODE then ODE_sem I ODE sol else (snd \<nu>)) $ i))"

lemma mk_v_exists:"\<exists>\<omega>. Vagree \<omega> \<nu> (- ODE_vars ODE) 
\<and> Vagree \<omega> (mk_xode I ODE sol) (ODE_vars ODE)"
  by(rule exI[where x="(concrete_v I ODE \<nu> sol)"])
    (auto simp add: Vagree_def)

lemma mk_v_agree:"Vagree (mk_v I ODE \<nu> sol) \<nu> (- ODE_vars ODE) 
\<and> Vagree (mk_v I ODE \<nu> sol) (mk_xode I ODE sol) (ODE_vars ODE)"
  apply (unfold mk_v_def)
  apply (rule someI_ex)
  apply (rule mk_v_exists)
  done

fun fml_sem  :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'b::finite, 'c::finite) formula \<Rightarrow> 'c::finite state set" and
  diff_formula_sem  :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'b::finite, 'c::finite) formula \<Rightarrow> 'c::finite state set" and
  prog_sem :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'b::finite, 'c::finite) hp \<Rightarrow> ('c::finite state * 'c::finite state) set"
where
  "fml_sem I (Geq t1 t2) = {v. dterm_sem I t1 v \<ge> dterm_sem I t2 v}"
| "fml_sem I (Prop P terms) = {\<nu>. Predicates I P (\<chi> i. dterm_sem I (terms i) \<nu>)}"
| "fml_sem I (Not \<phi>) = {v. v \<notin> fml_sem I \<phi>}"
| "fml_sem I (And \<phi> \<psi>) = fml_sem I \<phi> \<inter> fml_sem I \<psi>"
| "fml_sem I (Forall x \<phi>) = {v. \<forall>r. (repv v x r) \<in> fml_sem I \<phi>}"
| "fml_sem I (Box \<alpha> \<phi>) = {\<nu>. \<forall> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<longrightarrow> \<omega> \<in> fml_sem I \<phi>}"
| "fml_sem I (InContext c \<phi>) = Contexts I c (fml_sem I \<phi>)"
| "fml_sem I (DiffFormula p) = diff_formula_sem I p"

| "diff_formula_sem I (Geq f g) = {v. dterm_sem I (Differential f) v \<ge> dterm_sem I (Differential g) v}"
| "diff_formula_sem I (Not p) = diff_formula_sem I p"
| "diff_formula_sem I (And p q) = diff_formula_sem I p \<inter> diff_formula_sem I p"
  (* TODO: Totally broken: Think about predicational case *)
| "diff_formula_sem I  p = fml_sem I p"

| "prog_sem I (Pvar p) = Programs I p"
| "prog_sem I (Assign x t) = {(\<nu>, \<omega>). \<omega> = repv \<nu> x (dterm_sem I t \<nu>)}"
| "prog_sem I (DiffAssign x t) = {(\<nu>, \<omega>). \<omega> = repd \<nu> x (dterm_sem I t \<nu>)}"
| "prog_sem I (Test \<phi>) = {(\<nu>, \<nu>) | \<nu>. \<nu> \<in> fml_sem I \<phi>}"
| "prog_sem I (Choice \<alpha> \<beta>) = prog_sem I \<alpha> \<union> prog_sem I \<beta>"
| "prog_sem I (Sequence \<alpha> \<beta>) = prog_sem I \<alpha> O prog_sem I \<beta>"
| "prog_sem I (Loop \<alpha>) = (prog_sem I \<alpha>)\<^sup>*"
| "prog_sem I (EvolveODE ODE \<phi>) =
    ({(\<nu>, mk_v I ODE \<nu> (sol t)) | \<nu> sol t.
      t \<ge> 0 \<and>
      (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu> x \<in> fml_sem I \<phi>} \<and>
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
  (\<And>\<theta> :: ('a::finite, 'c::finite) trm. \<theta> \<in> range args \<Longrightarrow> (sterm_sem I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)) \<Longrightarrow>
  (sterm_sem I ($f f args) has_derivative frechet I ($f f args) \<nu>) (at \<nu>)"
apply(simp only: sfunction_case is_interp_def function_case_inner)
apply(erule func_lemma2)
apply(auto)
done

(* TODO: Should be able to remove these by adding some inductive_simp *)
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
  fixes I :: "('sf, 'sc, 'sz) interp" and \<nu>
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
fun BVF :: "('a, 'b, 'c) formula \<Rightarrow> ('c + 'c) set"
and BVP :: "('a, 'b, 'c) hp \<Rightarrow> ('c + 'c) set"
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
fun MBV :: "('a, 'b, 'c) hp \<Rightarrow> ('c + 'c) set"
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
primrec FVT :: "('a, 'c) trm \<Rightarrow> ('c + 'c) set"
where
  "FVT (Var x) = {Inl x}"
| "FVT (Const x) = {}"
| "FVT (Function f args) = (\<Union>i. FVT (args i))"
| "FVT (Plus f g) = FVT f \<union> FVT g"
| "FVT (Times f g) = FVT f \<union> FVT g"
| "FVT (Differential f) = (\<Union>x \<in> (FVT f). primify x)"
| "FVT (DiffVar x) = {Inr x}"

fun FVDiff :: "('a, 'c) trm \<Rightarrow> ('c + 'c) set"
where "FVDiff f = (\<Union>x \<in> (FVT f). primify x)"

lemma primify_contains:"x \<in> primify x"
by (cases "x") auto

lemma FVDiff_sub:"FVT f \<subseteq> FVDiff f"
by (auto simp add:  primify_contains)

(* Free variables of an ODE includes both the bound variables and the terms *)
fun FVO :: "('a, 'c) ODE \<Rightarrow> ('c + 'c) set"
  where
  "FVO (OVar c) = {}"
| "FVO (OSing x \<theta>) = FVT \<theta>"
| "FVO (OProd ODE1 ODE2) = FVO ODE1 \<union> FVO ODE2"

(* Free variables of a formula *)
(* Free variables of a program *)
fun FVF :: "('a, 'b, 'c) formula \<Rightarrow> ('c + 'c) set"
and FVP :: "('a, 'b, 'c) hp \<Rightarrow> ('c + 'c) set"
where
   "FVF (Geq f g) = FVT f \<union> FVT g"
 | "FVF (Prop p args) = (\<Union>i. FVT (args i))"
 | "FVF (Not p) = FVF p"
 | "FVF (And p q) = FVF p \<union> FVF q"
 | "FVF (Forall x p) = FVF p - {Inl x}"
 | "FVF (Box \<alpha> p) =   FVF p - MBV \<alpha>"
 | "FVF (DiffFormula p) = FVF p"
 | "FVF (InContext C p) = UNIV"
 | "FVP (Pvar a) = UNIV"
 | "FVP (Assign x \<theta>) = FVT \<theta>"
 | "FVP (DiffAssign x \<theta>) = FVT \<theta>"
 | "FVP (Test \<phi>) = FVF \<phi>"
 | "FVP (EvolveODE ODE \<phi>) = ODE_vars ODE \<union> FVO ODE \<union> FVF \<phi>"
 | "FVP (Choice \<alpha> \<beta>) = FVP \<alpha> \<union> FVP \<beta>"
 | "FVP (Sequence \<alpha> \<beta>) = (FVP \<alpha> \<union> FVP \<beta>) - (MBV \<alpha>)"
 | "FVP (Loop \<alpha>) = FVP \<alpha>"

primrec SIGT :: "('a, 'c) trm \<Rightarrow> 'a set"
where
  "SIGT (Var var) = {}"
| "SIGT (Const r) = {}"
| "SIGT (Function var f) = {var} \<union> (\<Union>i. SIGT (f i))"
| "SIGT (Plus t1 t2) = SIGT t1 \<union> SIGT t2"
| "SIGT (Times t1 t2) = SIGT t1 \<union> SIGT t2"
| "SIGT (DiffVar x) = {}"
| "SIGT (Differential t) = SIGT t"

primrec SIGO   :: "('a, 'c) ODE \<Rightarrow> ('a + 'c) set"
where
  "SIGO (OVar c) = {Inr c}"
| "SIGO (OSing x \<theta>) =  {Inl x| x. x \<in> SIGT \<theta>}"
| "SIGO (OProd ODE1 ODE2) = SIGO ODE1 \<union> SIGO ODE2"
  
primrec SIGP   :: "('a, 'b, 'c) hp      \<Rightarrow> ('a + 'b + 'c) set"
and     SIGF   :: "('a, 'b, 'c) formula \<Rightarrow> ('a + 'b + 'c) set"
where
  "SIGP (Pvar var) = {}"
| "SIGP (Assign var t) = {Inl x | x. x \<in> SIGT t}"
| "SIGP (DiffAssign var t) = {Inl x | x. x \<in> SIGT t}"
| "SIGP (Test p) = SIGF p"
| "SIGP (EvolveODE ODE p) = SIGF p \<union> {Inl x | x. Inl x \<in> SIGO ODE} \<union> {Inr (Inr x) | x. Inr x \<in> SIGO ODE}"
| "SIGP (Choice a b) = SIGP a \<union> SIGP b"
| "SIGP (Sequence a b) = SIGP a \<union> SIGP b"
| "SIGP (Loop a) = SIGP a"
| "SIGF (Geq t1 t2) = {Inl x | x. x \<in> SIGT t1 \<union> SIGT t2}"
| "SIGF (Prop var args) = {Inr (Inr var)} \<union> {Inl x | x. x \<in> (\<Union>i. SIGT (args i))}"
| "SIGF (Not p) = SIGF p"
| "SIGF (And p1 p2) = SIGF p1 \<union> SIGF p2"
| "SIGF (Forall var p) = SIGF p"
| "SIGF (Box a p) = SIGP a \<union> SIGF p"
| "SIGF (DiffFormula p) = SIGF p"
| "SIGF (InContext var p) = {Inr (Inl var)} \<union> SIGF p"

(* TODO: Distinguish identifiers for functions, predicates, etc*)
definition Iagree :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a + 'b + 'c) set \<Rightarrow> bool"
where "Iagree I J V \<equiv>
  (\<forall>i\<in>V.
    (\<exists>x. i = Inl x \<longrightarrow> Functions I x = Functions J x) \<and>
    (\<exists>x. i = Inr (Inl x) \<longrightarrow> Contexts I x = Contexts J x) \<and>
    (\<exists>x. i = Inr (Inr x) \<longrightarrow> Predicates I x = Predicates J x) \<and>
    (\<exists>x. i = Inr (Inr x) \<longrightarrow> Programs I x = Programs J x))"

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
  fix i :: 'a
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


lemma has_vector_derivative_zero_constant:
  assumes "convex s"
  assumes "\<And>x. x \<in> s \<Longrightarrow> (f has_vector_derivative 0) (at x within s)"
  obtains c where "\<And>x. x \<in> s \<Longrightarrow> f x = c"
  using has_derivative_zero_constant[of s f] assms
  by (auto simp: has_vector_derivative_def)

lemma has_vderiv_on_zero_constant:
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
  fixes x t::real and i::'sz
  assumes "t > 0"
  shows "x = (ll_on_open.flow UNIV (\<lambda>t. \<lambda>x. \<chi> (i::'sz). 0) UNIV 0 (\<chi> i. x) t) $ i"
proof -
  let ?T = UNIV
  let ?f = "(\<lambda>t. \<lambda>x. \<chi> i::'sz. 0)"
  let ?X = UNIV
  let ?t0.0 = 0
  let ?x0.0 = "\<chi> i::'sz. x"
  interpret ll: ll_on_open "UNIV" "(\<lambda>t x. \<chi> i::'sz. 0)" UNIV
    apply unfold_locales
    using gt_ex lipschitz_constI
    by (force simp: interval_def continuous_on_def local_lipschitz_def)+
  have foo1:"?t0.0 \<in> ?T" by auto
  have foo2:"?x0.0 \<in> ?X" by auto
  let ?v = "ll.flow  ?t0.0 ?x0.0"
  from ll.flow_solves_ode[OF foo1 foo2]
  have solves:"(ll.flow  ?t0.0 ?x0.0 solves_ode ?f) (ll.existence_ivl  ?t0.0 ?x0.0) ?X"  by (auto)
  then have solves:"(?v solves_ode ?f) (ll.existence_ivl  ?t0.0 ?x0.0) ?X" by auto
  have thex0: "(?v ?t0.0) $ (i::'sz) = x" by auto
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
  shows "\<And>\<nu> :: 'sz state. \<And>\<omega> ::'sz state. (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<Longrightarrow> Vagree \<nu> \<omega> (- (BVP \<alpha>))"
proof (induct rule: hp_induct)
  case Var then show "?case" 
    using agree_nil Compl_UNIV_eq pointed_finite.BVP.simps(1) by fastforce
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
    assume sem:"(\<nu>, \<omega>) \<in> prog_sem I (EvolveODE ODE P)"
    have agree_comm:"\<And>A B V. Vagree A B V \<Longrightarrow> Vagree B A V" unfolding Vagree_def by auto
    from sem have agree:"Vagree \<nu> \<omega> (- ODE_vars ODE)"
      apply(simp only: prog_sem.simps mem_Collect_eq)
      apply(erule exE)+
      proof -
        fix \<nu>' sol t  
        assume assm: "(\<nu>, \<omega>) = (\<nu>', mk_v I ODE \<nu>' (sol t)) \<and>
           0 \<le> t \<and>
           (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu>' x \<in> fml_sem I P} \<and> sol 0 = fst \<nu>'"
        hence "Vagree \<omega> \<nu> (- ODE_vars ODE)" using mk_v_agree[of I ODE \<nu> "(sol t)"] by auto
        thus  "Vagree \<nu> \<omega> (- ODE_vars ODE)" by (rule agree_comm)
      qed 
    thus "Vagree \<nu> \<omega> (- BVP (EvolveODE ODE P))" by auto
  qed
next
  case (Star a \<nu> \<omega>) then
    show "?case" 
      apply (simp only: prog_sem.simps)
      apply (erule converse_rtrancl_induct)
      by (auto simp add: Vagree_def)
qed (auto simp add: Vagree_def)

lemma coincidence_sterm:"Vagree \<nu> \<nu>' (FVT \<theta>) \<Longrightarrow> sterm_sem I  \<theta> (fst \<nu>) = sterm_sem I \<theta> (fst \<nu>')"
  apply(induct "\<theta>")
  apply(auto simp add: Vagree_def)
  by (meson rangeI)

lemma coincidence_formula:"Vagree \<nu> \<nu>' (FVF \<phi>) \<Longrightarrow> ((\<nu> \<in> fml_sem I \<phi>) \<longleftrightarrow> (\<nu>' \<in> fml_sem I \<phi>))"
  sorry

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
  fixes I :: "('sf, 'sc, 'sz) interp" and \<nu> :: "'sz state" and \<nu>'::"'sz state"
  shows "dfree \<theta> \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff \<theta>) \<Longrightarrow> frechet I  \<theta> (fst \<nu>) (snd \<nu>) = frechet I  \<theta> (fst \<nu>') (snd \<nu>')"
 proof (induction rule: dfree.induct)
  case dfree_Var then show ?case
    by (auto simp: inner_prod_eq Vagree_def simp del: basis_vector.simps)
next
  case dfree_Const then show ?case
    by auto
next
  case (dfree_Fun args var)
  assume free:"(\<And>i. dfree (args i))"
  assume IH:"(\<And>i. Vagree \<nu> \<nu>' (FVDiff (args i)) \<Longrightarrow> frechet I (args i) (fst \<nu>) (snd \<nu>) = frechet I (args i) (fst \<nu>') (snd \<nu>'))"
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
  fixes I :: "('sf::finite, 'sc::finite, 'sz::finite) interp" and \<nu> :: "'sz state" and \<nu>'::"'sz state"
  shows "dsafe \<theta> \<Longrightarrow> Vagree \<nu> \<nu>' (FVT \<theta>) \<Longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I \<theta> \<nu>'"
proof (induction rule: dsafe.induct)
  case dsafe_Var then show "?case" using Vagree_def rangeI 
    by (smt insert_iff mem_Collect_eq pointed_finite.FVT.simps(1) pointed_finite.dterm_sem.simps(1))

next
  case dsafe_Const then show "?case"
    by (auto)

next
  case (dsafe_Fun args f)
    assume safe:"(\<And>i. dsafe (args i))"
    assume IH:"\<And>i. Vagree \<nu> \<nu>' (FVT (args i)) \<Longrightarrow> dterm_sem I (args i) \<nu> = dterm_sem I (args i) \<nu>'"
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

definition valid :: "('sf, 'sc, 'sz) formula \<Rightarrow> bool"
where "valid \<phi> \<equiv> (\<forall> I. \<forall> \<nu>. is_interp I \<longrightarrow> \<nu> \<in> fml_sem I \<phi>)"

(* Arguments for a "nullary" function - a tuple of all-zeros. When we encode
  a function that has less than the maximum allowed number of arguments, we
  do so by making the remaining arguments 0 at every use site. We can't actually
  enforce that the interpretation of the function "doesnt care" about an argument,
  but if we never use that argument at more than one value there's no way to "notice"
  that the extra arguments exist *)
definition empty :: "('sf, 'sz) dtuple"
  where "empty \<equiv> \<lambda>i.(Const 0)"

(* Function argument tuple where the first argument is arbitrary and the rest are zero.*)
fun singleton :: "('sf, 'sz) trm \<Rightarrow> ('sf, 'sz) dtuple"
  where "singleton t i = (if i = vid1 then t else (Const 0))"

(* Equivalents of the above for functions over simple terms. *)
definition sempty :: "('sf, 'sz) stuple"
  where "sempty _ \<equiv> (Const 0)"

fun ssingleton :: "('sf, 'sz) trm \<Rightarrow> ('sf, 'sz) stuple"
  where "ssingleton t var = (if var = vid1 then t else (Const 0))"

definition assign_axiom :: "('sf, 'sc, 'sz) formula"
  where "assign_axiom \<equiv>
    ([[vid1 := ($f fid1 empty)]] (Prop vid1 (singleton (Var vid1))))
      \<leftrightarrow> Prop vid1 (singleton ($f fid1 empty))"

definition loop_iterate_axiom :: "('sf, 'sc, 'sz) formula"
  where "loop_iterate_axiom \<equiv> ([[$\<alpha> vid1**]]Predicational pid1)
    \<leftrightarrow> ((Predicational pid1) && ([[$\<alpha> vid1]][[$\<alpha> vid1**]]Predicational pid1))"

definition test_axiom :: "('sf, 'sc, 'sz) formula"
  where "test_axiom \<equiv>
    ([[?($\<phi> vid2 empty)]]$\<phi> vid1 empty) \<leftrightarrow> (($\<phi> vid2 empty) \<rightarrow> ($\<phi> vid1 empty))"

definition box_axiom :: "('sf, 'sc, 'sz) formula"
  where "box_axiom \<equiv> (\<langle>$\<alpha> vid1\<rangle>Predicational pid1) \<leftrightarrow> !([[$\<alpha> vid1]]!(Predicational pid1))"

definition choice_axiom :: "('sf, 'sc, 'sz) formula"
  where "choice_axiom \<equiv> ([[$\<alpha> vid1 \<union>\<union> $\<alpha> vid2]]Predicational pid1)
    \<leftrightarrow> (([[$\<alpha> vid1]]Predicational pid1) && ([[$\<alpha> vid2]]Predicational pid1))"

definition Kaxiom :: "('sf, 'sc, 'sz) formula"
  where "Kaxiom \<equiv> ([[$\<alpha> vid1]]((Predicational pid1) \<rightarrow> (Predicational pid2)))
    \<rightarrow> ([[$\<alpha> vid1]]Predicational pid1) \<rightarrow> ([[$\<alpha> vid1]]Predicational pid2)"

(*
definition Ibroken :: "('sf, 'sc, 'sz) formula"
  where "Ibroken \<equiv> ([[$$a]]($P [] \<rightarrow> ([[$$a]]$P []))
    \<rightarrow> ($P [] \<rightarrow> ([[($$a)**]]$P [])))"*)

definition Iaxiom :: "('sf, 'sc, 'sz) formula"
  where "Iaxiom \<equiv> 
  ([[($\<alpha> vid1)**]](Predicational pid1 \<rightarrow> ([[$\<alpha> vid1]]Predicational pid1)))
    \<rightarrow>((Predicational pid1 \<rightarrow> ([[($\<alpha> vid1)**]]Predicational pid1)))"

definition Vaxiom :: "('sf, 'sc, 'sz) formula"
  where "Vaxiom \<equiv> ($\<phi> vid1 empty) \<rightarrow> ([[$\<alpha> vid1]]($\<phi> vid1 empty))"

definition G_holds :: "('sf, 'sc, 'sz) formula \<Rightarrow> ('sf, 'sc, 'sz) hp \<Rightarrow> bool"
  where "G_holds \<phi> \<alpha> \<equiv> valid \<phi> \<longrightarrow> valid ([[\<alpha>]]\<phi>)"

definition Skolem_holds :: "('sf, 'sc, 'sz) formula \<Rightarrow> 'sz \<Rightarrow> bool"
  where "Skolem_holds \<phi> var \<equiv> valid \<phi> \<longrightarrow> valid (Forall var \<phi>)"

definition MP_holds :: "('sf, 'sc, 'sz) formula \<Rightarrow> ('sf, 'sc, 'sz) formula \<Rightarrow> bool"
  where "MP_holds \<phi> \<psi> \<equiv> valid (\<phi> \<rightarrow> \<psi>) \<longrightarrow> valid \<phi> \<longrightarrow> valid \<psi>"

definition CT_holds :: "'sf \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> bool"
  where "CT_holds g \<theta> \<theta>' \<equiv> valid (Equals \<theta> \<theta>')
    \<longrightarrow> valid (Equals (Function g (singleton \<theta>)) (Function g (singleton \<theta>')))"

definition CQ_holds :: "'sz \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> bool"
  where "CQ_holds p \<theta> \<theta>' \<equiv> valid (Equals \<theta> \<theta>')
    \<longrightarrow> valid ((Prop p (singleton \<theta>)) \<leftrightarrow> (Prop p (singleton \<theta>')))"

definition CE_holds :: "'sc \<Rightarrow> ('sf, 'sc, 'sz) formula \<Rightarrow> ('sf, 'sc, 'sz) formula \<Rightarrow> bool"
  where "CE_holds var \<phi> \<psi> \<equiv> valid (\<phi> \<leftrightarrow> \<psi>)
    \<longrightarrow> valid (InContext var \<phi> \<leftrightarrow> InContext var \<psi>)"

definition diff_const_axiom :: "('sf, 'sc, 'sz) formula"
  where "diff_const_axiom \<equiv> Equals (Differential ($f fid1 sempty)) (Const 0)"

lemma or_sem [simp]:
  "fml_sem I (Or \<phi> \<psi>) = fml_sem I \<phi> \<union> fml_sem I \<psi>"
  by (auto simp add: Or_def)

lemma iff_sem [simp]: "(\<nu> \<in> fml_sem I (A \<leftrightarrow> B))
  \<longleftrightarrow> ((\<nu> \<in> fml_sem I A) \<longleftrightarrow> (\<nu> \<in> fml_sem I B))"
  by (auto simp add: Equiv_def)

lemma box_sem:"fml_sem I (Box \<alpha> \<phi>) = {\<nu>. \<forall> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<longrightarrow> \<omega> \<in> fml_sem I \<phi>}"
  by (auto)

lemma loop_sem:"prog_sem I (Loop \<alpha>) = (prog_sem I \<alpha>)\<^sup>*"
  by (auto)

lemma impl_sem [simp]: "(\<nu> \<in> fml_sem I (A \<rightarrow> B))
  = ((\<nu> \<in> fml_sem I A) \<longrightarrow> (\<nu> \<in> fml_sem I B))"
  by (auto simp add: Implies_def)

lemma equals_sem [simp]: "(\<nu> \<in> fml_sem I (Equals \<theta> \<theta>'))
  = (dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu>)"
  by (auto simp add: Equals_def)

lemma diamond_sem [simp]: "fml_sem I (Diamond \<alpha> \<phi>)
  = {\<nu>. \<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<and> \<omega> \<in> fml_sem I \<phi>}"
  by (auto simp add: Diamond_def)

lemma iff_to_impl: "((\<nu> \<in> fml_sem I A) \<longleftrightarrow> (\<nu> \<in> fml_sem I B))
  \<longleftrightarrow> (((\<nu> \<in> fml_sem I A) \<longrightarrow> (\<nu> \<in> fml_sem I B))
     \<and> ((\<nu> \<in> fml_sem I B) \<longrightarrow> (\<nu> \<in> fml_sem I A)))"
by (auto)

lemma vec_extensionality:"(\<And>i. v$i = w$i) \<Longrightarrow> (v = w)"
  by (simp add: vec_eq_iff)

lemma proj_sing1:"(singleton \<theta> vid1) = \<theta>"
  by (auto simp add: singleton_def)

lemma proj_sing2:"vid1 \<noteq> y  \<Longrightarrow> (singleton \<theta> y) = (Const 0)"
  by (auto simp add: singleton_def)

theorem test_valid: "valid test_axiom"
  by (auto simp add: valid_def test_axiom_def)

lemma assign_lem1:
"dterm_sem I (if i = vid1 then Var vid1 else (Const 0))
                   (vec_lambda (\<lambda>y. if vid1 = y then Functions I fid1
  (vec_lambda (\<lambda>i. dterm_sem I (empty i) \<nu>)) else  vec_nth (fst \<nu>) y), snd \<nu>)
=
 dterm_sem I (if i = vid1 then $f fid1 empty else (Const 0)) \<nu>
"
 by (case_tac "i = vid1") (auto simp add: proj_sing1)

lemma assign_lem:
"dterm_sem I (singleton (Var vid1) i)
   (vec_lambda (\<lambda>y. if y = vid1  then Functions I fid1 (vec_lambda (\<lambda>i. dterm_sem I (empty i) \<nu>)) else vec_nth (fst \<nu>) y), snd \<nu>)
                   =
 dterm_sem I (singleton ($f fid1 empty) i) \<nu>"
 by (case_tac "i = vid1 ") (auto simp add: proj_sing1)

theorem assign_valid: "valid assign_axiom"
  apply(simp only: valid_def assign_axiom_def)
  apply(rule allI | rule impI)+
  apply(simp only: iff_sem fml_sem.simps mem_Collect_eq prog_sem.simps)
  apply(simp)
  apply(simp only: assign_lem1)
  done

lemma mem_to_nonempty: "\<omega> \<in> S \<Longrightarrow> (S \<noteq> {})"
  by (auto)

lemma loop_forward: "\<nu> \<in> fml_sem I ([[$\<alpha> id1**]]Predicational pid1)
  \<longrightarrow> \<nu> \<in> fml_sem I (Predicational pid1&&[[$\<alpha> id1]][[$\<alpha> id1**]]Predicational pid1)"
  by (cases \<nu>) (auto intro: converse_rtrancl_into_rtrancl)

lemma nat_case: "\<forall>n::nat. (n = 0) \<or> (\<exists>m. n = Suc m)"
  by (rule Nat.nat.nchotomy)

lemma loop_backward:
 "\<nu> \<in> fml_sem I (Predicational pid1 && [[$\<alpha> id1]][[$\<alpha> id1**]]Predicational pid1)
  \<longrightarrow> \<nu> \<in> fml_sem I ([[$\<alpha> id1**]]Predicational pid1)"
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
fixes I::"('sf,'sc,'sz) interp" and \<nu>
assumes "is_interp I"
assumes IS:"\<nu> \<in> fml_sem I ([[$\<alpha> vid1**]](Predicational pid1 \<rightarrow>
                          [[$\<alpha> vid1]]Predicational pid1))"
assumes BC:"\<nu> \<in> fml_sem I (Predicational pid1)"
shows "\<nu> \<in> fml_sem I ([[$\<alpha> vid1**]](Predicational pid1))"
proof -
  have IS':"\<And>\<nu>2. (\<nu>, \<nu>2) \<in> (prog_sem I ($\<alpha> vid1))\<^sup>* \<Longrightarrow> \<nu>2 \<in> fml_sem I (Predicational pid1 \<rightarrow> [[$\<alpha> vid1]](Predicational pid1))"
    using IS by auto
  have res:"\<And>\<nu>3. ((\<nu>, \<nu>3) \<in> (prog_sem I ($\<alpha> vid1))\<^sup>*) \<Longrightarrow> \<nu>3 \<in> fml_sem I (Predicational pid1)"
  proof -
    fix \<nu>3 
    show "((\<nu>, \<nu>3) \<in> (prog_sem I ($\<alpha> vid1))\<^sup>*) \<Longrightarrow> \<nu>3 \<in> fml_sem I (Predicational pid1)"
    apply(induction rule:rtrancl_induct)
    apply(rule BC)
    proof -
      fix y z
      assume vy:"(\<nu>, y) \<in> (prog_sem I ($\<alpha> vid1))\<^sup>*"
      assume yz:"(y, z) \<in> prog_sem I ($\<alpha> vid1)"
      assume yPP:"y \<in> fml_sem I (Predicational pid1)"
      have imp3:"y \<in> fml_sem I (Predicational pid1 \<rightarrow> [[$\<alpha> vid1 ]](Predicational pid1))"
        using IS' vy by (simp)
      have imp4:"y \<in> fml_sem I (Predicational pid1) \<Longrightarrow> y \<in> fml_sem I  ([[$\<alpha> vid1]](Predicational pid1))"
        using imp3 impl_sem by (auto)
      have yaPP:"y \<in> fml_sem I ([[$\<alpha> vid1]]Predicational pid1)" using imp4 yPP by auto
      have zPP:"z \<in> fml_sem I (Predicational pid1)" using yaPP box_sem yz mem_Collect_eq by blast  
      show "
        (\<nu>, y) \<in> (prog_sem I ($\<alpha> vid1))\<^sup>* \<Longrightarrow>
        (y, z) \<in> prog_sem I ($\<alpha> vid1) \<Longrightarrow>
        y \<in> fml_sem I (Predicational pid1) \<Longrightarrow>
        z \<in> fml_sem I (Predicational pid1)" using zPP by simp
    qed
  qed
  show "\<nu> \<in> fml_sem I ([[$\<alpha> vid1**]]Predicational pid1)"
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

lemma CT_lemma:"\<And>I::('sf::finite, 'sc::finite, 'sz::finite) interp. \<And> a::(real, 'sz) vec. \<And> b::(real, 'sz) vec. \<forall>I::('sf,'sc,'sz) interp. is_interp I \<longrightarrow> (\<forall>a b. dterm_sem I \<theta> (a, b) = dterm_sem I \<theta>' (a, b)) \<Longrightarrow>
             is_interp I \<Longrightarrow>
             Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta> else  (Const 0)) (a, b))) =
             Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta>' else (Const 0)) (a, b)))"
proof -
  fix I :: "('sf::finite, 'sc::finite, 'sz::finite) interp" and a :: "(real, 'sz) vec" and b :: "(real, 'sz) vec"
  assume a1: "is_interp I"
  (* NOTE: example of type annotation sadness here *)
  assume "\<forall>I::('sf,'sc,'sz) interp. is_interp I \<longrightarrow> (\<forall>a b. dterm_sem I \<theta> (a, b) = dterm_sem I \<theta>' (a, b))"
  then have "\<forall>i. dterm_sem I (if i = vid1 then \<theta>' else (Const 0)) (a, b) = dterm_sem I (if i = vid1 then \<theta> else (Const 0)) (a, b)"
    using a1 by presburger
  then show "Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta> else (Const 0)) (a, b)))
           = Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta>' else (Const 0)) (a, b)))"
    by presburger
qed

theorem CT_sound: "CT_holds var \<theta> \<theta>'"
  apply(simp only: CT_holds_def valid_def equals_sem vec_extensionality vec_eq_iff)
  apply(simp)
  apply(rule allI | rule impI)+
  apply(simp add: CT_lemma)
done

(* TODO: I think this lemma actually makes no sense.*)
lemma CQ_lemma:"\<And>I::('sf,'sc,'sz) interp. \<And>\<nu>. \<forall>I::('sf,'sc,'sz) interp. \<forall>\<nu>. is_interp I \<longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu> \<Longrightarrow>
           is_interp I \<Longrightarrow>
           Predicates I (var::'sz) (vec_lambda(\<lambda>i. dterm_sem I (if i = vid1 then \<theta> else  (Const 0)) \<nu>)) =
           Predicates I var (vec_lambda(\<lambda>i. dterm_sem I (if i = vid1 then \<theta>' else (Const 0)) \<nu>))"
proof -
  fix I :: "('sf,'sc,'sz) interp" and \<nu> :: "(real, 'sz) vec \<times> (real, 'sz) vec"
  assume a1: "\<forall>I::('sf,'sc,'sz) interp. \<forall> \<nu>. is_interp I \<longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu>"
  assume a2: "is_interp I"
  obtain ff :: "('sz \<Rightarrow> real) \<Rightarrow> ('sz \<Rightarrow> real) \<Rightarrow> 'sz" where
    f3: "\<forall>f fa. f (ff fa f) \<noteq> fa (ff fa f) \<or> vec_lambda f = vec_lambda fa"
    by (meson Cart_lambda_cong)
  have "dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu> "
    using a2 a1 by blast
  then have "dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else  (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>) = vid1 then \<theta> else (Const 0)) \<nu> \<noteq> dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else  (Const 0)) \<nu>) = vid1 then \<theta>' else (Const 0)) \<nu> \<longrightarrow> dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>) = vid1 then \<theta> else (Const 0)) \<nu> = dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>) = vid1 then \<theta>' else (Const 0)) \<nu>"
    by simp
  then have "(vec_lambda(\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>)) = (vec_lambda(\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else  (Const 0)) \<nu>))"
    using f3 by meson
  then show "Predicates I (var::'sz) (vec_lambda(\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>)) = Predicates I var (vec_lambda(\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else  (Const 0)) \<nu>))"
  (* TODO: Simplify. This subproof used to be a one-line "by presburger" *)
  proof -
    obtain ss :: "('sz \<Rightarrow> real) \<Rightarrow> ('sz \<Rightarrow> real) \<Rightarrow> 'sz" where
      f1: "\<forall>f fa. f (ss fa f) \<noteq> fa (ss fa f) \<or> vec_lambda f = vec_lambda fa"
      by (meson Cart_lambda_cong)
    have "dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = vid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = vid1 then \<theta> else Const 0) \<nu>) = vid1 then \<theta> else Const 0) \<nu> \<noteq> dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = vid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = vid1 then \<theta> else Const 0) \<nu>) = vid1 then \<theta>' else Const 0) \<nu> \<longrightarrow> dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = vid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = vid1 then \<theta> else Const 0) \<nu>) = vid1 then \<theta> else Const 0) \<nu> = dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = vid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = vid1 then \<theta> else Const 0) \<nu>) = vid1 then \<theta>' else Const 0) \<nu>"
      using \<open>dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu>\<close> by presburger
    then have "(\<chi> s. dterm_sem I (if s = vid1 then \<theta> else Const 0) \<nu>) = (\<chi> s. dterm_sem I (if s = vid1 then \<theta>' else Const 0) \<nu>)"
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


subsection \<open>ODE Axioms\<close>
definition DWaxiom :: "('sf, 'sc, 'sz) formula"
  where "DWaxiom = ([[EvolveODE (OVar vid1) (Predicational pid1)]](Predicational pid1))"

definition DWaxiom' :: "('sf, 'sc, 'sz) formula"
  where "DWaxiom' = ([[EvolveODE (OSing vid1 (Function fid1 (singleton (Var vid1)))) (Prop vid2 (singleton (Var vid1)))]](Prop vid2 (singleton (Var vid1))))"
  
definition DCaxiom :: "('sf, 'sc, 'sz) formula"
  where "DCaxiom = (
([[EvolveODE (OVar vid1) (Predicational pid1)]]Predicational pid3) \<rightarrow>
(([[EvolveODE (OVar vid1) (Predicational pid1)]](Predicational pid2)) 
  \<leftrightarrow>  
       ([[EvolveODE (OVar vid1) (And (Predicational pid1) (Predicational pid3))]]Predicational pid2)))"

definition f1::"'sf \<Rightarrow> 'sz \<Rightarrow> ('sf,'sz) trm"
where "f1 f x = Function f (singleton (Var x))"

definition f0::"'sf \<Rightarrow> ('sf,'sz) trm"
where "f0 f = Function f empty"

definition p1::"'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sc, 'sz) formula"
where "p1 p x = Prop p (singleton (Var x))"

definition P::"'sc \<Rightarrow> ('sf, 'sc, 'sz) formula"
where "P p = Predicational p"

definition DEaxiom :: "('sf, 'sc, 'sz) formula"
  where "DEaxiom = 
(([[EvolveODE (OSing vid1 (f1 fid1 vid1)) (p1 vid2 vid1)]] (P pid1))
\<leftrightarrow>
 ([[EvolveODE (OSing vid1 (f1 fid1 vid1)) (p1 vid2 vid1)]]
    [[DiffAssign vid1 (f1 fid1 vid1)]]P pid1))"

  
(* 
Function symbols?
[x'=c()&Q(1)]3(1)
<-> A t. (t \<ge> 0) \<rightarrow> (A s. (s\<ge>0 & t\<ge>s) \<rightarrow> Q(x+(c*s))) \<rightarrow> 
  [x:= x+(c()*t)]Q(x)) 
q should be x. change it!
*)
definition DSaxiom :: "('sf, 'sc, 'sz) formula"
  where "DSaxiom = 
(([[EvolveODE (OSing vid1 (f0 fid1)) (p1 vid2 vid1)]]p1 vid3 vid1)
\<leftrightarrow> 
(Forall vid2 
 (Implies (Geq (Var vid2) (Const 0)) 
 (Implies 
   (Forall vid3 
     (Implies (And (Geq (Var vid3) (Const 0)) (Geq (Var vid2) (Var vid3)))
        (Prop vid2 (singleton (Plus (Var vid1) (Times (f0 fid1) (Var vid3)))))))
   ([[Assign vid1 (Plus (Var vid1) (Times (f0 fid1) (Var vid2)))]]p1 vid3 vid1)))))"

definition DIaxiom :: "('sf, 'sc, 'sz) formula"
  where "DIaxiom = (((Predicational pid1) \<rightarrow> (And (Predicational pid2) ([[EvolveODE (OVar vid1) (Predicational pid1)]](DiffFormula (Predicational pid2))))) 
\<rightarrow> ([[EvolveODE (OVar vid1) (Predicational pid1)]]Predicational pid2))"

definition DGaxiom :: "('sf, 'sc, 'sz) formula"
  where "DGaxiom = (([[EvolveODE (OVar vid1) (Predicational pid1)]]Predicational pid2) \<leftrightarrow> 
  (Exists vid2 
    ([[EvolveODE (OProd (OVar vid1) (OSing vid2 (Plus (Times (Function fid1 empty) (Var vid2)) (Function fid2 empty)))) (Predicational pid1)]]
       Predicational pid2)))"

lemma Vagree_univ:"\<And>a b c d. Vagree (a,b) (c,d) UNIV \<Longrightarrow> a = c \<and> b = d"
  by (auto simp add: Vagree_def vec_eq_iff)
  
lemma DW_valid:"valid DWaxiom"
  apply(unfold DWaxiom_def valid_def Let_def impl_sem )
  apply(safe)
  apply(auto simp only: fml_sem.simps prog_sem.simps)
  subgoal for I aa ba ab bb sol t using mk_v_agree[of I "(OVar vid1)" "(ab,bb)" "sol t"]
    Vagree_univ[of "aa" "ba" "sol t" "ODEs I vid1 (sol t)"] solves_ode_domainD
    by (fastforce)
  done

lemma DE_lemma:
"repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1 (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))
 = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)"
proof
  have agree:"Vagree (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) (mk_xode I (OSing vid1 (f1 fid1 vid1)) (sol t))
      {Inl vid1, Inr vid1}" 
    using mk_v_agree[of I "(OSing vid1 (f1 fid1 vid1))" "(ab, bb)" "(sol t)"] by auto
  have fact:"dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t))
          = snd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) $ vid1"
    using agree apply(simp only: Vagree_def dterm_sem.simps f1_def mk_xode.simps)
    proof -
      assume alls:"(\<forall>i. Inl i \<in> {Inl vid1, Inr vid1} \<longrightarrow>
          fst (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t)) $ i =
          fst (sol t, ODE_sem I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (sol t)) $ i) \<and>
        (\<forall>i. Inr i \<in> {Inl vid1, Inr vid1} \<longrightarrow>
          snd (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t)) $ i =
          snd (sol t, ODE_sem I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (sol t)) $ i)"
      hence atVid'':"snd (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t)) $ vid1 = sterm_sem I ($f fid1 (singleton (trm.Var vid1))) (sol t)" 
        by auto
      have argsEq:"(\<chi> i. dterm_sem I (singleton (trm.Var vid1) i)
            (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t)))
            = (\<chi> i.  sterm_sem I (singleton (trm.Var vid1) i) (sol t))"
        using agree by (simp add: vec_extensionality Vagree_def f1_def)
      thus "Functions I fid1 (\<chi> i. dterm_sem I (singleton (trm.Var vid1) i)
            (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t))) 
          = snd (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t)) $ vid1"
        by (simp only: atVid'' ODE_sem.simps sterm_sem.simps dterm_sem.simps)
    qed
  have eqSnd:"(\<chi> y. if vid1 = y then snd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) $ vid1
        else snd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) $ y) = snd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t))"
    by (simp add: vec_extensionality)
  have truth:"repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
        (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))
      = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)"
    using fact by (auto simp only: eqSnd repd.simps fact prod.collapse split: if_split)
  thus "fst (repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
          (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))) =
    fst (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t))"

    "snd (repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
      (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))) =
    snd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) " 
    by auto
qed

lemma DE_valid:"valid DEaxiom"
(*  apply (simp add: DEaxiom_def valid_def Let_def 
    del: fml_sem.simps prog_sem.simps 
    add: fml_sem.simps(6) prog_sem.simps(7) )
  apply (intro allI impI arg_cong[where f=All] ext imp_cong refl)
  apply (auto simp del: prog_sem.simps)
  subgoal for I a b aa ba ab bb
  apply (auto simp only: prog_sem.simps fml_sem.simps)
  using DE_lemma sledgehammer
  
  apply (auto simp: DEaxiom_def valid_def Let_def)
  
  *)
  apply(auto simp only: DEaxiom_def valid_def Let_def iff_sem impl_sem)
  apply(auto simp only: fml_sem.simps prog_sem.simps mem_Collect_eq)
proof -
  fix I::"('sf,'sc,'sz) interp"
  and aa ba ab bb sol 
  and t::real
  and ac bc
   assume "is_interp I"
   assume allw:"\<forall>\<omega>. (\<exists>\<nu> sol t.
                ((ab, bb), \<omega>) = (\<nu>, mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> (sol t)) \<and>
                0 \<le> t \<and>
                (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f1 fid1 vid1)))) {0..t}
                 {x. mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> x \<in> fml_sem I (p1 vid2 vid1)} \<and>
                sol 0 = fst \<nu>) \<longrightarrow>
            \<omega> \<in> fml_sem I (P pid1)"
    assume t:"0 \<le> t"
    assume aaba:"(aa, ba) = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)"
    assume solve:" (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f1 fid1 vid1)))) {0..t}
        {x. mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) x \<in> fml_sem I (p1 vid2 vid1)}"
    assume sol0:"   sol 0 = fst (ab, bb)"
    assume rep:"   (ac, bc) =
       repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
        (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))"
    have aaba_sem:"(aa,ba) \<in> fml_sem I (P pid1)" using allw t aaba solve sol0 rep by blast
    have truth:"repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
        (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))
   = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)"
      using DE_lemma by auto
    show "
       repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
        (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))
       \<in> fml_sem I (P pid1)" using aaba aaba_sem truth by auto
  next
    fix I::"('sf,'sc,'sz) interp" and  aa ba ab bb sol and t::real
       assume "is_interp I"
       assume all:"\<forall>\<omega>. (\<exists>\<nu> sol t.
                ((ab, bb), \<omega>) = (\<nu>, mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> (sol t)) \<and>
                0 \<le> t \<and>
                (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f1 fid1 vid1)))) {0..t}
                 {x. mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> x \<in> fml_sem I (p1 vid2 vid1)} \<and>
                sol 0 = fst \<nu>) \<longrightarrow>
            (\<forall>\<omega>'. \<omega>' = repd \<omega> vid1 (dterm_sem I (f1 fid1 vid1) \<omega>) \<longrightarrow> \<omega>' \<in> fml_sem I (P pid1))"
       hence justW:"(\<exists>\<nu> sol t.
                ((ab, bb), (aa, ba)) = (\<nu>, mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> (sol t)) \<and>
                0 \<le> t \<and>
                (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f1 fid1 vid1)))) {0..t}
                 {x. mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> x \<in> fml_sem I (p1 vid2 vid1)} \<and>
                sol 0 = fst \<nu>) \<longrightarrow>
            (\<forall>\<omega>'. \<omega>' = repd (aa, ba) vid1 (dterm_sem I (f1 fid1 vid1) (aa, ba)) \<longrightarrow> \<omega>' \<in> fml_sem I (P pid1))"
         by (rule allE)
       assume t:"0 \<le> t"
       assume aaba:"(aa, ba) = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)"
       assume sol:"(sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f1 fid1 vid1)))) {0..t}
        {x. mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) x \<in> fml_sem I (p1 vid2 vid1)}"
       assume sol0:" sol 0 = fst (ab, bb)"
       have "repd (aa, ba) vid1 (dterm_sem I (f1 fid1 vid1) (aa, ba)) \<in> fml_sem I (P pid1)"
         using justW t aaba sol sol0 by auto
       hence foo:"repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1 (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t))) \<in> fml_sem I (P pid1)"
         using aaba by auto
       hence "repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1 (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))
             = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)" using DE_lemma by auto
       thus "mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t) \<in> fml_sem I (P pid1)" using foo by auto
  qed
  
lemma DC_valid:"valid DCaxiom" 
  apply(auto simp only: fml_sem.simps prog_sem.simps DCaxiom_def valid_def iff_sem impl_sem)
  apply(auto)
  apply(smt intervalE pointed_finite.mem_to_nonempty solves_ode_domainD)
  by fastforce
  
lemma DS_valid:"valid DSaxiom"
  apply(auto simp only: DSaxiom_def valid_def Let_def iff_sem impl_sem)
  apply(auto simp only: fml_sem.simps prog_sem.simps mem_Collect_eq  iff_sem impl_sem)
  proof -
    fix I::"('sf,'sc,'sz) interp" 
    and a b r aa ba
   assume good_interp:"is_interp I"
   assume allW:"\<forall>\<omega>. (\<exists>\<nu> sol t.
              ((a, b), \<omega>) = (\<nu>, mk_v I (OSing vid1 (f0 fid1)) \<nu> (sol t)) \<and>
              0 \<le> t \<and>
              (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..t}
               {x. mk_v I (OSing vid1 (f0 fid1)) \<nu> x \<in> fml_sem I (p1 vid2 vid1)} \<and>
              sol 0 = fst \<nu>) \<longrightarrow>
          \<omega> \<in> fml_sem I (p1 vid3 vid1)"
   assume "dterm_sem I (Const 0) (repv (a, b) vid2 r) \<le> dterm_sem I (trm.Var vid2) (repv (a, b) vid2 r)"
     hence leq:"0 \<le> r" by (auto)
   assume "\<forall>ra. repv (repv (a, b) vid2 r) vid3 ra
          \<in> {v. dterm_sem I (Const 0) v \<le> dterm_sem I (trm.Var vid3) v} \<inter>
             {v. dterm_sem I (trm.Var vid3) v \<le> dterm_sem I (trm.Var vid2) v} \<longrightarrow>
          Predicates I vid2
           (\<chi> i. dterm_sem I (singleton (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3))) i)
                  (repv (repv (a, b) vid2 r) vid3 ra))"
   hence constraint:"\<forall>ra. (0 \<le> ra \<and> ra \<le> r) \<longrightarrow> 
          (repv (repv (a, b) vid2 r) vid3 ra) 
        \<in> fml_sem I (Prop vid2 (singleton (Plus (Var vid1) (Times (f0 fid1) (Var vid3)))))"
       using leq by auto
  assume aaba:" (aa, ba) =
     repv (repv (a, b) vid2 r) vid1
      (dterm_sem I (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid2))) (repv (a, b) vid2 r))"
  let ?abba = "repv (repd (a, b) vid1 (Functions I fid1 (\<chi> i. 0))) vid1
      (dterm_sem I (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid2))) (repv (a, b) vid2 r))"
  from allW have thisW:"(\<exists>\<nu> sol t.
             ((a, b), ?abba) = (\<nu>, mk_v I (OSing vid1 (f0 fid1)) \<nu> (sol t)) \<and>
             0 \<le> t \<and>
             (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..t}
              {x. mk_v I (OSing vid1 (f0 fid1)) \<nu> x \<in> fml_sem I (p1 vid2 vid1)} \<and>
             sol 0 = fst \<nu>) \<longrightarrow>
         ?abba \<in> fml_sem I (p1 vid3 vid1)" by blast
  let ?c = "Functions I fid1 (\<chi> _. 0)"
  let ?sol = "(\<lambda>t. \<chi> i. if i = vid1 then (a $ i) + ?c * t else (a $ i))"
  have 
  agrees:"Vagree (mk_v I (OSing vid1 (f0 fid1)) (a, b) (?sol r)) (a, b) (- ODE_vars (OSing vid1 (f0 fid1))) 
  \<and> Vagree (mk_v I (OSing vid1 (f0 fid1)) (a, b) (?sol r))
   (mk_xode I (OSing vid1 (f0 fid1)) (?sol r)) (ODE_vars (OSing vid1 (f0 fid1)))" 
    using mk_v_agree[of "I" "(OSing vid1 (f0 fid1))" "(a,b)" "(?sol r)"] by auto
  
  have prereq1a:"fst ?abba
  = fst (mk_v I (OSing vid1 (f0 fid1)) (a,b) (?sol r))"
    using  agrees aaba 
    apply (auto simp add: aaba Vagree_def)
    apply (rule vec_extensionality)
    subgoal for i
      apply (cases "i = vid1")
      using vne12 agrees Vagree_def  apply (auto simp add: aaba f0_def empty_def )
      done
    apply (rule vec_extensionality)
      subgoal for i
        apply (cases "i = vid1")
        apply(auto  simp add: f0_def empty_def)
      done
    done
  have prereq1b:"snd (?abba) = snd (mk_v I (OSing vid1 (f0 fid1)) (a,b) (?sol r))"
    using  agrees aaba 
    apply (auto simp add: aaba Vagree_def)
    apply (rule vec_extensionality)
    subgoal for i
      apply (cases "i = vid1")
      using vne12 agrees Vagree_def  apply (auto simp add: aaba f0_def empty_def )
      done
    done
  
  have "?abba = mk_v I (OSing vid1 (f0 fid1)) (a,b) (?sol r)"
    using prod_eq_iff prereq1a prereq1b by blast
  hence req1:"((a, b), ?abba) = ((a, b), mk_v I (OSing vid1 (f0 fid1)) (a,b) (?sol r))" by auto
  have "sterm_sem I ($f fid1 (\<lambda>i. Const 0)) b = Functions I fid1 (\<chi> i. 0)" by auto
  hence vec_simp:"(\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I ($f fid1 (\<lambda>i. Const 0)) b else 0) 
      = (\<lambda>a b. \<chi> i. if i = vid1 then Functions I fid1 (\<chi> i. 0) else 0)"
    by (auto simp add: vec_eq_iff cong: if_cong)
    (* TODO: have a solution that exists everywhere, want to restrict the domain. Fabian says this
       should be true but has not been formalized just yet. *)
    interpret ll:ll_on_open_it "{0 .. r}" "(\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))" "{x. mk_v I (OSing vid1 (f0 fid1)) (a,b) x \<in> fml_sem I (p1 vid2 vid1)}"
    apply(standard)
    apply(auto)
    sorry
    (* Combine with flow_usolves_ode and equals_flowI to get uniqueness of solution *)
    have req3:"(?sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..r}
              {x. mk_v I (OSing vid1 (f0 fid1)) (a,b) x \<in> fml_sem I (p1 vid2 vid1)}" 
    apply(auto simp add: f0_def empty_def vec_simp) 
    apply(rule solves_odeI)
    apply(auto simp only: has_vderiv_on_def has_vector_derivative_def)
    apply (rule has_derivative_vec[THEN has_derivative_eq_rhs])
    defer
    apply (rule ext)
    apply (subst scaleR_vec_def)
    apply (rule refl)
    apply (auto intro!: derivative_eq_intros)
    (* Domain constraint satisfied*)
    using constraint apply (auto)
    subgoal for t
      apply(erule allE[where x="t"])
      apply(auto simp add: p1_def)
    proof -
      have eq:"(\<chi> i. dterm_sem I (if i = vid1 then Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3)) else Const 0)
            (\<chi> y. if vid3 = y then t else fst (\<chi> y. if vid2 = y then r else fst (a, b) $ y, b) $ y, b)) =
            (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
              (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. Const 0))) (a, b)
                (\<chi> i. if i = vid1 then a $ i + Functions I fid1 (\<chi> _. 0) * t else a $ i)))"
        using vne12 vne13 mk_v_agree[of "I" "(OSing vid1 ($f fid1 (\<lambda>i. Const 0)))" "(a, b)" "(\<chi> i. if i = vid1 then a $ i + Functions I fid1 (\<chi> _. 0) * t else a $ i)"]
        by (auto simp add: vec_eq_iff f0_def empty_def Vagree_def)
      show "0 \<le> t \<Longrightarrow>
    t \<le> r \<Longrightarrow>
    Predicates I vid2
     (\<chi> i. dterm_sem I (if i = vid1 then Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3)) else Const 0)
            (\<chi> y. if vid3 = y then t else fst (\<chi> y. if vid2 = y then r else fst (a, b) $ y, b) $ y, b)) \<Longrightarrow>
    Predicates I vid2
     (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
            (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. Const 0))) (a, b)
              (\<chi> i. if i = vid1 then a $ i + Functions I fid1 (\<chi> _. 0) * t else a $ i)))" using eq by auto
    qed
    done
      
  have req4:"?sol 0 = fst (a,b)" by (auto simp: vec_eq_iff)
  have inPred:"?abba \<in> fml_sem I (p1 vid3 vid1)"
    using \<open>(\<exists>\<nu> sol t. ((a, b), ?abba) = (\<nu>, mk_v I (OSing vid1 (f0 fid1)) \<nu> (sol t)) \<and> 0 \<le> t \<and> (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..t} {x. mk_v I (OSing vid1 (f0 fid1)) \<nu> x \<in> fml_sem I (p1 vid2 vid1)} \<and> sol 0 = fst \<nu>) \<longrightarrow> ?abba \<in> fml_sem I (p1 vid3 vid1)\<close>
    using req1 leq req3 req4 thisW by fastforce
  have sem_eq:"?abba \<in> fml_sem I (p1 vid3 vid1) \<longleftrightarrow> (aa,ba) \<in> fml_sem I (p1 vid3 vid1)"
    apply(rule coincidence_formula)
    by (auto simp add: aaba Vagree_def p1_def f0_def empty_def)
  from inPred sem_eq have  inPred':"(aa,ba) \<in> fml_sem I (p1 vid3 vid1)"
    by auto
  (* thus by lemma 6 consequence for formulas *)
  show "repv (repv (a, b) vid2 r) vid1
       (dterm_sem I (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid2))) (repv (a, b) vid2 r))
       \<in> fml_sem I (p1 vid3 vid1)" using aaba inPred' by auto
next
  fix I::"('sf,'sc,'sz) interp"
  and aa ba ab bb sol 
  and t:: real
  assume good_interp:"is_interp I"
  assume all:"
       \<forall>r. dterm_sem I (Const 0) (repv (ab, bb) vid2 r) \<le> dterm_sem I (trm.Var vid2) (repv (ab, bb) vid2 r) \<longrightarrow>
           (\<forall>ra. repv (repv (ab, bb) vid2 r) vid3 ra
                 \<in> {v. dterm_sem I (Const 0) v \<le> dterm_sem I (trm.Var vid3) v} \<inter>
                    {v. dterm_sem I (trm.Var vid3) v \<le> dterm_sem I (trm.Var vid2) v} \<longrightarrow>
                 Predicates I vid2
                  (\<chi> i. dterm_sem I (singleton (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3))) i)
                         (repv (repv (ab, bb) vid2 r) vid3 ra))) \<longrightarrow>
           (\<forall>\<omega>. \<omega> = repv (repv (ab, bb) vid2 r) vid1
                      (dterm_sem I (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid2))) (repv (ab, bb) vid2 r)) \<longrightarrow>
                 \<omega> \<in> fml_sem I (p1 vid3 vid1))"
  assume t:"0 \<le> t"
  assume aaba:"(aa, ba) = mk_v I (OSing vid1 (f0 fid1)) (ab, bb) (sol t)"
  assume sol:"(sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..t}
        {x. mk_v I (OSing vid1 (f0 fid1)) (ab, bb) x \<in> fml_sem I (p1 vid2 vid1)}"
  hence constraint:"\<And>s. s \<in> {0 .. t} \<Longrightarrow> sol t \<in> {x. mk_v I (OSing vid1 (f0 fid1)) (ab, bb) x \<in> fml_sem I (p1 vid2 vid1)}"
    using solves_ode_domainD by fastforce
  assume sol0:"sol 0 = fst (ab, bb)"
  have impl:"dterm_sem I (Const 0) (repv (ab, bb) vid2 t) \<le> dterm_sem I (trm.Var vid2) (repv (ab, bb) vid2 t) \<longrightarrow>
           (\<forall>ra. repv (repv (ab, bb) vid2 t) vid3 ra
                 \<in> {v. dterm_sem I (Const 0) v \<le> dterm_sem I (trm.Var vid3) v} \<inter>
                    {v. dterm_sem I (trm.Var vid3) v \<le> dterm_sem I (trm.Var vid2) v} \<longrightarrow>
                 Predicates I vid2
                  (\<chi> i. dterm_sem I (singleton (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3))) i)
                         (repv (repv (ab, bb) vid2 t) vid3 ra))) \<longrightarrow>
           (\<forall>\<omega>. \<omega> = repv (repv (ab, bb) vid2 t) vid1
                      (dterm_sem I (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid2))) (repv (ab, bb) vid2 t)) \<longrightarrow>
                 \<omega> \<in> fml_sem I (p1 vid3 vid1))" using all by auto
    have another_eq:"\<And>i ra. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                  (mk_v I (OSing vid1 (f0 fid1)) (ab, bb) (sol t))

          =  dterm_sem I (if i = vid1 then Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3)) else Const 0)
                  (\<chi> y. if vid3 = y then ra else fst (\<chi> y. if vid2 = y then t else fst (ab, bb) $ y, bb) $ y, bb)"
      using mk_v_agree[of "I" "(OSing vid1 (f0 fid1))" "(ab, bb)" "(sol t)"]  vne12 vne23 vne13
      apply(auto simp add: f0_def p1_def empty_def)
      apply(unfold Vagree_def)
      using aaba apply(simp add: f0_def empty_def)
      (* TODO: Think this needs uniqueness of solutions *)
      
    have allRa:"(\<forall>ra. repv (repv (ab, bb) vid2 t) vid3 ra
                 \<in> {v. dterm_sem I (Const 0) v \<le> dterm_sem I (trm.Var vid3) v} \<inter>
                    {v. dterm_sem I (trm.Var vid3) v \<le> dterm_sem I (trm.Var vid2) v} \<longrightarrow>
                 Predicates I vid2
                  (\<chi> i. dterm_sem I (singleton (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3))) i)
                         (repv (repv (ab, bb) vid2 t) vid3 ra)))"
      using mk_v_agree[of "I" "(OSing vid1 (f0 fid1))" "(ab, bb)" "(sol t)"]
           vne23 constraint[of t] apply(auto simp add: Vagree_def p1_def)
      (*
      *)
      
  show "mk_v I (OSing vid1 (f0 fid1)) (ab, bb) (sol t) \<in> fml_sem I (p1 vid3 vid1)" sorry
qed 
oops

(* TODO:  differential formula semantics actually bogus right now
 * I believe the only correct semantics to give a DiffFormula(Predicational P)
 * is THE x. DI_is_valid_for (x). So the validity of this axiom will be a trivial
 * appeal to the validity of the interpretation. But then in substitution we will do the
 * real work by showing that adjoints are valid interpretations, so in adjoints all of the
 * DI_is_valid_for(x)'s actually exist.
*)
lemma DI_valid:"valid DIaxiom"
  apply(unfold DIaxiom_def valid_def impl_sem iff_sem)
  done

lemma DG_valid:"valid DGaxiom"
  apply(auto simp add: DGaxiom_def valid_def Let_def)
  done

oops

section Substitution

definition NTUadmit :: "('d \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a + 'd, 'c) trm \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "NTUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i. FVT (\<sigma> i)) \<inter> U) = {}"

inductive NTadmit :: "('d \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a + 'd, 'c) trm \<Rightarrow> bool"
where 
  NTadmit_Diff:"NTadmit \<sigma> \<theta> \<Longrightarrow> NTUadmit \<sigma> \<theta> UNIV \<Longrightarrow> NTadmit \<sigma> (Differential \<theta>)"
| NTadmit_Fun:"(\<And>i. NTadmit \<sigma> (args i)) \<Longrightarrow> NTadmit \<sigma> (Function f args)"
| NTadmit_Plus:"NTadmit \<sigma> \<theta>1 \<Longrightarrow> NTadmit \<sigma> \<theta>2 \<Longrightarrow> NTadmit \<sigma> (Plus \<theta>1 \<theta>2)"
| NTadmit_Times:"NTadmit \<sigma> \<theta>1 \<Longrightarrow> NTadmit \<sigma> \<theta>2 \<Longrightarrow> NTadmit \<sigma> (Times \<theta>1 \<theta>2)"
| NTadmit_DiffVar:"NTadmit \<sigma> (DiffVar x)"
| NTadmit_Var:"NTadmit \<sigma> (Var x)"
| NTadmit_Const:"NTadmit \<sigma> (Const r)"

primrec NTsubst::"('a + 'b, 'c) trm \<Rightarrow> ('b \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a, 'c) trm"
where
  "NTsubst (Var v) \<sigma> = Var v"
| "NTsubst (DiffVar v) \<sigma> = DiffVar v"
| "NTsubst (Const r) \<sigma> = Const r"  
| "NTsubst (Function f args) \<sigma> = 
    (case f of Inl f' \<Rightarrow> Function f' (\<lambda>i. NTsubst (args i) \<sigma>) | Inr f' \<Rightarrow> \<sigma> f')"  
| "NTsubst (Plus \<theta>1 \<theta>2) \<sigma> = Plus (NTsubst \<theta>1 \<sigma>) (NTsubst \<theta>2 \<sigma>)"  
| "NTsubst (Times \<theta>1 \<theta>2) \<sigma> = Times (NTsubst \<theta>1 \<sigma>) (NTsubst \<theta>2 \<sigma>)"  
| "NTsubst (Differential \<theta>) \<sigma> = Differential (NTsubst \<theta> \<sigma>)"

primrec Tsubst::"('sf, 'sz) trm \<Rightarrow> ('sf, 'sc, 'sz) subst \<Rightarrow> ('sf, 'sz) trm"
where
  "Tsubst (Var x) \<sigma> = Var x"
| "Tsubst (DiffVar x) \<sigma> = DiffVar x"  
| "Tsubst (Const r) \<sigma> = Const r"  
| "Tsubst (Function f args) \<sigma> = (case SFunctions \<sigma> f of Some f' \<Rightarrow> NTsubst f' | None \<Rightarrow> Function f) (\<lambda> i. Tsubst (args i) \<sigma>)"  
| "Tsubst (Plus \<theta>1 \<theta>2) \<sigma> = Plus (Tsubst \<theta>1 \<sigma>) (Tsubst \<theta>2 \<sigma>)"  
| "Tsubst (Times \<theta>1 \<theta>2) \<sigma> = Times (Tsubst \<theta>1 \<sigma>) (Tsubst \<theta>2 \<sigma>)"  
| "Tsubst (Differential \<theta>) \<sigma> = Differential (Tsubst \<theta> \<sigma>)"

primrec NOsubst::"('a + 'b, 'c) ODE \<Rightarrow> ('b \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a, 'c) ODE"
where
  "NOsubst (OVar c) \<sigma> = OVar c"
| "NOsubst (OSing x \<theta>) \<sigma> = OSing x (NTsubst \<theta> \<sigma>)"
| "NOsubst (OProd ODE1 ODE2) \<sigma> = OProd (NOsubst ODE1 \<sigma>) (NOsubst ODE2 \<sigma>)"

primrec Osubst::"('sf, 'sz) ODE \<Rightarrow> ('sf, 'sc, 'sz) subst \<Rightarrow> ('sf, 'sz) ODE"
where
  "Osubst (OVar c) \<sigma> = (case SODEs \<sigma> c of Some c' \<Rightarrow> c' | None \<Rightarrow> OVar c)"
| "Osubst (OSing x \<theta>) \<sigma> = OSing x (Tsubst \<theta> \<sigma>)"
| "Osubst (OProd ODE1 ODE2) \<sigma> = OProd (Osubst ODE1 \<sigma>) (Osubst ODE2 \<sigma>)"

fun NPsubst::"('a + 'd, 'b, 'c) hp \<Rightarrow> ('d \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a, 'b, 'c) hp"
and NFsubst::"('a + 'd, 'b, 'c) formula \<Rightarrow> ('d \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a, 'b, 'c) formula"
where
  "NPsubst (Pvar a) \<sigma> = Pvar a"
| "NPsubst (Assign x \<theta>) \<sigma> = Assign x (NTsubst \<theta> \<sigma>)"
| "NPsubst (DiffAssign x \<theta>) \<sigma> = DiffAssign x (NTsubst \<theta> \<sigma>)"
| "NPsubst (Test \<phi>) \<sigma> = Test (NFsubst \<phi> \<sigma>)"
| "NPsubst (EvolveODE ODE \<phi>) \<sigma> = EvolveODE (NOsubst ODE \<sigma>) (NFsubst \<phi> \<sigma>)"
| "NPsubst (Choice \<alpha> \<beta>) \<sigma> = Choice (NPsubst \<alpha> \<sigma>) (NPsubst \<beta> \<sigma>)"
| "NPsubst (Sequence \<alpha> \<beta>) \<sigma> = Sequence (NPsubst \<alpha> \<sigma>) (NPsubst \<beta> \<sigma>)"
| "NPsubst (Loop \<alpha>) \<sigma> = Loop (NPsubst \<alpha> \<sigma>)"

| "NFsubst (Geq \<theta>1 \<theta>2) \<sigma> = Geq (NTsubst \<theta>1 \<sigma>) (NTsubst \<theta>2 \<sigma>)"
| "NFsubst (Prop p args) \<sigma> = Prop p (\<lambda>i. NTsubst (args i) \<sigma>)"
| "NFsubst (Not \<phi>) \<sigma> = Not (NFsubst \<phi> \<sigma>)"
| "NFsubst (And \<phi> \<psi>) \<sigma> = And (NFsubst \<phi> \<sigma>) (NFsubst \<psi> \<sigma>)"
| "NFsubst (Forall x \<phi>) \<sigma> = Forall x (NFsubst \<phi> \<sigma>)"
| "NFsubst (Box \<alpha> \<phi>) \<sigma> = Box (NPsubst \<alpha> \<sigma>) (NFsubst \<phi> \<sigma>)"
| "NFsubst (DiffFormula \<phi>) \<sigma> = DiffFormula (NFsubst \<phi> \<sigma>)"
| "NFsubst (InContext C \<phi>) \<sigma> = InContext C (NFsubst \<phi> \<sigma>)"
  
fun PPsubst::"('a, 'b + 'd, 'c) hp \<Rightarrow> ('d \<Rightarrow> ('a, 'b, 'c) formula) \<Rightarrow> ('a, 'b, 'c) hp"
and PFsubst::"('a, 'b + 'd, 'c) formula \<Rightarrow> ('d \<Rightarrow> ('a, 'b, 'c) formula) \<Rightarrow> ('a, 'b, 'c) formula"
where
  "PPsubst (Pvar a) \<sigma> = Pvar a"
| "PPsubst (Assign x \<theta>) \<sigma> = Assign x \<theta>"
| "PPsubst (DiffAssign x \<theta>) \<sigma> = DiffAssign x \<theta>"
| "PPsubst (Test \<phi>) \<sigma> = Test (PFsubst \<phi> \<sigma>)"
| "PPsubst (EvolveODE ODE \<phi>) \<sigma> = EvolveODE ODE (PFsubst \<phi> \<sigma>)"
| "PPsubst (Choice \<alpha> \<beta>) \<sigma> = Choice (PPsubst \<alpha> \<sigma>) (PPsubst \<beta> \<sigma>)"
| "PPsubst (Sequence \<alpha> \<beta>) \<sigma> = Sequence (PPsubst \<alpha> \<sigma>) (PPsubst \<beta> \<sigma>)"
| "PPsubst (Loop \<alpha>) \<sigma> = Loop (PPsubst \<alpha> \<sigma>)"

| "PFsubst (Geq \<theta>1 \<theta>2) \<sigma> = (Geq \<theta>1 \<theta>2)"
| "PFsubst (Prop p args) \<sigma> = Prop p args"
| "PFsubst (Not \<phi>) \<sigma> = Not (PFsubst \<phi> \<sigma>)"
| "PFsubst (And \<phi> \<psi>) \<sigma> = And (PFsubst \<phi> \<sigma>) (PFsubst \<psi> \<sigma>)"
| "PFsubst (Forall x \<phi>) \<sigma> = Forall x (PFsubst \<phi> \<sigma>)"
| "PFsubst (Box \<alpha> \<phi>) \<sigma> = Box (PPsubst \<alpha> \<sigma>) (PFsubst \<phi> \<sigma>)"
| "PFsubst (DiffFormula \<phi>) \<sigma> = DiffFormula (PFsubst \<phi> \<sigma>)"
| "PFsubst (InContext C \<phi>) \<sigma> = (case C of Inl C' \<Rightarrow> InContext C' (PFsubst \<phi> \<sigma>) | Inr p' \<Rightarrow> \<sigma> p')"

  
fun Psubst::"('sf, 'sc, 'sz) hp \<Rightarrow> ('sf, 'sc, 'sz) subst \<Rightarrow> ('sf, 'sc, 'sz) hp"
and Fsubst::"('sf, 'sc, 'sz) formula \<Rightarrow> ('sf, 'sc, 'sz) subst \<Rightarrow> ('sf, 'sc, 'sz) formula"
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
| "Fsubst (Prop p args) \<sigma> = (case SPredicates \<sigma> p of Some p' \<Rightarrow> NFsubst p' (\<lambda>i. Tsubst (args i) \<sigma>) | None \<Rightarrow> Prop p (\<lambda>i. Tsubst (args i) \<sigma>))"
| "Fsubst (Not \<phi>) \<sigma> = Not (Fsubst \<phi> \<sigma>)"
| "Fsubst (And \<phi> \<psi>) \<sigma> = And (Fsubst \<phi> \<sigma>) (Fsubst \<psi> \<sigma>)"
| "Fsubst (Forall x \<phi>) \<sigma> = Forall x (Fsubst \<phi> \<sigma>)"
| "Fsubst (Box \<alpha> \<phi>) \<sigma> = Box (Psubst \<alpha> \<sigma>) (Fsubst \<phi> \<sigma>)"
| "Fsubst (DiffFormula \<phi>) \<sigma> = DiffFormula (Fsubst \<phi> \<sigma>)"
| "Fsubst (InContext C \<phi>) \<sigma> = (case SContexts \<sigma> C of Some C' \<Rightarrow> PFsubst C' (\<lambda>(). (Fsubst \<phi> \<sigma>)) | None \<Rightarrow>  InContext C (Fsubst \<phi> \<sigma>))"

definition FVA :: "('a \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('c + 'c) set"
where "FVA args = (\<Union> i. FVT (args i))"

fun SFV :: "('a, 'b, 'c) subst \<Rightarrow> ('a + 'b + 'c) \<Rightarrow> ('c + 'c) set"
where "SFV \<sigma> (Inl i) = (case SFunctions \<sigma> i of Some f' \<Rightarrow> FVT f' | None \<Rightarrow> {})"
| "SFV \<sigma> (Inr (Inl i)) = (case SContexts \<sigma> i of Some C' \<Rightarrow> FVF C' | None \<Rightarrow> {})"
| "SFV \<sigma> (Inr (Inr i)) = (case SPredicates \<sigma> i of Some p' \<Rightarrow> FVF p' | None \<Rightarrow> {})"

definition FVS :: "('a, 'b, 'c) subst \<Rightarrow> ('c + 'c) set"
where "FVS \<sigma> = (\<Union>i. SFV \<sigma> i)"

definition SDom :: "('a, 'b, 'c) subst \<Rightarrow> ('a + 'b + 'c) set"
where "SDom \<sigma> = 
 {Inl x | x. x \<in> dom (SFunctions \<sigma>)}
 \<union> {Inr (Inl x) | x. x \<in> dom (SContexts \<sigma>)}
 \<union> {Inr (Inr x) | x. x \<in> dom (SPredicates \<sigma>)} 
 \<union> {Inr (Inr x) | x. x \<in> dom (SPrograms \<sigma>)}"

definition TUadmit :: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'c) trm \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "TUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> SIGT \<theta>. (case SFunctions \<sigma> i of Some f' \<Rightarrow> FVT f')) \<inter> U) = {}"

inductive Tadmit :: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'c) trm \<Rightarrow> bool"
where 
  Tadmit_Diff:"Tadmit \<sigma> \<theta> \<Longrightarrow> TUadmit \<sigma> \<theta> UNIV \<Longrightarrow> Tadmit \<sigma> (Differential \<theta>)"
| Tadmit_Fun:"(\<And>i. Tadmit \<sigma> (args i)) \<Longrightarrow> Tadmit \<sigma> (Function f args)"
| Tadmit_Plus:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Tadmit \<sigma> (Plus \<theta>1 \<theta>2)"
| Tadmit_Times:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Tadmit \<sigma> (Times \<theta>1 \<theta>2)"
| Tadmit_DiffVar:"Tadmit \<sigma> (DiffVar x)"
| Tadmit_Var:"Tadmit \<sigma> (Var x)"
| Tadmit_Const:"Tadmit \<sigma> (Const r)"

inductive OUadmit:: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'c) ODE \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where 
  "OUadmit \<sigma> (OVar c) U"
| "TUadmit \<sigma> \<theta> U \<Longrightarrow> OUadmit \<sigma> (OSing x \<theta>) U"
| "OUadmit \<sigma> ODE1 U \<Longrightarrow> OUadmit \<sigma> ODE2 U \<Longrightarrow> OUadmit \<sigma> (OProd ODE1 ODE2) U"

  
definition PUadmit :: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'b, 'c) hp \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "PUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> (SDom \<sigma> \<inter> SIGP \<theta>).  SFV \<sigma> i) \<inter> U) = {}"

definition FUadmit :: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "FUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> (SDom \<sigma> \<inter> SIGF \<theta>).  SFV \<sigma> i) \<inter> U) = {}"
 
inductive Padmit:: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'b, 'c) hp \<Rightarrow> bool"
and Fadmit:: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> bool"
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
| "Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> {Inl x} \<Longrightarrow> Fadmit \<sigma> (Forall x \<phi>)"
| "Fadmit \<sigma> \<phi> \<Longrightarrow> Padmit \<sigma> a \<Longrightarrow> FUadmit \<sigma> \<phi> (BVP a) \<Longrightarrow> Fadmit \<sigma> (Box a \<phi>)"
| "Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> UNIV \<Longrightarrow> Fadmit \<sigma> (InContext C \<phi>)"
  
fun extendf :: "('sf, 'sc, 'sz) interp \<Rightarrow> 'sz Rvec \<Rightarrow> ('sf + 'sz, 'sc, 'sz) interp"
where "extendf I R =
\<lparr>Functions = (\<lambda>f. case f of Inl f' \<Rightarrow> Functions I f' | Inr f' \<Rightarrow> (\<lambda>_. R $ f')),
 Predicates = Predicates I,
 Contexts = Contexts I,
 Programs = Programs I,
 ODEs = ODEs I\<rparr>"

fun extendc :: "('sf, 'sc, 'sz) interp \<Rightarrow> 'sz state set \<Rightarrow> ('sf, 'sc + unit, 'sz) interp"
where "extendc I R =
\<lparr>Functions =  Functions I,
 Predicates = Predicates I,
 Contexts = (\<lambda>C. case C of Inl C' \<Rightarrow> Contexts I C' | Inr () \<Rightarrow> (\<lambda>_.  R)),
 Programs = Programs I,
 ODEs = ODEs I\<rparr>"

definition adjoint :: "('sf, 'sc, 'sz) interp \<Rightarrow> ('sf, 'sc, 'sz) subst \<Rightarrow> 'sz state \<Rightarrow> ('sf, 'sc, 'sz) interp" 
where "adjoint I \<sigma> \<nu> =
\<lparr>Functions =   (\<lambda>f. case SFunctions \<sigma> f of Some f' \<Rightarrow> (\<lambda>R. dterm_sem (extendf I R) f' \<nu>) | None \<Rightarrow> Functions I f),
 Predicates = (\<lambda>p. case SPredicates \<sigma> p of Some p' \<Rightarrow> (\<lambda>R. \<nu> \<in>fml_sem (extendf I R) p') | None \<Rightarrow> Predicates I p),
 Contexts =   (\<lambda>c. case SContexts \<sigma> c of Some c' \<Rightarrow> (\<lambda>R. fml_sem (extendc I R) c') | None \<Rightarrow> Contexts I c),
 Programs =   (\<lambda>a. case SPrograms \<sigma> a of Some a' \<Rightarrow> prog_sem I a' | None \<Rightarrow> Programs I a),
 ODEs =     (\<lambda>ode. case SODEs \<sigma> ode of Some ode' \<Rightarrow> ODE_sem I ode' | None \<Rightarrow> ODEs I ode)\<rparr>"

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

definition NTadjoint::"('sf, 'sc, 'sz) interp \<Rightarrow> ('d::finite \<Rightarrow> ('sf, 'sz) trm) \<Rightarrow> 'sz state \<Rightarrow> ('sf + 'd, 'sc, 'sz) interp" 
where "NTadjoint I \<sigma> \<nu> =
\<lparr>Functions =   (\<lambda>f. case f of Inl f' \<Rightarrow> Functions I f' | Inr f' \<Rightarrow> (\<lambda>R. dterm_sem I (\<sigma> f') \<nu>)),
 Predicates = Predicates I,
 Contexts = Contexts I,
 Programs = Programs I,
 ODEs = ODEs I\<rparr>"

lemma dsem_to_ssem:"dfree \<theta> \<Longrightarrow> dterm_sem I \<theta> \<nu> = sterm_sem I \<theta> (fst \<nu>)"
  by (induct rule: dfree.induct) (auto)

(* TODO: simplify*)
lemma adjoint_free:
  assumes sfree:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
  shows "adjoint I \<sigma> \<nu> =
  \<lparr>Functions =  (\<lambda>f. case SFunctions \<sigma> f of Some f' \<Rightarrow> (\<lambda>R. sterm_sem (extendf I R) f' (fst \<nu>)) | None \<Rightarrow> Functions I f),
   Predicates = (\<lambda>p. case SPredicates \<sigma> p of Some p' \<Rightarrow> (\<lambda>R. \<nu> \<in> fml_sem (extendf I R) p') | None \<Rightarrow> Predicates I p),
   Contexts =   (\<lambda>c. case SContexts \<sigma> c of Some c' \<Rightarrow> (\<lambda>R. fml_sem (extendc I R) c') | None \<Rightarrow> Contexts I c),
   Programs =   (\<lambda>a. case SPrograms \<sigma> a of Some a' \<Rightarrow> prog_sem I a' | None \<Rightarrow> Programs I a),
   ODEs =     (\<lambda>ode. case SODEs \<sigma> ode of Some ode' \<Rightarrow> ODE_sem I ode' | None \<Rightarrow> ODEs I ode)\<rparr>"
  using dsem_to_ssem[OF sfree] 
  by (cases \<nu>) (auto simp add: adjoint_def fun_eq_iff split: option.split)


lemma NTadjoint_free:"(\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (NTadjoint I \<sigma> \<nu> =
\<lparr>Functions =   (\<lambda>f. case f of Inl f' \<Rightarrow> Functions I f' | Inr f' \<Rightarrow> (\<lambda>R. sterm_sem I (\<sigma> f') (fst \<nu>))),
 Predicates = Predicates I,
 Contexts = Contexts I,
 Programs = Programs I,
 ODEs = ODEs I\<rparr>)" 
  by (auto simp add: dsem_to_ssem NTadjoint_def)

lemma nsubst_sterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
shows "dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> sterm_sem I (NTsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induction rule: dfree.induct)
  case (dfree_Fun args f) then
    show "?case" 
      by(cases "f") (auto simp add:  NTadjoint_free)
qed (auto)
(*
lemma sterm_determines_frechet:
assumes good_interp1:"is_interp I"
assumes good_interp2:"is_interp J"
assumes free1:"dfree (\<theta>1::('a::finite, 'c) trm)"
assumes free2:"dfree (\<theta>2::('a::finite, 'c::finite) trm)"
assumes sem:"sterm_sem I \<theta>1 (fst \<nu>) = sterm_sem J \<theta>2 (fst \<nu>)"
shows "frechet I \<theta>1 (fst \<nu>) (snd \<nu>) = frechet J \<theta>2 (fst \<nu>) (snd \<nu>)"
proof -
  (*   Deriv.has_derivative_unique: (?f has_derivative ?F) (at ?x) \<Longrightarrow> (?f has_derivative ?F') (at ?x) \<Longrightarrow> ?F = ?F'*)
  let ?v = "(fst \<nu>)"
  have d1:"(sterm_sem I \<theta>1 has_derivative frechet I \<theta>1 ?v) (at ?v)" 
    sorry(*     by (auto simp add: frechet_correctness good_interp1 free1)*)
  have "(sterm_sem I \<theta>2 has_derivative frechet I \<theta>2 ?v) (at ?v)" 
    sorry (*by (auto simp add: frechet_correctness good_interp2 free2)*)
  hence d2:"(sterm_sem I \<theta>1 has_derivative frechet I \<theta>2 ?v) (at ?v)"   
    using sem by (auto intro: derivative_eq_intros)
  thus "?thesis" using has_derivative_unique d1 by auto
qed
*)

lemma nsubst_frechet:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"
shows "dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> frechet I (NTsubst \<theta> \<sigma>) (fst \<nu>) = frechet (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induct rule: dfree.induct)    
  case (dfree_Fun args f) then
  show "?case" 
     sorry (*by(cases "f") (auto simp add:  NTadjoint_free nsubst_sterm good_interp )*)
qed (auto  simp add: nsubst_sterm)
    
lemma nsubst_dterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"    
shows "NTadmit \<sigma> \<theta> \<Longrightarrow> dsafe \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dterm_sem I (NTsubst \<theta> \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> \<nu>"
proof (induction rule: NTadmit.induct)
  case (NTadmit_Fun \<sigma> args f) 
    thus "?case" by (cases "f") (auto simp add: vec_extensionality  NTadjoint_def)
next
    case (NTadmit_Diff \<sigma> \<theta>) 
    hence admit:"NTadmit \<sigma> \<theta>"
      and admitU:"NTUadmit \<sigma> \<theta> UNIV"
      and IH : "dsafe \<theta> \<Longrightarrow>
            (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dterm_sem I (NTsubst \<theta> \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> \<nu>"
      and safe: "dsafe (Differential \<theta>)" 
      and freeSub:"\<And>i. dfree (\<sigma> i)"
      by auto
    have free:"dfree \<theta>" using safe by auto
    have sem:"sterm_sem I (NTsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
      using nsubst_sterm[OF free freeSub] by auto
    then show "dterm_sem I (NTsubst (Differential \<theta>) \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) (Differential \<theta>) \<nu>"
      by (auto simp add: directional_derivative_def frechet_correctness nsubst_frechet[OF good_interp free freeSub])
qed (auto simp add: NTadmit.cases)

lemma ntsubst_preserves_free:
"dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dfree(NTsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case"
    by (cases "i") (auto intro:dfree.intros)
qed (auto intro: dfree.intros)

lemma ntsubst_free_to_safe:
"dfree \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dsafe (NTsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case"
    by (cases "i") (auto intro:dsafe.intros ntsubst_preserves_free)
qed (auto intro: dsafe.intros)

lemma ntsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dsafe (NTsubst \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Fun args i) then show "?case"
    by (cases "i") (auto intro:dsafe.intros ntsubst_preserves_free dfree_is_dsafe)
next
  case (dsafe_Diff \<theta>) then show "?case"
    by  (auto intro:dsafe.intros ntsubst_preserves_free)
qed (auto simp add: ntsubst_preserves_free intro: dsafe.intros)

lemma tsubst_preserves_free:
"dfree \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dfree(Tsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case" 
    by (cases "SFunctions \<sigma> i") (auto intro:dfree.intros ntsubst_preserves_free)
qed (auto intro: dfree.intros)

lemma tsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dsafe(Tsubst \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Fun args i) then show "?case" 
    sorry 
    (* by (cases "SFunctions \<sigma> i") (auto intro:dsafe.intros ntsubst_preserves_safe tsubst_preserves_free dfree_is_dsafe)*)
qed (auto intro: dsafe.intros tsubst_preserves_free)

lemma subst_sterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
shows "
  dfree \<theta> \<Longrightarrow>
  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> 
   sterm_sem I (Tsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induction rule: dfree.induct)
  case (dfree_Fun args f) 
    note frees = dfree_Fun.hyps(1) and sfree = dfree_Fun.prems(1)
    have IH:"(\<And>i. dfree (args i) \<Longrightarrow>
        sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>))" 
      using  dfree_Fun.prems dfree_Fun.IH by auto
    have eqs:"\<And>i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)"
      by (auto simp add: IH frees)
    show "?case" 
    proof (cases "SFunctions \<sigma> f")
      fix f'
      assume some:"SFunctions \<sigma> f = Some f'" 
      let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
      have subFree:"(\<And>i. dfree (?sub i))" using tsubst_preserves_free[OF frees sfree] by simp
      have IH2:"sterm_sem I (NTsubst f' ?sub) (fst \<nu>) = sterm_sem (NTadjoint I ?sub \<nu>) f' (fst \<nu>)"
        using frees subFree sfree[OF some] by (simp add: nsubst_sterm)
      show "?thesis" 
        using IH frees by (auto simp add: eqs adjoint_free[OF sfree] IH2 NTadjoint_free[OF subFree] some)
    qed (auto simp add: IH adjoint_def vec_extensionality frees)
  qed auto

lemma subst_dterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"
shows "
  Tadmit \<sigma> \<theta> \<Longrightarrow>
  dsafe \<theta> \<Longrightarrow>
  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> 
   dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) \<theta> \<nu>"
proof (induction rule: Tadmit.induct)
  case (Tadmit_Fun \<sigma> args f) 
    note safe = Tadmit_Fun.prems(1) and sfree = Tadmit_Fun.prems(2)
    hence safes:"\<And>i. dsafe (args i)" by auto
    have IH:"(\<And>i. dsafe (args i) \<Longrightarrow>
        dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
      using  Tadmit_Fun.prems Tadmit_Fun.IH by auto
    have eqs:"\<And>i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>"
      by (auto simp add: IH safes)
    show "?case" 
    proof (cases "SFunctions \<sigma> f")
      fix f'
      assume some:"SFunctions \<sigma> f = Some f'" 
      let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
      have subFree:"(\<And>i. dfree (?sub i))" sorry (*using tsubst_preserves_free[OF safes sfree] by simp*)
      have admit:"\<And>i. NTadmit ?sub f'" sorry
      have safef:"dsafe f'" sorry
      have IH2:"dterm_sem I (NTsubst f' ?sub) \<nu> = dterm_sem (NTadjoint I ?sub \<nu>) f' \<nu>"
        by (simp add: nsubst_dterm[OF good_interp admit safef subFree])
      show "?thesis" 
        using IH safes by (auto simp add: eqs adjoint_free[OF sfree] IH2 NTadjoint_free[OF subFree] some good_interp)
    qed (auto simp add: IH adjoint_def vec_extensionality safes)
  qed auto

oops
end

(*
code_thms dl.pointed_finite.NTsubst
print_codesetup
export_code dl.pointed_finite.NTsubst in Haskell
module_name Example file "examples/"
*)
(*
definition x::Enum.finite_5 where "x = finite_5.a\<^sub>1"
global_interpretation ddl:pointed_finite x x x x x x x x x
  defines Tsubst = ddl.Tsubst
  done

term ddl.Tsubst
export_code "ddl.Tsubst" in SML
*)

definition foo::real where "foo = 1.234"
export_code foo in SML

end