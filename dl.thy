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

theory "dl"
imports Complex_Main HOL "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis" "Ordinary_Differential_Equations/Ordinary_Differential_Equations"
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

type_synonym state_dim = "Enum.finite_5"
type_synonym Rn = "real^state_dim"
type_synonym id = state_dim
type_synonym state = "Rn \<times> Rn"
type_synonym simple_state = Rn
type_synonym func_domain_dim = "Enum.finite_5"
type_synonym func_domain = "real^func_domain_dim"

subsection \<open>Syntax\<close>
text \<open>
  We define the syntax of dL terms, formulas and hybrid programs. We deviate
  slightly from the definitions given in CADE'15, which allows arbitrarily
  nested differentials, but with a surprising semantics (e.g. (x')' is zero in
  every state). We restrict the differential operator to what we call simple 
  terms \<theta>_s, which may not contain any further differentials. We also explicitly
  represent the arguments to functions (and their simple term equivalents), 
  which morally speaking should be vectors \<theta>^m and \<theta>_s^m, respectively. However 
  since \<theta>^m is simply an abbreviation for m => \<theta>  it's not clear how to prove 
  that any recursive functions over terms would terminate in this
  representation. Thus they are currently represented as tuples, but finding a 
  way to switch to vectors would make this theory significantly more general.
  
  In keeping with the CADE'15 presentation we currently make the simplifying 
  assumption that all terms are smooth, and thus division and arbitrary 
  exponentiation are absent from the syntax. Several other standard logical 
  constructs are implemented as derived forms to reduce the soundness burden.
\<close>

(* NOTE: The distinction between sterm and dterm should go away. Right now the
 difference is that dterms can contain differentials, but sterms cannot. It
 was decided that probably it's easier to have one type for terms and then
 have a predicate "is_diff_free" that tells us which of the terms are
 sterms. *)
 datatype sterm =
   (* Program variable *)
   SVar id
 (* N.B. This is technically more expressive than true dL since most reals 
   can't be written down. *)
 | SConst real
 | SFunction id "func_domain_dim \<Rightarrow> sterm" ("$s")
 | SPlus sterm sterm
 | STimes sterm sterm
 
datatype dterm =
   Var id ("$\<theta>")
 (* Differential variables only ok in a dterm *)
 | DiffVar id ("$'")
 | Function id "func_domain_dim \<Rightarrow> dterm" ("$f")
 | Plus dterm dterm
 | Times dterm dterm
   (* Inside a differential can only have simple terms *)
 | Differential sterm
 (* Wrap a simple term up as a dterm *)
 | Simply sterm
 
(* My first attempt at encoding ODE systems to write them as a function which
 for every variable specifies either the RHS of the ODE (a differential-free term)
 or explicitly says that variable is not bound by the ODE (None)
 
 NOTE: After discussing this, I am going to try a different representation of ODE's
 which are built up recursively as either atomic ODE's that bind one variable or 
 product ODE's that are the product of two smaller ODE systems. This makes some
 bogus ODE's well-typed, so we will need another predicate to rule out e.g. ODE's
 that bind the same variable to two different terms.
 *)
type_synonym ODE =  "state_dim \<Rightarrow> (sterm option)"

datatype hp =
   Pvar id                ("$\<alpha>")
 | Assign id dterm        (infixr ":=" 10)
 | DiffAssign id dterm
 | Test formula           ("?")
 (* An ODE program is an ODE system with some evolution domain. *)
 | EvolveODE ODE formula
 | Choice hp hp           (infixl "\<union>\<union>" 10)
 | Sequence hp hp         (infixr ";;" 8)
 | Loop hp                ("_**")

and formula =
   Geq dterm dterm      
 | Prop id "func_domain_dim \<Rightarrow> dterm"      ("$\<phi>")
 | Not formula            ("!")
 | And formula formula    (infixl "&&" 8)
 | Forall id formula
 | Box hp formula         ("([[_]]_)" 10)
 (* DiffFormula \<phi> gives us the invariant for proving \<phi> by differential induction. *)
 | DiffFormula formula
 (* Unary quantifier symbols *)
 | InContext id formula
 (* Nullary quantifier symbols *)
 | Predicational id
 
type_synonym stuple = "(func_domain_dim \<Rightarrow> sterm)"
type_synonym dtuple = "(func_domain_dim \<Rightarrow> dterm)"

(* Derived forms *)
fun Or :: "formula \<Rightarrow> formula \<Rightarrow> formula" (infixl "||" 7)
  where "Or P Q = Not (And (Not P) (Not Q))"

fun Implies :: "formula \<Rightarrow> formula \<Rightarrow> formula" (infixr "\<rightarrow>" 10)
  where "Implies P Q = Or Q (Not P)"

fun Equiv :: "formula \<Rightarrow> formula \<Rightarrow> formula" (infixl "\<leftrightarrow>" 10) 
  where "Equiv P Q = Or (And P Q) (And (Not P) (Not Q))"

fun Exists :: "id \<Rightarrow> formula \<Rightarrow> formula"
  where "Exists x P = Not (Forall x (Not P))"
  
fun Equals :: "dterm \<Rightarrow> dterm \<Rightarrow> formula"
  where "Equals \<theta> \<theta>' = ((Geq \<theta> \<theta>') && (Geq \<theta>' \<theta>))"

fun Diamond :: "hp \<Rightarrow> formula \<Rightarrow> formula" ("(\<langle>_\<rangle>_)" 10)
  where "Diamond \<alpha> P = Not(Box \<alpha> (Not P))"
  
subsection \<open>Denotational Semantics\<close>
  
text \<open>
  The central definitions for the denotational semantics are states \nu, 
  interpretations I and the interpretation functions [[\psi]]I, [[\theta]]I\nu,
  [[\alpha]]I, which are represented by the Isabelle functions fml_semantics,
  term_semantics and prog_semantics, respectively.
  
  The additional functions term_list_semantics and loop_semantics are
  straightforward helper functions for the definitions of term_semantics
  and prog_semantics.
  
  To enable reasoning about derivatives of functions, our interpretations 
  include a field FunctionFrechet specifying the Frechet derivative 
  (FunctionFrechet f \<nu>) : \<real>^m -> \<real> for every function in every state. The 
  proposition (is_interp I) asserts that every function is  differentiable and
  its derivative agrees everywhere with the derivative given by 
  FunctionFrechet.
  \<close>

record interp =
  Functions       :: "id \<Rightarrow> func_domain \<Rightarrow> real"
  FunctionFrechet :: "id \<Rightarrow> Rn \<Rightarrow> func_domain \<Rightarrow> real"
  Predicates      :: "id \<Rightarrow> func_domain \<Rightarrow> bool"
  Contexts        :: "id \<Rightarrow> state set \<Rightarrow> state set"
  Predicationals  :: "id \<Rightarrow> state set"
  Programs        :: "id \<Rightarrow> (state * state) set"

definition is_interp :: "interp \<Rightarrow> bool"
  where "is_interp I \<equiv> 
    \<forall>x. \<forall>i. (FDERIV (Functions I i) x :> (FunctionFrechet I i x))"

(* sterm_semantics is the term semantics for differential-free terms. *)
primrec sterm_semantics :: "interp \<Rightarrow> sterm \<Rightarrow> simple_state \<Rightarrow> real"
  where "sterm_semantics I (SVar x) v = v $ x"
  | "sterm_semantics I (SFunction f args) v = 
    Functions I f (vec_lambda (\<lambda>i. sterm_semantics I (args i) v))"
  | "sterm_semantics I (SPlus t1 t2) v = 
    (sterm_semantics I t1 v) + (sterm_semantics I t2 v)"
  | "sterm_semantics I (STimes t1 t2) v =                     
    (sterm_semantics I t1 v) * (sterm_semantics I t2 v)"
  | "sterm_semantics I (SConst r) v = r"
  
(* basis_vector i is the i'th basis vector for the standard Euclidean basis. *)
fun basis_vector :: "id \<Rightarrow> Rn"
  where "basis_vector x = vec_lambda (\<lambda>i. if x = i then 1 else 0)"

(* frechet I \<theta> \<nu> gives us the frechet derivative of the term \<theta> in the interpretation
 I at state \<nu> (containing only the unprimed variables). The frechet derivative is a 
 linear map from the differential state \<nu> to reals. 
 *)
primrec frechet :: "interp \<Rightarrow> sterm \<Rightarrow> simple_state \<Rightarrow> simple_state \<Rightarrow> real"
  where "frechet I (SVar x) v = (\<lambda>v'. inner v' (basis_vector x))"
  | "frechet I (SFunction f args) v = 
    (\<lambda>v'. FunctionFrechet I f (vec_lambda (\<lambda>i. sterm_semantics I (args i) v))
       (vec_lambda (\<lambda>i. frechet I (args i) v v')))"
  | "frechet I (SPlus t1 t2) v = (\<lambda>v'. frechet I t1 v v' + frechet I t2 v v')"
  | "frechet I (STimes t1 t2) v = 
    (\<lambda>v'. (sterm_semantics I t1 v) * (frechet I t2 v v')
        + (frechet I t1 v v') * (sterm_semantics I t2 v))"
  | "frechet I (SConst r) v = (\<lambda>v'. 0)"
  
 
fun directional_derivative :: "interp \<Rightarrow> sterm \<Rightarrow> state \<Rightarrow> real" 
  where "directional_derivative I t = (\<lambda>v. frechet I t (fst v) (snd v))"

(* Semantics for terms that are allowed to contain differentials.
   Note there is some duplication with sterm_semantics (hence the desire to combine the two).*)
primrec dterm_semantics :: "interp \<Rightarrow> dterm \<Rightarrow> state \<Rightarrow> real"
  where "dterm_semantics I (Var x) = (\<lambda>v. vec_nth (fst v) x)"
  | "dterm_semantics I (DiffVar x) = (\<lambda>v. vec_nth (snd v) x)"
  | "dterm_semantics I (Function f args) = 
    (\<lambda>v. Functions I f (vec_lambda (\<lambda>i. dterm_semantics I (args i) v)))"
  | "dterm_semantics I (Plus t1 t2) = 
    (\<lambda>v. (dterm_semantics I t1 v) + (dterm_semantics I t2 v))" 
  | "dterm_semantics I (Times t1 t2) = 
    (\<lambda>v. (dterm_semantics I t1 v) * (dterm_semantics I t2 v))"
  | "dterm_semantics I (Differential t) = (\<lambda>v. directional_derivative I t v)"
  | "dterm_semantics I (Simply t) = (\<lambda>\<nu>. sterm_semantics I t (fst \<nu>))"

(* repv \<nu> x r replaces the value of (unprimed) variable x in the state \<nu> with r *)
fun repv :: "state \<Rightarrow> id \<Rightarrow> real \<Rightarrow> state"
  where "repv v x r = 
  (vec_lambda (\<lambda>y. if x = y then r else vec_nth (fst v) y), snd v)"

(* repd \<nu> x' r replaces the value of (primed) variable x' in the state \<nu> with r *)
fun repd :: "state \<Rightarrow> id \<Rightarrow> real \<Rightarrow> state"
  where "repd v x r = 
  (fst v, vec_lambda (\<lambda>y. if x = y then r else vec_nth (snd v) y))"

(* rhs_semantics gives us the "semantics for the right hand side of an ODE"
   rhs_semantics I \<nu> ODE gives us vector in Rn that contains for each variable
   either the value of the corresponding term in the ODE or 0 if the variable is unbound.
  *)
fun rhs_semantics:: "interp \<Rightarrow> Rn \<Rightarrow> ODE \<Rightarrow> Rn"
  where "rhs_semantics I \<nu> ODE = vec_lambda (\<lambda>i. case ODE i of None \<Rightarrow> 0 | Some t \<Rightarrow> sterm_semantics I t \<nu>)"

(* ivp I \<nu> ODE gives us an initial-value problem based on ODE in the initial state \<nu>*)
fun ivp :: "interp \<Rightarrow> Rn \<Rightarrow> ODE \<Rightarrow> Rn ivp"
  where "ivp I \<nu>0 ODE = 
  \<lparr>ivp_f = (\<lambda>t\<nu>. rhs_semantics I  (snd t\<nu>) ODE), 
   ivp_t0 = 0, 
   ivp_x0 = \<nu>0, 
   ivp_T = UNIV, 
   ivp_X = UNIV \<rparr>"

(* ivp_semantics_at I IVP t gives the state produced by
 following IVP for t time. *)
fun ivp_semantics_at::"interp \<Rightarrow> Rn ivp \<Rightarrow> real \<Rightarrow> state"
  where "ivp_semantics_at I IVP t = 
    (ivp.solution IVP t, ivp_f IVP (t, (ivp.solution IVP t)))"

(* Semantics for formulas, differential formulas, programs, initial-value problems and loops.
   Loops and IVP's do not strictly have to have their own notion of semantics, but for loops
   it was helpful to describe the semantics recursively and for IVP's it was convenient to
   have ivp_semantics as a helper function simply because ODE's are a little complicated.
   
   Differential formulas do actually have to have their own notion of semantics, because
   the meaning of a differential formula (\<phi>)' depends on the syntax of the formula \<phi>:
   we can have two formulas \<phi> and \<psi> that have the exact same semantics, but where 
   (\<phi>)' and (\<psi>)' differ because \<phi> and \<psi> differ syntactically.
*)
fun fml_semantics  :: "interp \<Rightarrow> formula \<Rightarrow> state set"
and diff_formula_semantics  :: "interp \<Rightarrow> formula \<Rightarrow> state set"
and prog_semantics :: "interp \<Rightarrow> hp \<Rightarrow> (state * state) set"
and ivp_semantics  :: "interp \<Rightarrow> Rn ivp \<Rightarrow> formula \<Rightarrow> state set"
and loop_semantics :: "interp \<Rightarrow> hp \<Rightarrow> nat \<Rightarrow> (state * state) set"
  where "fml_semantics I (Geq t1 t2) = 
        {v. dterm_semantics I t1 v \<ge> dterm_semantics I t2 v}"
      | "fml_semantics I (Prop P terms) =
        {\<nu>. Predicates I P (vec_lambda (\<lambda>i. dterm_semantics I (terms i) \<nu>))}"
      | "fml_semantics I (Not \<phi>) = {v. v \<notin> fml_semantics I \<phi>}"
      | "fml_semantics I (And \<phi> \<psi>) = fml_semantics I \<phi> \<inter> fml_semantics I \<psi>"
      | "fml_semantics I (Forall x \<phi>) = 
        {v. \<forall>r. (repv v x r) \<in> fml_semantics I \<phi>}"
      | "fml_semantics I (Box \<alpha> \<phi>) =
        {\<nu>. \<forall> \<omega>. (\<nu>, \<omega>) \<in> prog_semantics I \<alpha> \<longrightarrow> \<omega> \<in> fml_semantics I \<phi>}"
      | "fml_semantics I (InContext c \<phi>) = Contexts I c (fml_semantics I \<phi>)"
      | "fml_semantics I (Predicational p) = Predicationals I p"
      | "fml_semantics I (DiffFormula p) = diff_formula_semantics I p"
      | "diff_formula_semantics I (Geq (Simply f) (Simply g)) = 
          {v. dterm_semantics I (Differential f) v \<ge> dterm_semantics I (Differential g) v}"
      | "diff_formula_semantics I (Not p) = diff_formula_semantics I p"
      | "diff_formula_semantics I (And p q) = diff_formula_semantics I p \<inter> diff_formula_semantics I p"
      | "diff_formula_semantics I  p = fml_semantics I p"
 
      | "prog_semantics I (Pvar p) = Programs I p"
      | "prog_semantics I (Assign x t) = 
        {(\<nu>, \<omega>) | \<nu> \<omega>. \<omega> = repv \<nu> x (dterm_semantics I t \<nu>)}"
      | "prog_semantics I (DiffAssign x t) =
        {(\<nu>, \<omega>) | \<nu> \<omega>. \<omega> = repd \<nu> x (dterm_semantics I t \<nu>)}"
      | "prog_semantics I (Test \<phi>) = {(\<nu>, \<nu>) | \<nu>. \<nu> \<in> fml_semantics I \<phi>}"
      | "prog_semantics I (Choice \<alpha> \<beta>) = 
        prog_semantics I \<alpha> \<union> prog_semantics I \<beta>"
      | "prog_semantics I (Sequence \<alpha> \<beta>) = 
        {(\<nu>, \<omega>) | \<nu> \<omega>. \<exists>\<mu>. (\<nu>, \<mu>) \<in> prog_semantics I \<alpha> 
                         \<and> (\<mu>, \<omega>) \<in> prog_semantics I \<beta>}"
      | "prog_semantics I (Loop \<alpha>) = (\<Union>n. loop_semantics I \<alpha> n)"
      | "prog_semantics I (EvolveODE ODE \<phi>) = 
        {(\<nu>, \<mu>) | \<nu> \<mu>. \<mu> \<in> ivp_semantics I (ivp I (fst \<nu>) ODE) \<phi>}"
      | "ivp_semantics I IVP \<phi> = 
        {\<omega>. (\<exists>t. (\<omega> = ivp_semantics_at I IVP t \<and>
          (\<forall>s. ((s \<ge> 0 \<and> s \<le> t) \<longrightarrow> (ivp_semantics_at I IVP s) \<in> fml_semantics I \<phi>)))) }"
      | "loop_semantics I \<alpha> 0 = {(\<nu>, \<nu>) | \<nu>. \<nu> = \<nu>}"
      | "loop_semantics I \<alpha> (Suc n) = 
        {(\<nu>, \<omega>) | \<nu> \<omega>. \<exists>\<mu>. (\<nu>, \<mu>) \<in> prog_semantics I \<alpha> 
                         \<and> (\<mu>, \<omega>) \<in> loop_semantics I \<alpha> n}"

   
subsection \<open>Trivial Simplification Lemmas\<close>
text \<open>
 We often want to pretend the definitions in the semantics are written slightly
 differently than they are. Since the simplifier has some trouble guessing that
 these are the right simplifications to do, we write them all out explicitly as
 lemmas, even though they prove trivially.
\<close>

lemma svar_case: "sterm_semantics I (SVar x) = (\<lambda>v. v $ x)"
  apply(auto)
  done

lemma sconst_case: "sterm_semantics I (SConst r) = (\<lambda>v. r)"
  apply(auto)
  done

lemma sfunction_case: "sterm_semantics I (SFunction f args) = 
(\<lambda>v. Functions I f (vec_lambda (\<lambda>i. sterm_semantics I (args i) v)))"
  apply(auto)
done

lemma splus_case:  "sterm_semantics I (SPlus t1 t2) = 
  (\<lambda>v. (sterm_semantics I t1 v) + (sterm_semantics I t2 v))"
  apply(auto)
done

lemma stimes_case: "sterm_semantics I (STimes t1 t2) = 
  (\<lambda>v. (sterm_semantics I t1 v) * (sterm_semantics I t2 v))"
  apply(auto)
done

subsection \<open>Characterization of Term Derivatives\<close>
text \<open>
 This section builds up to a proof that in well-formed interpretations, all 
 terms have derivatives, and those derivatives agree with the expected rules
 of derivatives. In particular, we show the [frechet] function given in the
 denotational semantics is the true Frechet derivative of a term. From this
 theorem we can recover all the standard derivative rules as corollaries.
\<close>
        
lemma inner_prod_eq: 
  fixes i::id
  shows "(\<lambda>(v::Rn). inner ((\<lambda>y. y) v) ((\<lambda>_. basis_vector (i::state_dim)) v)) 
    = (\<lambda>(v::Rn). vec_nth v i)"
  proof -
    have big_and: "\<And>v. inner ((\<lambda>y. y) v) ((\<lambda>_. basis_vector (i::state_dim)) v)
      = vec_nth v i" 
    proof -
      have 4: "finite {k. k = i}" by (auto)
      have 5: "finite {k. \<not>(k = i)}" by (auto) 
      have 7: "\<And>v. (\<Sum>j \<in> {k. k = i} \<inter>{k. \<not>(k = i)}. 
                 ((vec_nth v j) * (vec_nth (basis_vector i) j))) = 0"
               by(auto)
      have 9: "\<And>v. (\<Sum>j \<in> {k. k = i}. 
                 ((vec_nth v j) * (vec_nth (basis_vector i) j))) 
               = (vec_nth v i) * (vec_nth (basis_vector i) i)"
               by(auto)
      have 10: "\<And>v. (\<Sum>j \<in> {k. \<not>(k = i)}. 
                 ((vec_nth v j) * (vec_nth (basis_vector i) j))) = 0"
               by(auto)

      have 1: "\<And>v. inner ((\<lambda>y. y) v) ((\<lambda>_. basis_vector i) v) =
              inner v (basis_vector i)" by (auto)
      
      also have 2: "\<And>v. (inner v (basis_vector i)) =
               (\<Sum>j\<in> UNIV. ((vec_nth v j) * (vec_nth (basis_vector i) j)))" 
               by (simp add: inner_vec_def)
      also have 3: 
        "\<And>v. (\<Sum>j\<in> UNIV. ((vec_nth v j) * (vec_nth (basis_vector i) j))) = 
             (\<Sum>j\<in>({k. k = i \<or> \<not>(k = i)}). 
               ((vec_nth v j) * (vec_nth (basis_vector i) j)))"
               by (auto)
      also have 3: 
        "\<And>v. (\<Sum>j\<in> ({k. k = i \<or> \<not>(k = i)}). 
           ((vec_nth v j) * (vec_nth (basis_vector i) j))) = 
        (\<Sum>j\<in> ({k. k = i} \<union> {k. \<not>(k = i)}). 
           ((vec_nth v j) * (vec_nth (basis_vector i) j)))"
               by (smt Collect_cong Collect_disj_eq)
      also from 4 and 5 
      have 6: 
        "\<And>v. (\<Sum>j\<in> ({k. k = i} \<union> {k. \<not>(k = i)}). 
            ((vec_nth v j) * (vec_nth (basis_vector i) j))) =
            (\<Sum>j \<in> {k. k = i}. ((vec_nth v j) * (vec_nth (basis_vector i)j)))
          + (\<Sum>j \<in> {k. \<not>(k = i)}. ((vec_nth v j) * (vec_nth (basis_vector i)j)))
          - (\<Sum>j \<in> {k. k = i} \<inter>{k. \<not>(k = i)}. 
              ((vec_nth v j) * (vec_nth (basis_vector i) j)))"
               by (rule setsum_Un)
      also from 6 and 7 have 8: "\<And>v. 
             (\<Sum>j \<in> {k. k = i}.((vec_nth v j)*(vec_nth (basis_vector i)j)))
            + (\<Sum>j \<in> {k. \<not>(k = i)}.((vec_nth v j)*(vec_nth (basis_vector i)j)))
            - (\<Sum>j \<in> {k. k = i} \<inter>{k. \<not>(k = i)}. 
              ((vec_nth v j) * (vec_nth (basis_vector i) j)))
            =
              (\<Sum>j \<in> {k. k = i}.((vec_nth v j)*(vec_nth (basis_vector i)j)))
            + (\<Sum>j \<in> {k. \<not>(k = i)}.((vec_nth v j)*(vec_nth (basis_vector i)j)))"
               by(auto)
      also from 9 and 10 have 11: 
      "\<And>v. (\<Sum>j \<in> {k. k = i}. ((vec_nth v j) * (vec_nth (basis_vector i) j)))
        + (\<Sum>j \<in> {k. \<not>(k = i)}. ((vec_nth v j) * (vec_nth (basis_vector i) j)))
      = (vec_nth v i) * (vec_nth (basis_vector i) i)"
               by(auto)
      also from 11 have 12: 
      "\<And>v. (vec_nth v i) * (vec_nth (basis_vector i) i) = vec_nth v i" by(auto)
      finally show "\<And>v. ?thesis v" by(auto)
    qed
    from big_and have big_forall:
    "\<forall>v. (\<lambda>v. inner ((\<lambda>y. y) v) ((\<lambda>_. basis_vector (i::state_dim)) v)) v 
      = (\<lambda>v. vec_nth v i) v" 
    by (rule allI)
    have 16: "(\<lambda>v. inner ((\<lambda>y. y) v) ((\<lambda>_. basis_vector (i::state_dim)) v)) 
      \<in> extensional UNIV" by(auto)
    have 17: "(\<lambda>v. vec_nth v i) \<in> extensional UNIV" by(auto)
    from big_forall and 16 and 17 have 18: 
    "(\<lambda>v. inner ((\<lambda>y. y) v) ((\<lambda>_. basis_vector (i::state_dim)) v)) 
    =(\<lambda>v. vec_nth v i)"
      by (auto)
    from 18 show ?thesis by(auto)
qed

theorem svar_deriv: 
  fixes x:: id and \<nu>:: "Rn" and F::"real filter"
  shows "((\<lambda>v. vec_nth v x) has_derivative 
    (\<lambda>v'. inner v' (vec_lambda (\<lambda>i. if x = i then 1 else 0)))) (at \<nu>)"
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
  by(auto)
  have deriv_eq: "(\<lambda>h. inner (?f \<nu>) (?g' h) + inner (?f' h) (?g \<nu>)) 
    = (\<lambda>v'. inner v' (vec_lambda (\<lambda>i. if x = i then 1 else 0)))"
  by(auto)
  from better_deriv and deriv_eq show ?thesis by (auto)
qed

(* TODO: This is now silly *) 
fun stuple_proj::"(func_domain_dim \<Rightarrow> sterm) \<Rightarrow> func_domain_dim \<Rightarrow> sterm"
  where "stuple_proj args i = args i"

lemma function_case_inner:
  assumes good_interp:
    "(\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x))"       
  assumes IH:"((\<lambda>v. vec_lambda(\<lambda>i. sterm_semantics I (args i) v)) 
             has_derivative (\<lambda> v. vec_lambda(\<lambda>i. frechet I (args i) \<nu> v))) (at \<nu>)"
  shows  "((\<lambda>v. Functions I f (vec_lambda(\<lambda>i. sterm_semantics I (args i) v)))
            has_derivative (\<lambda>v. frechet I ($s f args) \<nu> v)) (at \<nu>)"
proof -
  let ?h = "(\<lambda>v. Functions I f (vec_lambda(\<lambda>i. sterm_semantics I (args i) v)))"
  let ?h' = "frechet I ($s f args) \<nu>"
  let ?g = "(\<lambda>v. vec_lambda(\<lambda>i. sterm_semantics I (args i) v))"
  let ?g' = "(\<lambda>v. vec_lambda(\<lambda>i. frechet I (args i) \<nu> v))"
  let ?f = "(\<lambda>y. Functions I f y)"
  let ?f' = "FunctionFrechet I f (?g \<nu>)"
  have hEqFG:  "?h  = ?f  o ?g" by (auto)
  have hEqFG': "?h' = ?f' o ?g'"                          
    proof -
      have frechet_def:"frechet I (SFunction f args) \<nu> 
          = (\<lambda>v'. FunctionFrechet I f (?g \<nu>) (vec_lambda(\<lambda>i. frechet I (args i) \<nu> v')))"         
      by (auto)
      have composition:
        "(\<lambda>v'. FunctionFrechet I f (?g \<nu>) (vec_lambda(\<lambda>i. frechet I (args i) \<nu> v')))
      = (FunctionFrechet I f (?g \<nu>)) o (\<lambda> v'. vec_lambda(\<lambda>i. frechet I (args i) \<nu> v'))"
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

lemma func_lemma2:"\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x) \<Longrightarrow>
    (\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> (sterm_semantics I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)) \<Longrightarrow>
    ((\<lambda>v. Functions I f (vec_lambda(\<lambda>i. sterm_semantics I (args i) v))) has_derivative frechet I ($s f args) \<nu>) (at \<nu>)"
proof -
  assume a1: "\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x)"
  assume a2: "\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> (sterm_semantics I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)"
  have "\<forall>f fa v. (\<exists>fb. \<not> (f (fb::Enum.finite_5) has_derivative fa fb (v::(real, Enum.finite_5) vec)) (at v)) \<or> ((\<lambda>v. vec_lambda(\<lambda>fa. (f fa v::real))) has_derivative (\<lambda>va. vec_lambda(\<lambda>f. fa f v va))) (at v)"
    using has_derivative_vec by force
  then have "((\<lambda>v. vec_lambda(\<lambda>f. sterm_semantics I (args f) v) )has_derivative (\<lambda>v. vec_lambda(\<lambda>f. frechet I (args f) \<nu> v))) (at \<nu>)"
    using a2 by (meson rangeI)
  then show "((\<lambda>v. Functions I f (vec_lambda(\<lambda>f. sterm_semantics I (args f) v))) has_derivative frechet I ($s f args) \<nu>) (at \<nu>)"
    using a1 function_case_inner by blast
qed 

lemma func_lemma:"                  
is_interp I \<Longrightarrow>                 
(\<And>\<theta> :: sterm. \<theta> \<in> range args \<Longrightarrow> (sterm_semantics I \<theta> has_derivative 
                 frechet I \<theta> \<nu>) (at \<nu>)) \<Longrightarrow> (sterm_semantics I ($s f args) has_derivative 
            frechet I ($s f args) \<nu>) (at \<nu>)"
apply(simp only: sfunction_case is_interp_def function_case_inner)
apply(erule func_lemma2)
apply(auto)
done

(* Our syntactically-defined derivatives of terms agree with the actual derivatives of the terms.
 Since our definition of derivative is total, this gives us that derivatives are "decidable" for
 terms (modulo computations on reals) and that they obey all the expected identities, which gives
 us the axioms we want for differential terms essentially for free.
 *)
lemma frechet_correctness:
  fixes I and \<nu> 
  assumes good_interp:"is_interp I"
  shows "FDERIV (sterm_semantics I \<theta>) \<nu> :> (frechet I \<theta> \<nu>)"
  proof (induct \<theta>)
    fix I \<nu> 
    show "\<And>x. (sterm_semantics I (SVar x) has_derivative 
               frechet I (SVar x) \<nu>) (at \<nu>)"
      by (simp add: svar_case svar_deriv)
  next
    show "\<And>x. (sterm_semantics I (SConst x) has_derivative 
               frechet I (SConst x) \<nu>) (at \<nu>)"
      by (simp add: sconst_case)
  next
                 
     fix f 
     fix args :: stuple
     assume IH:"\<And>\<theta> :: sterm. \<theta> \<in> range args \<Longrightarrow> (sterm_semantics I \<theta> has_derivative 
                 frechet I \<theta> \<nu>) (at \<nu>)"
     show "(sterm_semantics I ($s f args) has_derivative 
            frechet I ($s f args) \<nu>) (at \<nu>)"
        using IH func_lemma good_interp by (auto)
  next
    fix x1 x2a
    assume IH1:"(sterm_semantics I x1 has_derivative frechet I x1 \<nu>) (at \<nu>)"
    assume IH2:"(sterm_semantics I x2a has_derivative frechet I x2a \<nu>) (at \<nu>)"
    show "(sterm_semantics I (SPlus x1 x2a) has_derivative 
          frechet I (SPlus x1 x2a) \<nu>) (at \<nu>)"
      using IH1 IH2 splus_case by (auto)
  next
    fix x1 x2a
    assume IH1:"(sterm_semantics I x1 has_derivative frechet I x1 \<nu>) (at \<nu>)"
    assume IH2:"(sterm_semantics I x2a has_derivative frechet I x2a \<nu>) (at \<nu>)"
    show "(sterm_semantics I (STimes x1 x2a) has_derivative 
           frechet I (STimes x1 x2a) \<nu>) (at \<nu>)"
    using stimes_case IH1 IH2 by (auto)
  qed                                 

section \<open>Prerequisites for Substitution\<close>
subsection \<open>Variable Binding Definitions\<close>
text\<open>
  We represent the (free or bound or must-bound) variables of a term as an (id + id) set,
  where all the (Inl x) elements are unprimed variables x and all the (Inr x) elements are
  primed variables x'.
  \<close>
(* The bound variables of an ODE (which will also be included as free variables) *)
fun ODE_vars :: "ODE \<Rightarrow> (id + id) set"
  where "ODE_vars ODE =
    (\<Union>x \<in> ({x. ODE x \<noteq> None}) . ({Inl x, Inr x}))"

(* Bound variables of a formula 
   Bound variables of a program *)
fun BVF :: "formula \<Rightarrow> (id + id) set"
and BVP :: "hp \<Rightarrow> (id + id) set"
where
   "BVF (Geq f g) = {}"
 | "BVF (Prop p dfun_args) = {}"
 | "BVF (Not p) = BVF p"
 | "BVF (And p q) = BVF p \<union> BVF q"
 | "BVF (Forall x p) = {Inl x} \<union> BVF p"
 | "BVF (Box \<alpha> p) = BVP \<alpha> \<union> BVF p"
 | "BVF (DiffFormula p) = BVF p"
 | "BVF (InContext C p) = UNIV"
 | "BVF (Predicational P) = UNIV"    

 | "BVP (Pvar a) = UNIV"
 | "BVP (Assign x \<theta>) = {Inl x}"
 | "BVP (DiffAssign x \<theta>) = {Inr x}"
 | "BVP (Test \<phi>) = {}"
 | "BVP (EvolveODE ODE \<phi>) = ODE_vars ODE" 
 | "BVP (Choice \<alpha> \<beta>) = BVP \<alpha> \<union> BVP \<beta>"
 | "BVP (Sequence \<alpha> \<beta>) = BVP \<alpha> \<union> BVP \<beta>"
 | "BVP (Loop \<alpha>) = BVP \<alpha>"

(* Must-bound variables (of a program)*)
fun MBV :: "hp \<Rightarrow> (id + id) set"
  where
   "MBV (Pvar a) = {}"
 | "MBV (Choice \<alpha> \<beta>) = MBV \<alpha> \<inter> MBV \<beta>" 
 | "MBV (Sequence \<alpha> \<beta>) = MBV \<alpha> \<union> MBV \<beta>"
 | "MBV (Loop \<alpha>) = {}"
 | "MBV \<alpha> = BVP \<alpha>"

(* Free variables of a simple term *)
primrec FVS :: "sterm \<Rightarrow> id set"
where
   "FVS (SVar x) = {x}"
 | "FVS (SConst x) = {}"
 | "FVS (SFunction f args) = (\<Union>i. FVS (args i))"
 | "FVS (SPlus f g) = FVS f \<union> FVS g"
 | "FVS (STimes f g) = FVS f \<union> FVS g"

(* Free variables of a differential term *)
(* Free variables of the arguments to a differential-term function 
  (tuples of differential terms)*)
primrec FVD :: "dterm \<Rightarrow> (id + id) set"
where
   "FVD (Var x) = {Inl x}"
 | "FVD (DiffVar x) = {Inr x}"
 | "FVD (Function f args) = (\<Union>i. FVD (args i))"
 | "FVD (Plus f g) = FVD f \<union> FVD g"
 | "FVD (Times f g) = FVD f \<union> FVD g"
 | "FVD (Differential f) = (\<Union>x \<in> (FVS f). {Inl x, Inr x})"
 | "FVD (Simply f) =  {Inl x | x. x \<in> FVS f}"
 (*| "FVDA (FA a1 a2 a3 a4 a5) = FVD a1 \<union> FVD a2 \<union>  FVD a3 \<union>  FVD a4 \<union> FVD a5"*)
 
(* Free variables of an ODE includes both the bound variables and the terms *)
fun FVODE :: "ODE \<Rightarrow> (id + id) set"
  where
   "FVODE ODE = 
     (\<Union>x \<in> {x. Some x \<in> {(ODE y)| y. y = y}}. FVD (Simply x))"

(* Free variables of a formula *)
(* Free variables of a program *)
fun FVF :: "formula \<Rightarrow> (id + id) set"
and FVP :: "hp \<Rightarrow> (id + id) set"
where
   "FVF (Geq f g) = FVD f \<union> FVD g"
 | "FVF (Prop p args) = (\<Union>i. FVD (args i))"
 | "FVF (Not p) = FVF p"
 | "FVF (And p q) = FVF p \<union> FVF q"
 | "FVF (Forall x p) = FVF p - {Inl x}"
 | "FVF (Box \<alpha> p) =   FVF p - MBV \<alpha>"
 | "FVF (DiffFormula p) = FVF p"
 | "FVF (InContext C p) = UNIV"
 | "FVF (Predicational P) = UNIV"    
 | "FVP (Pvar a) = UNIV"
 | "FVP (Assign x \<theta>) = FVD \<theta>"
 | "FVP (DiffAssign x \<theta>) = FVD \<theta>"
 | "FVP (Test \<phi>) = FVF \<phi>"
 | "FVP (EvolveODE ODE \<phi>) = ODE_vars ODE \<union> FVODE ODE \<union> FVF \<phi>"
 | "FVP (Choice \<alpha> \<beta>) = FVP \<alpha> \<union> FVP \<beta>"
 | "FVP (Sequence \<alpha> \<beta>) = (FVP \<alpha> \<union> FVP \<beta>) - (MBV \<alpha>)"
 | "FVP (Loop \<alpha>) = FVP \<alpha>"
 


subsection \<open>Axioms\<close>
text \<open>
  The uniform substitution calculus is based on a finite list of concrete 
  axioms, which are defined and proved sound in this section. When axioms apply
  to arbitrary programs or formulas, they mention concrete program or formula
  variables, which are then instantiated by uniform substitution, as opposed
  metavariables.
  \<close>

(* Predicates*)
definition H :: "id" where "H \<equiv> finite_5.a\<^sub>1"
definition P :: "id" where "P \<equiv> finite_5.a\<^sub>2"
definition Q :: "id" where "Q \<equiv> finite_5.a\<^sub>3"

(* Predicationals *)
definition PP :: "id" where "PP \<equiv> finite_5.a\<^sub>1"
definition QQ :: "id" where "QQ \<equiv> finite_5.a\<^sub>2"

(* Programs *)
definition a :: "id" where "a \<equiv> finite_5.a\<^sub>1"
definition b :: "id" where "b \<equiv> finite_5.a\<^sub>2"

(* Program variables*)
definition x :: "id" where "x \<equiv> finite_5.a\<^sub>1"

(* Functions *)
definition f :: "id" where "f \<equiv> finite_5.a\<^sub>1"

definition valid :: "formula \<Rightarrow> bool" 
where "valid \<phi> \<equiv> (\<forall> I. \<forall> \<nu>. is_interp I \<longrightarrow> \<nu> \<in> fml_semantics I \<phi>)" 

(* Arguments for a "nullary" function - a tuple of all-zeros. When we encode 
  a function that has less than the maximum allowed number of arguments, we
  do so by making the remaining arguments 0 at every use site. We can't actually
  enforce that the interpretation of the function "doesnt care" about an argument,
  but if we never use that argument at more than one value there's no way to "notice"
  that the extra arguments exist *)
definition empty :: "dtuple"
  where "empty \<equiv> \<lambda>i.(Simply (SConst 0))"

(* Function argument tuple where the first argument is arbitrary and the rest are zero.*)
fun singleton :: "dterm \<Rightarrow> dtuple"
  where "singleton t i = (if i = finite_5.a\<^sub>1 then t else (Simply (SConst 0)))"

(* Equivalents of the above for functions over simple terms. *)
definition sempty :: "stuple"
  where "sempty _ \<equiv> (SConst 0)"

fun ssingleton :: "sterm \<Rightarrow> stuple"
  where "ssingleton t finite_5.a\<^sub>1 = t"
  | "ssingleton t _ = (SConst 0)"
     
definition assign_axiom :: "formula"
  where "assign_axiom \<equiv> 
    ([[x := ($f f empty)]] (Prop P (singleton (Var x)))) 
      \<leftrightarrow> Prop P (singleton ($f f empty))"

definition loop_iterate_axiom :: "formula"
  where "loop_iterate_axiom \<equiv> ([[$\<alpha> a**]]Predicational PP) 
    \<leftrightarrow> ((Predicational PP) && ([[$\<alpha> a]][[$\<alpha> a**]]Predicational PP))"
  
definition test_axiom :: "formula"
  where "test_axiom \<equiv> 
    ([[?($\<phi> H empty)]]$\<phi> P empty) \<leftrightarrow> (($\<phi> H empty) \<rightarrow> ($\<phi> P empty))"
   
definition box_axiom :: "formula"
  where "box_axiom \<equiv> (\<langle>$\<alpha> a\<rangle>Predicational PP) \<leftrightarrow> !([[$\<alpha> a]]!(Predicational PP))"

definition choice_axiom :: "formula"
  where "choice_axiom \<equiv> ([[$\<alpha> a \<union>\<union> $\<alpha> b]]Predicational PP) 
    \<leftrightarrow> (([[$\<alpha> a]]Predicational PP) && ([[$\<alpha> b]]Predicational PP))"
 
definition Kaxiom :: "formula"
  where "Kaxiom \<equiv> ([[$\<alpha> a]]((Predicational PP) \<rightarrow> (Predicational QQ))) 
    \<rightarrow> ([[$\<alpha> a]]Predicational PP) \<rightarrow> ([[$\<alpha> a]]Predicational QQ)"
  
(*
definition Ibroken :: "formula"
  where "Ibroken \<equiv> ([[$$a]]($P [] \<rightarrow> ([[$$a]]$P [])) 
    \<rightarrow> ($P [] \<rightarrow> ([[($$a)**]]$P [])))"*)
  
definition Iaxiom :: "formula"
  where "Iaxiom \<equiv> ([[($\<alpha> a)**]](Predicational PP \<rightarrow> ([[$\<alpha> a]]Predicational PP))
    \<rightarrow> (Predicational PP \<rightarrow> ([[($\<alpha> a)**]]Predicational PP)))"

definition Vaxiom :: "formula"
  where "Vaxiom \<equiv> ($\<phi> P empty) \<rightarrow> ([[$\<alpha> a]]($\<phi> P empty))"
  
definition G_holds :: "formula \<Rightarrow> hp \<Rightarrow> bool"
  where "G_holds \<phi> \<alpha> \<equiv> valid \<phi> \<longrightarrow> valid ([[\<alpha>]]\<phi>)"
  
definition Skolem_holds :: "formula \<Rightarrow> id \<Rightarrow> bool"
  where "Skolem_holds \<phi> var \<equiv> valid \<phi> \<longrightarrow> valid (Forall var \<phi>)"

definition MP_holds :: "formula \<Rightarrow> formula \<Rightarrow> bool"
  where "MP_holds \<phi> \<psi> \<equiv> valid (\<phi> \<rightarrow> \<psi>) \<longrightarrow> valid \<phi> \<longrightarrow> valid \<psi>"
                                                                          
definition CT_holds :: "id \<Rightarrow> dterm \<Rightarrow> dterm \<Rightarrow> bool"
  where "CT_holds g \<theta> \<theta>' \<equiv> valid (Equals \<theta> \<theta>') 
    \<longrightarrow> valid (Equals (Function g (singleton \<theta>)) (Function g (singleton \<theta>')))"
                                                      
definition CQ_holds :: "id \<Rightarrow> dterm \<Rightarrow> dterm \<Rightarrow> bool"
  where "CQ_holds p \<theta> \<theta>' \<equiv> valid (Equals \<theta> \<theta>') 
    \<longrightarrow> valid ((Prop p (singleton \<theta>)) \<leftrightarrow> (Prop p (singleton \<theta>')))"
 
definition CE_holds :: "id \<Rightarrow> formula \<Rightarrow> formula \<Rightarrow> bool"                           
  where "CE_holds var \<phi> \<psi> \<equiv> valid (\<phi> \<leftrightarrow> \<psi>) 
    \<longrightarrow> valid (InContext var \<phi> \<leftrightarrow> InContext var \<psi>)"
 
definition diff_const_axiom :: "formula"
  where "diff_const_axiom \<equiv> Equals (Differential ($s f sempty)) (Simply (SConst 0))"

theorem test_valid: "valid test_axiom"
  apply(simp only: valid_def test_axiom_def)
  apply(auto)
done

lemma li_zero_case: "loop_semantics I \<alpha> 0 = {(\<nu>, \<nu>) | \<nu>. \<nu> = \<nu>}"
  apply(auto)
done

lemma or_semantics [simp]:
  "fml_semantics I (Or \<phi> \<psi>) = fml_semantics I \<phi> \<union> fml_semantics I \<psi>"
  apply(auto)
done

lemma iff_semantics [simp]: "(\<nu> \<in> fml_semantics I (A \<leftrightarrow> B)) 
  \<longleftrightarrow> ((\<nu> \<in> fml_semantics I A) \<longleftrightarrow> (\<nu> \<in> fml_semantics I B))"
  apply (auto)
done

lemma impl_semantics [simp]: "(\<nu> \<in> fml_semantics I (A \<rightarrow> B)) 
  = ((\<nu> \<in> fml_semantics I A) \<longrightarrow> (\<nu> \<in> fml_semantics I B))"
  apply (auto)
done

lemma equals_semantics [simp]: "(\<nu> \<in> fml_semantics I (Equals \<theta> \<theta>')) 
  = (dterm_semantics I \<theta> \<nu> = dterm_semantics I \<theta>' \<nu>)"
  apply(auto)
done

lemma diamond_semantics [simp]: "fml_semantics I (Diamond \<alpha> \<phi>)
  = {\<nu>. \<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_semantics I \<alpha> \<and> \<omega> \<in> fml_semantics I \<phi>}"
  apply(auto)
done

lemma iff_to_impl: "((\<nu> \<in> fml_semantics I A) \<longleftrightarrow> (\<nu> \<in> fml_semantics I B))
  \<longleftrightarrow> (((\<nu> \<in> fml_semantics I A) \<longrightarrow> (\<nu> \<in> fml_semantics I B)) 
     \<and> ((\<nu> \<in> fml_semantics I B) \<longrightarrow> (\<nu> \<in> fml_semantics I A)))"
apply (auto)
done

lemma vec_extensionality:"(\<forall>i. v$i = w$i) \<Longrightarrow> (v = w)"
  apply(simp add: vec_eq_iff)
 done
 
lemma proj_sing1:"(singleton \<theta> x) = \<theta>"
apply(auto simp add: singleton_def x_def)
done

lemma proj_sing2:"x \<noteq> y  \<Longrightarrow> (singleton \<theta> y) = Simply (SConst 0)"
apply(auto simp add: singleton_def x_def)
done

lemma assign_lem1:
"dterm_semantics I (if i = finite_5.a\<^sub>1 then $\<theta> x else Simply (SConst 0))
                   (vec_lambda (\<lambda>y. if x = y then Functions I f 
  (vec_lambda (\<lambda>i. dterm_semantics I (dl.empty i) \<nu>)) else  vec_nth (fst \<nu>) y), snd \<nu>)
=
 dterm_semantics I (if i = finite_5.a\<^sub>1 then $f f dl.empty else Simply (SConst 0)) \<nu>
"
 apply(case_tac "i = x")
 apply(auto simp add: proj_sing1) 
 done

lemma assign_lem:
"dterm_semantics I (singleton ($\<theta> x) i)
   (vec_lambda (\<lambda>y. if y = x  then Functions I f (vec_lambda (\<lambda>i. dterm_semantics I (dl.empty i) \<nu>)) else vec_nth (fst \<nu>) y), snd \<nu>)
                   =
 dterm_semantics I (singleton ($f f dl.empty) i) \<nu>"
 apply(case_tac "i = x ")
 apply(auto simp add: proj_sing1) 
 done
  
theorem assign_valid: "valid assign_axiom"
  apply(simp only: valid_def assign_axiom_def)
  apply(rule allI | rule impI)+
  apply(simp only: iff_semantics fml_semantics.simps mem_Collect_eq prog_semantics.simps)
  apply(simp)
  apply(simp only: assign_lem1)
  done

lemma mem_to_nonempty: "\<omega> \<in> S \<Longrightarrow> (S \<noteq> {})"
apply (auto)
done

lemma loop_forward: "\<nu> \<in> fml_semantics I ([[$\<alpha> a**]]Predicational PP) 
  \<longrightarrow> \<nu> \<in> fml_semantics I (Predicational PP&&[[$\<alpha> a]][[$\<alpha> a**]]Predicational PP)"
  apply(rule impI)
  apply(simp)
  apply(auto)
  apply(metis (mono_tags, lifting) li_zero_case mem_Collect_eq surj_pair)
  apply(metis (mono_tags, lifting) loop_semantics.simps(2) mem_Collect_eq
        prog_semantics.simps(1))
done
  
lemma nat_case: "\<forall>n::nat. (n = 0) \<or> (\<exists>m. n = Suc m)"
  apply(rule Nat.nat.nchotomy)
  done
  
lemma loop_semantics_case: "(\<nu>, \<omega>) \<in> loop_semantics I \<alpha> n \<longrightarrow> (\<nu> = \<omega>) 
  \<or> (\<exists>m. \<exists>\<mu>. (n = Suc m) \<and> (\<nu>, \<mu>) \<in> prog_semantics I \<alpha> 
     \<and> (\<mu>, \<omega>) \<in> loop_semantics I \<alpha> m)"
  apply(induct n)
  apply(simp)
  apply(rule impI)
  apply(auto)
done
  
lemma loop_backward: 
 "\<nu> \<in> fml_semantics I (Predicational PP && [[$\<alpha> a]][[$\<alpha> a**]]Predicational PP) 
  \<longrightarrow> \<nu> \<in> fml_semantics I ([[$\<alpha> a**]]Predicational PP)"
  apply(rule impI)
  apply(simp)
  apply(erule conjE)
  apply(rule allI)
  apply(auto)
  apply(metis loop_semantics_case prod.collapse prog_semantics.simps(1))
  done
  
theorem loop_valid: "valid loop_iterate_axiom"
  apply(simp only: valid_def loop_iterate_axiom_def)
  apply(simp only: iff_semantics)
  apply(simp only: HOL.iff_conv_conj_imp)
  apply(rule allI | rule impI)+
  apply(rule conjI)
  apply(rule loop_forward)
  apply(rule loop_backward)
done

theorem box_valid: "valid box_axiom"
  apply(simp only: valid_def box_axiom_def)
  apply(rule allI)+
  apply(simp only: iff_semantics)
  apply(simp)
done
  
theorem choice_valid: "valid choice_axiom"
  apply(simp only: valid_def choice_axiom_def)
  apply(auto)
done

theorem K_valid: "valid Kaxiom"
  apply(simp only: valid_def Kaxiom_def)
  apply(rule allI)+
  apply(simp only: impl_semantics)
  apply(rule impI)+
  apply(simp only: fml_semantics.simps prog_semantics.simps 
        impl_semantics mem_Collect_eq)
  apply(rule allI)  
  apply(auto)
done

theorem I_valid: "valid Iaxiom"
  apply(simp only: valid_def Iaxiom_def fml_semantics.simps 
    prog_semantics.simps iff_semantics impl_semantics mem_Collect_eq)
  apply(rule allI | rule impI)+
sorry
  
theorem V_valid: "valid Vaxiom"
  apply(simp only: valid_def Vaxiom_def impl_semantics)
  apply(rule allI | rule impI)+
  apply(auto simp add: dl.empty_def)
done

theorem G_sound: "G_holds \<phi> \<alpha>"
  apply(simp add: G_holds_def valid_def)
done
  
theorem Skolem_sound: "Skolem_holds \<phi> var"
  apply(simp add: Skolem_holds_def valid_def)
done
  
theorem MP_sound: "MP_holds \<phi> \<psi>"
  apply(simp only: MP_holds_def valid_def)
  apply(auto)
done
  
lemma CT_lemma:"\<And>I a b. \<forall>I. is_interp I \<longrightarrow> (\<forall>a b. dterm_semantics I \<theta> (a, b) = dterm_semantics I \<theta>' (a, b)) \<Longrightarrow>
             is_interp I \<Longrightarrow>
             Functions I var (vec_lambda (\<lambda>i. dterm_semantics I (if i = a\<^sub>1 then \<theta> else Simply (SConst 0)) (a, b))) =
             Functions I var (vec_lambda (\<lambda>i. dterm_semantics I (if i = a\<^sub>1 then \<theta>' else Simply (SConst 0)) (a, b)))"
proof -
  fix I :: interp and a :: "(real, Enum.finite_5) vec" and b :: "(real, Enum.finite_5) vec"
  assume a1: "is_interp I"
  assume "\<forall>I. is_interp I \<longrightarrow> (\<forall>a b. dterm_semantics I \<theta> (a, b) = dterm_semantics I \<theta>' (a, b))"
  then have "\<forall>f. dterm_semantics I (if f = a\<^sub>1 then \<theta>' else Simply (SConst 0)) (a, b) = dterm_semantics I (if f = a\<^sub>1 then \<theta> else Simply (SConst 0)) (a, b)"
    using a1 by presburger
  then show "Functions I var (vec_lambda (\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta> else Simply (SConst 0)) (a, b)))
 = Functions I var (vec_lambda (\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta>' else Simply (SConst 0)) (a, b)))"
    by presburger
qed

theorem CT_sound: "CT_holds var \<theta> \<theta>'"
  apply(simp only: CT_holds_def valid_def equals_semantics vec_extensionality vec_eq_iff)
  apply(simp)
  apply(rule allI | rule impI)+
  apply(simp add: CT_lemma)
  done
  
lemma CQ_lemma:"\<And>I \<nu>. \<forall>I \<nu>. is_interp I \<longrightarrow> dterm_semantics I \<theta> \<nu> = dterm_semantics I \<theta>' \<nu> \<Longrightarrow>
           is_interp I \<Longrightarrow>
           Predicates I var (vec_lambda(\<lambda>i. dterm_semantics I (if i = a\<^sub>1 then \<theta> else Simply (SConst 0)) \<nu>)) =
           Predicates I var (vec_lambda(\<lambda>i. dterm_semantics I (if i = a\<^sub>1 then \<theta>' else Simply (SConst 0)) \<nu>))"
proof -
  fix I :: interp and \<nu> :: "(real, Enum.finite_5) vec \<times> (real, Enum.finite_5) vec"
  assume a1: "\<forall>I \<nu>. is_interp I \<longrightarrow> dterm_semantics I \<theta> \<nu> = dterm_semantics I \<theta>' \<nu>"
  assume a2: "is_interp I"
  obtain ff :: "(Enum.finite_5 \<Rightarrow> real) \<Rightarrow> (Enum.finite_5 \<Rightarrow> real) \<Rightarrow> Enum.finite_5" where
    f3: "\<forall>f fa. f (ff fa f) \<noteq> fa (ff fa f) \<or> vec_lambda f = vec_lambda fa"
    by (meson Cart_lambda_cong)
  have "dterm_semantics I \<theta> \<nu> = dterm_semantics I \<theta>' \<nu> "
    using a2 a1 by blast
  then have "dterm_semantics I (if ff (\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta>' else Simply (SConst 0)) \<nu>) (\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta> else Simply (SConst 0)) \<nu>) = a\<^sub>1 then \<theta> else Simply (SConst 0)) \<nu> \<noteq> dterm_semantics I (if ff (\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta>' else Simply (SConst 0)) \<nu>) (\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta> else Simply (SConst 0)) \<nu>) = a\<^sub>1 then \<theta>' else Simply (SConst 0)) \<nu> \<longrightarrow> dterm_semantics I (if ff (\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta>' else Simply (SConst 0)) \<nu>) (\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta> else Simply (SConst 0)) \<nu>) = a\<^sub>1 then \<theta> else Simply (SConst 0)) \<nu> = dterm_semantics I (if ff (\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta>' else Simply (SConst 0)) \<nu>) (\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta> else Simply (SConst 0)) \<nu>) = a\<^sub>1 then \<theta>' else Simply (SConst 0)) \<nu>"
    by simp
  then have "(vec_lambda(\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta> else Simply (SConst 0)) \<nu>)) = (vec_lambda(\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta>' else Simply (SConst 0)) \<nu>))"
    using f3 by meson
  then show "Predicates I var (vec_lambda(\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta> else Simply (SConst 0)) \<nu>)) = Predicates I var (vec_lambda(\<lambda>f. dterm_semantics I (if f = a\<^sub>1 then \<theta>' else Simply (SConst 0)) \<nu>))"
    by presburger
qed 

theorem CQ_sound: "CQ_holds var \<theta> \<theta>'"
  apply(simp only: CQ_holds_def valid_def equals_semantics vec_extensionality vec_eq_iff)
  apply(rule allI | rule impI)+
  apply(simp only: iff_semantics singleton.simps fml_semantics.simps mem_Collect_eq)
  apply(simp only: CQ_lemma)
done
  
theorem CE_sound: "CE_holds var \<phi> \<psi>"
  apply(simp only: CE_holds_def valid_def iff_semantics)
  apply(rule impI)
  apply(rule allI)
  apply(rule allI)
  apply(simp)
  apply(metis subsetI subset_antisym surj_pair)
done

lemma constant_deriv_inner:
 assumes interp:"\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x)"
 shows "FunctionFrechet I f (vec_lambda (\<lambda>i. sterm_semantics I (sempty i) (fst \<nu>))) (vec_lambda(\<lambda>i. frechet I (sempty i) (fst \<nu>) (snd \<nu>)))= 0"
  proof -

    have empty_zero:"(vec_lambda(\<lambda>i. frechet I (sempty i) (fst \<nu>) (snd \<nu>))) = 0"
    using sempty_def Cart_lambda_cong frechet.simps(5) zero_vec_def
    by fastforce
    let ?x = "(vec_lambda (\<lambda>i. sterm_semantics I (sempty i) (fst \<nu>)))"
    from interp 
    have has_deriv:"(Functions I f has_derivative FunctionFrechet I f ?x) (at ?x)"
    by auto
    then have f_linear:"linear (FunctionFrechet I f ?x)"
    using Deriv.has_derivative_linear by auto
    then 
    show ?thesis using empty_zero f_linear Linear_Algebra.linear_0 by (auto)
  qed

lemma constant_deriv_zero:"is_interp I \<Longrightarrow> directional_derivative I ($s f sempty) \<nu> = 0"
  apply(simp only: is_interp_def directional_derivative.simps frechet.simps 
        frechet_correctness)
  apply(rule constant_deriv_inner)
  apply(auto)
done

theorem diff_const_axiom_valid: "valid diff_const_axiom"
  apply(simp only: valid_def diff_const_axiom_def equals_semantics)
  apply(rule allI | rule impI)+
  apply(simp only:  dterm_semantics.simps 
        constant_deriv_zero sterm_semantics.simps)
  done

section \<open>Unused Lemmas\<close>

lemma sum_unique_nonzero:
 fixes i::id and f::"id \<Rightarrow> real"
 assumes restZero:"\<And>j. j\<in>(UNIV::id set) \<Longrightarrow> j \<noteq> i \<Longrightarrow> f j = 0" 
 shows "(\<Sum>j\<in>(UNIV::id set). f j) = f i"
 proof -
   let ?U = "UNIV :: id set"
   let ?A = "{k \<in> ?U. k = i}"
   let ?B = "{k \<in> ?U. \<not>(k = i)}"
   have finA:"finite ?A" by auto
   have finB:"finite ?B" by auto
   have emptyInter: "?A \<inter> ?B = {}" by auto
   from emptyInter 
   have zeroInter:"(\<Sum>j \<in> (?A \<inter> ?B). f j) = 0" 
   by (auto)
   have union_univ:"?U = ?A \<union> ?B " by (auto)
   from union_univ
   have partition:"(\<Sum>j \<in> ?U. (f j)) = (\<Sum>j \<in> ?A \<union> ?B. (f j))"
   by (auto)
   from finA finB
   have union_sum:"(\<Sum>j \<in> ?A \<union> ?B. (f j)) = 
     (\<Sum>j \<in> ?A. (f j)) + (\<Sum>j \<in> ?B. (f j)) - (\<Sum>j \<in> (?A \<inter> ?B). (f j))"
   by (rule setsum_Un)
   from restZero
   have Bzero:"(\<Sum>j \<in> ?B. (f j)) = 0" by (auto)
   have Asingle:"(\<Sum>j \<in> ?A. (f j)) = f i" by (auto)
   from partition union_sum zeroInter Bzero Asingle 
   show ?thesis by auto
 qed
end