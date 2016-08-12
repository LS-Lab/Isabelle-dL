theory Syntax
imports
  Complex_Main HOL
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
  "./Ids"
begin 
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
| Exists 'c "('a, 'b, 'c) formula"
| Diamond "('a, 'b, 'c) hp" "('a, 'b, 'c) formula"         ("(\<langle> _ \<rangle> _)" 10)
(* DiffFormula \<phi> gives us the invariant for proving \<phi> by differential induction. *)
| DiffFormula "('a, 'b, 'c) formula"
(* Unary quantifier symbols *)
| InContext 'b "('a, 'b, 'c) formula"
  
  
(* Derived forms *)
definition Or :: "('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" (infixl "||" 7)
  where "Or P Q = Not (And (Not P) (Not Q))"

definition Implies :: "('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" (infixr "\<rightarrow>" 10)
  where "Implies P Q = Or Q (Not P)"

definition Equiv :: "('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" (infixl "\<leftrightarrow>" 10)
  where "Equiv P Q = Or (And P Q) (And (Not P) (Not Q))"

definition Forall :: "'c \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula"
  where "Forall x P = Not (Exists x (Not P))"

definition Equals :: "('a, 'c) trm \<Rightarrow> ('a, 'c) trm \<Rightarrow> ('a, 'b, 'c) formula"
  where "Equals \<theta> \<theta>' = ((Geq \<theta> \<theta>') && (Geq \<theta>' \<theta>))"

definition Box :: "('a, 'b, 'c) hp \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" ("([[_]]_)" 10)
  where "Box \<alpha> P = Not (Diamond \<alpha> (Not P))"
  
(* Definite predicational as a context with a constant argument (e.g. constant true *)
fun Predicational :: "'b \<Rightarrow> ('a, 'b, 'c) formula"
  where "Predicational P = InContext P (Geq (Const 0) (Const 0))"

(* Arguments for a "nullary" function - a tuple of all-zeros. When we encode
  a function that has less than the maximum allowed number of arguments, we
  do so by making the remaining arguments 0 at every use site. We can't actually
  enforce that the interpretation of the function "doesnt care" about an argument,
  but if we never use that argument at more than one value there's no way to "notice"
  that the extra arguments exist *)
context ids begin

definition empty::" 'sz \<Rightarrow> ('sf, 'sz) trm"
  where "empty \<equiv> \<lambda>i.(Const 0)"

(* Function argument tuple where the first argument is arbitrary and the rest are zero.*)
fun singleton :: "('sf, 'sz) trm \<Rightarrow> ('sz \<Rightarrow> ('sf, 'sz) trm)"
  where "singleton t i = (if i = vid1 then t else (Const 0))"

(* Equivalents of the above for functions over simple terms. *)
definition sempty :: "('sz \<Rightarrow> ('sf, 'sz) trm)"
  where "sempty _ \<equiv> (Const 0)"

fun ssingleton :: "('sf, 'sz) trm \<Rightarrow> ('sz \<Rightarrow> ('sf, 'sz) trm)"
  where "ssingleton t var = (if var = vid1 then t else (Const 0))"

definition f1::"'sf \<Rightarrow> 'sz \<Rightarrow> ('sf,'sz) trm"
  where "f1 f x = Function f (singleton (Var x))"

definition f0::"'sf \<Rightarrow> ('sf,'sz) trm"
  where "f0 f = Function f empty"

definition p1::"'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sc, 'sz) formula"
  where "p1 p x = Prop p (singleton (Var x))"

definition P::"'sc \<Rightarrow> ('sf, 'sc, 'sz) formula"
  where "P p = Predicational p"
end

(* Well-formedness predicates *)
inductive dfree :: "('a, 'c) trm \<Rightarrow> bool"
where
  dfree_Var: "dfree (Var i)"
| dfree_Const: "dfree (Const r)"
| dfree_Fun: "(\<And>i. dfree (args i)) \<Longrightarrow> dfree (Function i args)"
| dfree_Plus: "dfree \<theta>\<^sub>1 \<Longrightarrow> dfree \<theta>\<^sub>2 \<Longrightarrow> dfree (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dfree_Times: "dfree \<theta>\<^sub>1 \<Longrightarrow> dfree \<theta>\<^sub>2 \<Longrightarrow> dfree (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"
  
inductive dsafe :: "('a, 'c) trm \<Rightarrow> bool"
where
  dsafe_Var: "dsafe (Var i)"
| dsafe_Const: "dsafe (Const r)"
| dsafe_Fun: "(\<And>i. dsafe (args i)) \<Longrightarrow> dsafe (Function i args)"
| dsafe_Plus: "dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Times: "dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Diff: "dfree \<theta> \<Longrightarrow> dsafe (Differential \<theta>)"
| dsafe_DiffVar: "dsafe ($' i)"

(* Explictly-written variables that are bound by the ODE. Needed to compute whether
 * ODE's are valid (e.g. whether they bind the same variable twice) *)
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
| "ffree p \<Longrightarrow> ffree (Exists x p)"
| "hpfree a \<Longrightarrow> ffree p \<Longrightarrow> ffree (Diamond a p)"
| "ffree (Predicational P)"
| "dfree t1 \<Longrightarrow> dfree t2 \<Longrightarrow> ffree (Geq t1 t2)"

inductive hpsafe:: "('a, 'b, 'c) hp \<Rightarrow> bool"
and fsafe:: "('a, 'b, 'c) formula \<Rightarrow> bool"
where
   hpsafe_Pvar:"hpsafe (Pvar x)"
 | hpsafe_Assign:"dsafe e \<Longrightarrow> hpsafe (Assign x e)"
 | hpsafe_DiffAssign:"dsafe e \<Longrightarrow> hpsafe (DiffAssign x e)"
 | hpsafe_Test:"fsafe P \<Longrightarrow> hpsafe (Test P)" 
 | hpsafe_Evolve:"osafe ODE \<Longrightarrow> fsafe P \<Longrightarrow> hpsafe (EvolveODE ODE P)"
 | hpsafe_Choice:"hpsafe a \<Longrightarrow> hpsafe b \<Longrightarrow> hpsafe (Choice a b )"
 | hpsafe_Sequence:"hpsafe a \<Longrightarrow> hpsafe b \<Longrightarrow> hpsafe (Sequence a b)"
 | hpsafe_Loop:"hpsafe a \<Longrightarrow> hpsafe (Loop a)"

 | fsafe_Geq:"dsafe t1 \<Longrightarrow> dsafe t2 \<Longrightarrow> fsafe (Geq t1 t2)"
 | fsafe_Prop:"(\<And>i. dsafe (args i)) \<Longrightarrow> fsafe (Prop p args)"
 | fsafe_Not:"fsafe p \<Longrightarrow> fsafe (Not p)"
 | fsafe_And:"fsafe p \<Longrightarrow> fsafe q \<Longrightarrow> fsafe (And p q)"
 | fsafe_Exists:"fsafe p \<Longrightarrow> fsafe (Exists x p)"
 | fsafe_Diamond:"hpsafe a \<Longrightarrow> fsafe p \<Longrightarrow> fsafe (Diamond a p)"
 | fsafe_DiffFormula:"ffree p \<Longrightarrow> fsafe (DiffFormula p)"
 | fsafe_InContext:"fsafe f \<Longrightarrow> fsafe (InContext C f)"

(* Auto-generated simplifier rules for safety predicates *)  
inductive_simps
      dfree_Plus_simps[simp]: "dfree (Plus a b)"
  and dfree_Times_simps[simp]: "dfree (Times a b)"
  and dfree_Var_simps[simp]: "dfree (Var x)"
  and dfree_Fun_simps[simp]: "dfree (Function i args)"

inductive_simps
      dsafe_Plus_simps[simp]: "dsafe (Plus a b)"
  and dsafe_Times_simps[simp]: "dsafe (Times a b)"
  and dsafe_Var_simps[simp]: "dsafe (Var x)"
  and dsafe_Fun_simps[simp]: "dsafe (Function i args)"
  and dsafe_Diff_simps[simp]: "dsafe (Differential a)"

(* Basic reasoning principles about syntactic constructs, including inductive principles *)
lemma dfree_is_dsafe: "dfree \<theta> \<Longrightarrow> dsafe \<theta>"
  by (induction rule: dfree.induct) (auto intro: dsafe.intros)
  
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

lemma fml_induct:
"(\<And>t1 t2. P (Geq t1 t2))
\<Longrightarrow> (\<And>p args. P (Prop p args))
\<Longrightarrow> (\<And>p. P p \<Longrightarrow> P (Not p))
\<Longrightarrow> (\<And>p q. P p \<Longrightarrow> P q \<Longrightarrow> P (And p q))
\<Longrightarrow> (\<And>x p. P p \<Longrightarrow> P (Exists x p))
\<Longrightarrow> (\<And>a p. P p \<Longrightarrow> P (Diamond a p))
\<Longrightarrow> (\<And>p. P p \<Longrightarrow> P (DiffFormula p))
\<Longrightarrow> (\<And>C p. P p \<Longrightarrow> P (InContext C p))
\<Longrightarrow> P \<phi>"
  by (induction rule: formula.induct) (auto)

context ids begin
lemma proj_sing1:"(singleton \<theta> vid1) = \<theta>"
  by (auto simp add: singleton.simps)

lemma proj_sing2:"vid1 \<noteq> y  \<Longrightarrow> (singleton \<theta> y) = (Const 0)"
  by (auto simp add: singleton_def)
end

end