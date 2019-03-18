theory Syntax
imports
  Complex_Main
  Word_Lib.Word_Lib
  Word_Lib.Word_Lemmas
  "./Ids"
begin 
section \<open>Syntax\<close>
text \<open>
  We define the syntax of dL terms, formulas and hybrid programs. As in
  CADE'15, the syntax allows arbitrarily nested differentials. However, 
  the semantics of such terms is very surprising (e.g. (x')' is zero in
  every state), so we define predicates dfree and dsafe to describe terms
  with no differentials and no nested differentials, respectively.

  In keeping with the CADE'15 presentation we currently make the simplifying
  assumption that all terms are smooth, and thus division and arbitrary
  exponentiation are absent from the syntax. Several other standard logical
  constructs are implemented as derived forms to reduce the soundness burden.
  
  The types of formulas and programs are parameterized by three finite types 
  ('a, 'b, 'c) used as identifiers for function constants, context constants, and
  everything else, respectively. These type variables are distinct because some
  substitution operations affect one type variable while leaving the others unchanged.
  Because these types will be finite in practice, it is more useful to think of them
  as natural numbers that happen to be represented as types (due to HOL's lack of dependent types).
  The types of terms and ODE systems follow the same approach, but have only two type 
  variables because they cannot contain contexts.
\<close>
type_synonym word = "32 Word.word"

definition NEG_INF::"word"
where "NEG_INF = -((2 ^ 31) -1)"

definition POS_INF::"word"
where "POS_INF = (2^31) - 1"

typedef bword = "{n::word. sint n \<ge> sint NEG_INF \<and> sint n \<le> sint POS_INF}"
  apply(rule exI[where x=NEG_INF])
  by (auto simp add: NEG_INF_def POS_INF_def)



(* Numeric literals *)
type_synonym lit = bword
      
setup_lifting type_definition_bword

lift_definition bword_zero::"bword" is "0::32 Word.word"
  by(auto simp add: POS_INF_def NEG_INF_def)

lift_definition bword_one::"bword" is "1::32 Word.word"
  by(auto simp add: POS_INF_def NEG_INF_def)

lift_definition bword_neg_one::"bword" is "-1::32 Word.word"
    by(auto simp add: POS_INF_def NEG_INF_def)

datatype ('a, 'c) trm =
(* Real-valued variables given meaning by the state and modified by programs. *)
  Var 'c
| Const lit
(* A function (applied to its arguments) consists of an identifier for the function
 * and a function 'c \<Rightarrow> ('a, 'c) trm (where 'c is a finite type) which specifies one
 * argument of the function for each element of type 'c. To simulate a function with
 * less than 'c arguments, set the remaining arguments to a constant, such as Const 0*)
| Function 'a "'c \<Rightarrow> ('a, 'c) trm" ("$f")
(* A functional is analogous to a function, but can depend on ALL state variables*)
| Functional 'a ("$$F")
(* A functional that can depend only on base variables and thus is differentiable*)
(*| DFunctional 'a ("$$F'")*)
| Plus "('a, 'c) trm" "('a, 'c) trm"
| Times "('a, 'c) trm" "('a, 'c) trm"
| Div "('a, 'c) trm" "('a, 'c) trm"
| Neg "('a, 'c) trm"
| Max "('a, 'c) trm" "('a, 'c) trm"
| Min "('a, 'c) trm" "('a, 'c) trm"
| Abs "('a, 'c) trm"
(* A (real-valued) variable standing for a differential, such as x', given meaning by the state
 * and modified by programs. *)
| DiffVar 'c ("$'") 
(* The differential of an arbitrary term (\<theta>)' *)
| Differential "('a, 'c) trm"

type_synonym 'c space  = "'c option"

definition All ::"'c space" where Space_All_def[simp]:"All = None"
definition NB ::"'c \<Rightarrow> 'c space" where Space_NB_def[simp]:"NB = Some"
(*
datatype 'c space =
  All
| NB 'c (* one variable not-bound *)*)

datatype('a, 'c) ODE =
(* Variable standing for an ODE system, given meaning by the interpretation *)
  OVar 'c "'c space"
(* Singleton ODE defining x' = \<theta>, where \<theta> may or may not contain x
 * (but must not contain differentials) *)
| OSing 'c "('a, 'c) trm"
(* The product OProd ODE1 ODE2 composes two ODE systems in parallel, e.g. 
 * OProd (x' = y) (y' = -x) is the system {x' = y, y' = -x} *)
| OProd "('a, 'c) ODE" "('a, 'c) ODE"

fun oprod::"('a,'c) ODE \<Rightarrow> ('a,'c) ODE \<Rightarrow> ('a,'c) ODE"
  where "oprod (OSing x t) ODE2 = (OProd (OSing x t) ODE2)"
  | "oprod (OVar c d) ODE2 = (OProd (OVar c d) ODE2)"
  | "oprod (OProd ll lr) ODE2 = oprod ll (oprod lr  ODE2)"

lemma oprod_induct:
  fixes l r::"('a,'c)ODE" and P::"('a,'c)ODE \<Rightarrow> ('a,'c)ODE \<Rightarrow> bool"
  assumes BC1:"(\<And>x t ODE2. P (OSing x t) ODE2)"
  assumes BC2:"(\<And>c d ODE2. (P (OVar c d) ODE2))"
  assumes  IH:"\<And>l1 l2 x. (\<And>x. P l1 x) \<Longrightarrow> (\<And>x. P l2 x) \<Longrightarrow> P (OProd l1 l2) x"
  shows "P l r"
  apply(induction l arbitrary:r)
    apply(rule BC2)
   apply(rule BC1)
  by(rule IH)



datatype ('a, 'b, 'c) hp =
(* Variables standing for programs, given meaning by the interpretation. *)
  Pvar 'c                           ("$\<alpha>")
(* Assignment to a real-valued variable x := \<theta> *)
| Assign 'c "('a, 'c) trm"                (infixr ":=" 10)
(* Nondeterministic assignment to a real-valued variable x := * *)
| AssignAny 'c                
(* Assignment to a differential variable*)
| DiffAssign 'c "('a, 'c) trm"
(* Program ?\<phi> succeeds iff \<phi> holds in current state. *)
| Test "('a, 'b, 'c) formula"                 ("?")
(* An ODE program is an ODE system with some evolution domain. *)
| EvolveODE "('a, 'c) ODE" "('a, 'b, 'c) formula"
(* Non-deterministic choice between two programs a and b *)
| Choice "('a, 'b, 'c) hp" "('a, 'b, 'c) hp"            (infixl "\<union>\<union>" 10)
(* Sequential composition of two programs a and b *)
| Sequence "('a, 'b, 'c) hp"  "('a, 'b, 'c) hp"         (infixr ";;" 8)
(* Nondeterministic repetition of a program "a", zero or more times. *)
| Loop "('a, 'b, 'c) hp"                      ("_**")

and ('a, 'b, 'c) formula =
  Geq "('a, 'c) trm" "('a, 'c) trm"
| Prop 'c "'c \<Rightarrow> ('a, 'c) trm"      ("$\<phi>")
| Not "('a, 'b, 'c) formula"            ("!")
| And "('a, 'b, 'c) formula" "('a, 'b, 'c) formula"    (infixl "&&" 8)
| Exists 'c "('a, 'b, 'c) formula"
(* \<langle>\<alpha>\<rangle>\<phi> iff exists run of \<alpha> where \<phi> is true in end state *)
| Diamond "('a, 'b, 'c) hp" "('a, 'b, 'c) formula"         ("(\<langle> _ \<rangle> _)" 10)
(* Contexts C are symbols standing for functions from (the semantics of) formulas to 
 * (the semantics of) formulas, thus C(\<phi>) is another formula. While not necessary
 * in terms of expressiveness, contexts allow for more efficient reasoning principles. *)
| InContext 'b "('a, 'b, 'c) formula"
    
(* Derived forms *)
definition DFunl :: "'a \<Rightarrow> ('a,'c) trm"
  where "DFunl fid = Function fid Var"

definition DPredl :: "'c \<Rightarrow> ('a,'b,'c) formula"
  where "DPredl fid = Prop fid Var"

definition Minus :: "('a,'c) trm \<Rightarrow> ('a,'c) trm \<Rightarrow> ('a,'c) trm" 
  where "Minus \<theta>\<^sub>1 \<theta>\<^sub>2 = Plus \<theta>\<^sub>1 (Neg \<theta>\<^sub>2)"

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

definition NotEquals :: "('a, 'c) trm \<Rightarrow> ('a, 'c) trm \<Rightarrow> ('a, 'b, 'c) formula"
where "NotEquals \<theta> \<theta>' = Not((Geq \<theta> \<theta>') && (Geq \<theta>' \<theta>))"

definition Greater :: "('a, 'c) trm \<Rightarrow> ('a, 'c) trm \<Rightarrow> ('a, 'b, 'c) formula"
where "Greater \<theta> \<theta>' = ((Geq \<theta> \<theta>') && (Not (Geq \<theta>' \<theta>)))"

definition Less :: "('a, 'c) trm \<Rightarrow> ('a, 'c) trm \<Rightarrow> ('a, 'b, 'c) formula"
  where "Less \<theta> \<theta>' = ((Geq \<theta>' \<theta>) && (Not (Geq \<theta> \<theta>')))"

definition Le ::  "('a, 'c) trm \<Rightarrow> ('a, 'c) trm \<Rightarrow> ('a, 'b, 'c) formula" where "Le = Less"
definition Ge ::  "('a, 'c) trm \<Rightarrow> ('a, 'c) trm \<Rightarrow> ('a, 'b, 'c) formula" where "Ge = Greater"

definition Leq :: "('a, 'c) trm \<Rightarrow> ('a, 'c) trm \<Rightarrow> ('a, 'b, 'c) formula"
  where "Leq \<theta> \<theta>' = (Geq \<theta>' \<theta>)"

definition Box :: "('a, 'b, 'c) hp \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" ("([[_]]_)" 10)
where "Box \<alpha> P = Not (Diamond \<alpha> (Not P))"
  
definition TT ::"('a,'b,'c) formula" 
where "TT = Geq (Const (bword_zero)) (Const (bword_zero))"

definition FF ::"('a,'b,'c) formula" 
where "FF = Geq (Const (bword_zero)) (Const (bword_one))"


type_synonym ('a,'b,'c) sequent = "('a,'b,'c) formula list * ('a,'b,'c) formula list"
(* Rule: assumptions, then conclusion *)
type_synonym ('a,'b,'c) rule = "('a,'b,'c) sequent list * ('a,'b,'c) sequent"

  
(* silliness to enable proving disequality lemmas *)
primrec sizeF::"('sf,'sc, 'sz) formula \<Rightarrow> nat"
  and   sizeP::"('sf,'sc, 'sz) hp \<Rightarrow> nat"
where 
  "sizeP (Pvar a) = 1"
| "sizeP (Assign x \<theta>) = 1"
| "sizeP (AssignAny _) = 1"
| "sizeP (DiffAssign x \<theta>) = 1"
| "sizeP (Test \<phi>) = Suc (sizeF \<phi>)"
| "sizeP (EvolveODE ODE \<phi>) = Suc (sizeF \<phi>)"
| "sizeP (Choice \<alpha> \<beta>) = Suc (sizeP \<alpha> + sizeP \<beta>)"
| "sizeP (Sequence \<alpha> \<beta>) = Suc (sizeP \<alpha> + sizeP \<beta>)"
| "sizeP (Loop \<alpha>) = Suc (sizeP \<alpha>)"
| "sizeF (Geq p q) = 1"
| "sizeF (Prop p args) = 1"
| "sizeF (Not p) = Suc (sizeF p)"
| "sizeF (And p q) = sizeF p + sizeF q"
| "sizeF (Exists x p) = Suc (sizeF p)"
| "sizeF (Diamond p q) = Suc (sizeP p + sizeF q)"
| "sizeF (InContext C \<phi>) = Suc (sizeF \<phi>)"

lemma sizeF_diseq:"sizeF p \<noteq> sizeF q \<Longrightarrow> p \<noteq> q" by auto
  
named_theorems "expr_diseq" "Structural disequality rules for expressions"  
lemma [expr_diseq]:"p \<noteq> And p q" by(induction p, auto)
lemma [expr_diseq]:"q \<noteq> And p q" by(induction q, auto)
lemma [expr_diseq]:"p \<noteq> Not p" by(induction p, auto)
lemma [expr_diseq]:"p \<noteq> Or p q" by(rule sizeF_diseq, auto simp add: Or_def)
lemma [expr_diseq]:"q \<noteq> Or p q" by(rule sizeF_diseq, auto simp add: Or_def)
lemma [expr_diseq]:"p \<noteq> Implies p q" by(rule sizeF_diseq, auto simp add: Implies_def Or_def)
lemma [expr_diseq]:"q \<noteq> Implies p q" by(rule sizeF_diseq, auto simp add: Implies_def Or_def)
lemma [expr_diseq]:"p \<noteq> Equiv p q" by(rule sizeF_diseq, auto simp add: Equiv_def Or_def)
lemma [expr_diseq]:"q \<noteq> Equiv p q" by(rule sizeF_diseq, auto simp add: Equiv_def Or_def)
lemma [expr_diseq]:"p \<noteq> Exists x p" by(induction p, auto)
lemma [expr_diseq]:"p \<noteq> Diamond a p" by(induction p, auto)
lemma [expr_diseq]:"p \<noteq> InContext C p" by(induction p, auto)

(* A predicational is like a context with no argument, i.e. a variable standing for a 
 * state-dependent formula, given meaning by the interpretation. This differs from a predicate
 * because predicates depend only on their arguments (which might then indirectly depend on the state).
 * We encode a predicational as a context applied to a formula whose truth value is constant with
 * respect to the state (specifically, always true)*)
fun Predicational :: "'b \<Rightarrow> ('a, 'b, 'c) formula" ("Pc")
where "Predicational P = InContext P (Geq (Const (bword_zero)) (Const (bword_zero)))"

(* Abbreviations for common syntactic constructs in order to make axiom definitions, etc. more
 * readable. *)
context ids begin
(* "Empty" function argument tuple, encoded as tuple where all arguments assume a constant value. *)
definition empty::" 'b \<Rightarrow> ('a, 'b) trm"
where "empty \<equiv> \<lambda>i.(Const (bword_zero))"

(* Function argument tuple with (effectively) one argument, where all others have a constant value. *)
fun singleton :: "('a, 'sz) trm \<Rightarrow> ('sz \<Rightarrow> ('a, 'sz) trm)"
where "singleton t i = (if i = vid1 then t else (Const (bword_zero)))"

lemma expand_singleton:"singleton t = (\<lambda>i. (if i = vid1 then t else (Const (bword_zero))))"
  by auto

(* Function applied to one argument *)
definition f1::"'sf \<Rightarrow> 'sz \<Rightarrow> ('sf,'sz) trm"
where "f1 f x = Function f (singleton (Var x))"

(* Function applied to zero arguments (simulates a constant symbol given meaning by the interpretation) *)
definition f0::"'sf \<Rightarrow> ('sf,'sz) trm"
where "f0 f = Function f empty"

(* Predicate applied to one argument *)
definition p1::"'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sc, 'sz) formula"
where "p1 p x = Prop p (singleton (Var x))"

(* Predicational *)
definition P::"'sc \<Rightarrow> ('sf, 'sc, 'sz) formula"
where "P p = Predicational p"
end

subsection \<open>Well-Formedness predicates\<close>
inductive dfree :: "('a, 'c) trm \<Rightarrow> bool"
where
  dfree_Var: "dfree (Var i)"
| dfree_Const: "dfree (Const r)"
| dfree_Fun: "(\<forall>i. dfree (args i)) \<Longrightarrow> dfree (Function i args)"
| dfree_Plus: "dfree \<theta>\<^sub>1 \<Longrightarrow> dfree \<theta>\<^sub>2 \<Longrightarrow> dfree (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dfree_Neg: "dfree \<theta> \<Longrightarrow> dfree (Neg \<theta>)"
| dfree_Times: "dfree \<theta>\<^sub>1 \<Longrightarrow> dfree \<theta>\<^sub>2 \<Longrightarrow> dfree (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"
(* regular functionals are not dfree because they can depend on differential state, that's what dfunctionals are for *)
(*| dfree_DFunctional: "dfree ($$F' fid)"*)
  
inductive dsafe :: "('a, 'c) trm \<Rightarrow> bool"
where
  dsafe_Var: "dsafe (Var i)"
| dsafe_Const: "dsafe (Const r)"
| dsafe_Fun: "(\<forall>i. dsafe (args i)) \<Longrightarrow> dsafe (Function i args)"
(* | dsafe_DFunl: "dsafe ($$F' i)" *)
| dsafe_Funl: "dsafe ($$F i)"
| dsafe_Neg: "dsafe \<theta> \<Longrightarrow> dsafe (Neg \<theta>)"
| dsafe_Plus: "dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Times: "dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Div: "dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Div \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Diff: "dfree \<theta> \<Longrightarrow> dsafe (Differential \<theta>)"
| dsafe_DiffVar: "dsafe ($' i)"
| dsafe_Max :"dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Max \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Min :"dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Min \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Abs :"dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe (Abs \<theta>\<^sub>1)"

inductive dexec :: "('a, 'c) trm \<Rightarrow> bool"
where
  dexec_Var: "dexec (Var i)"
| dexec_Const: "dexec (Const r)"
| dexec_Neg: "dexec \<theta> \<Longrightarrow> dexec (Neg \<theta>)"
| dexec_Plus: "dexec \<theta>\<^sub>1 \<Longrightarrow> dexec \<theta>\<^sub>2 \<Longrightarrow> dexec (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dexec_Times: "dexec \<theta>\<^sub>1 \<Longrightarrow> dexec \<theta>\<^sub>2 \<Longrightarrow> dexec (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dexec_Div: "dexec \<theta>\<^sub>1 \<Longrightarrow> dexec \<theta>\<^sub>2 \<Longrightarrow> dexec (Div \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dexec_Max :"dexec \<theta>\<^sub>1 \<Longrightarrow> dexec \<theta>\<^sub>2 \<Longrightarrow> dexec (Max \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dexec_Min :"dexec \<theta>\<^sub>1 \<Longrightarrow> dexec \<theta>\<^sub>2 \<Longrightarrow> dexec (Min \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dexec_Abs :"dexec \<theta>\<^sub>1 \<Longrightarrow> dexec (Abs \<theta>\<^sub>1)"


(* Explictly-written variables that are bound by the ODE. Needed to compute whether
 * ODE's are valid (e.g. whether they bind the same variable twice) *)
fun ODE_dom::"('a, 'c) ODE \<Rightarrow> 'c set"
where 
  "ODE_dom (OVar c d) =  {}"
| "ODE_dom (OSing x \<theta>) = {x}"
| "ODE_dom (OProd ODE1 ODE2) = ODE_dom ODE1 \<union> ODE_dom ODE2"

lemma ODE_dom_assoc:"ODE_dom (oprod ODE1 ODE2) = ODE_dom (OProd ODE1 ODE2)"
  apply(induction ODE1 arbitrary:ODE2)
  by(auto)

inductive osafe:: "('a, 'c) ODE \<Rightarrow> bool"
where
  osafe_Var:"osafe (OVar c d)"
| osafe_Sing:"dfree \<theta> \<Longrightarrow> osafe (OSing x \<theta>)"
| osafe_Prod:"osafe ODE1 \<Longrightarrow> osafe ODE2 \<Longrightarrow> ODE_dom ODE1 \<inter> ODE_dom ODE2 = {} \<Longrightarrow> osafe (OProd ODE1 ODE2)"

lemma osafe_assoc:
  fixes ODE1 ODE2
  shows "osafe (OProd ODE1 ODE2) = osafe (oprod ODE1 ODE2)"
proof -
  have lr:"osafe (OProd ODE1 ODE2) \<Longrightarrow> osafe (oprod ODE1 ODE2)"
    apply(induction ODE1 arbitrary:ODE2)
       apply(auto)
    by (metis (no_types, lifting) ODE.distinct ODE.inject ODE_dom.simps ODE_dom_assoc Un_empty inf_sup_distrib1 inf_sup_distrib2 osafe.cases osafe_Prod)

(*    by (metis (no_types, lifting) ODE.distinct(3) ODE.distinct(5) ODE.inject(3) ODE_dom.simps(3) ODE_dom_assoc Un_empty inf_sup_distrib1 inf_sup_distrib2 osafe.cases osafe_Prod)*)
  have rl:"osafe (oprod ODE1 ODE2) \<Longrightarrow> osafe (OProd ODE1 ODE2)"
    apply(induction ODE1 arbitrary:ODE2)
      apply(auto)
    by (metis (no_types, lifting) ODE.distinct ODE.inject ODE_dom.simps ODE_dom_assoc Un_empty inf_sup_distrib1 inf_sup_distrib2 osafe.cases osafe_Prod)
  show ?thesis using lr rl by (auto)
qed

(* Programs/formulas without any differential terms. This definition not currently used but may
 * be useful in the future. *)
inductive hpfree:: "('a, 'b, 'c) hp \<Rightarrow> bool"
  and     ffree::  "('a, 'b, 'c) formula \<Rightarrow> bool"
where
  "hpfree (Pvar x)"
| "dfree e \<Longrightarrow> hpfree (Assign x e)"
| "hpfree (AssignAny x)"
(* Differential programs allowed but not differential terms  *)
| "dfree e \<Longrightarrow> hpfree (DiffAssign x e)"
| "ffree P \<Longrightarrow> hpfree (Test P)" 
(* Differential programs allowed but not differential terms  *)
| "osafe ODE \<Longrightarrow> ffree P \<Longrightarrow> hpfree (EvolveODE ODE P)"
| "hpfree a \<Longrightarrow> hpfree b \<Longrightarrow> hpfree (Choice a b )"
| "hpfree a \<Longrightarrow> hpfree b \<Longrightarrow> hpfree (Sequence a b)"
| "hpfree a \<Longrightarrow> hpfree (Loop a)"
| "ffree f \<Longrightarrow> ffree (InContext C f)"
| "(\<forall> arg. (arg \<in> range args \<longrightarrow> dfree arg)) \<Longrightarrow> ffree (Prop p args)"
| "ffree p \<Longrightarrow> ffree (Not p)"
| "ffree p \<Longrightarrow> ffree q \<Longrightarrow> ffree (And p q)"
| "ffree p \<Longrightarrow> ffree (Exists x p)"
| "hpfree a \<Longrightarrow> ffree p \<Longrightarrow> ffree (Diamond a p)"
| "ffree (Predicational P)"
| "dfree t1 \<Longrightarrow> dfree t2 \<Longrightarrow> ffree (Geq t1 t2)"

inductive hpsafe:: "('a, 'b, 'c) hp \<Rightarrow> bool"
  and     fsafe::  "('a, 'b, 'c) formula \<Rightarrow> bool"
where
   hpsafe_Pvar:"hpsafe (Pvar x)"
 | hpsafe_Assign:"dsafe e \<Longrightarrow> hpsafe (Assign x e)"
 | hpsafe_AssignAny:" hpsafe (AssignAny e)"
 | hpsafe_DiffAssign:"dsafe e \<Longrightarrow> hpsafe (DiffAssign x e)"
 | hpsafe_Test:"fsafe P \<Longrightarrow> hpsafe (Test P)" 
 | hpsafe_Evolve:"osafe ODE \<Longrightarrow> fsafe P \<Longrightarrow> hpsafe (EvolveODE ODE P)"
 | hpsafe_Choice:"hpsafe a \<Longrightarrow> hpsafe b \<Longrightarrow> hpsafe (Choice a b )"
 | hpsafe_Sequence:"hpsafe a \<Longrightarrow> hpsafe b \<Longrightarrow> hpsafe (Sequence a b)"
 | hpsafe_Loop:"hpsafe a \<Longrightarrow> hpsafe (Loop a)"

 | fsafe_Geq:"dsafe t1 \<Longrightarrow> dsafe t2 \<Longrightarrow> fsafe (Geq t1 t2)"
 | fsafe_Prop:"(\<forall>i. dsafe (args i)) \<Longrightarrow> fsafe (Prop p args)"
 | fsafe_Not:"fsafe p \<Longrightarrow> fsafe (Not p)"
 | fsafe_And:"fsafe p \<Longrightarrow> fsafe q \<Longrightarrow> fsafe (And p q)"
 | fsafe_Exists:"fsafe p \<Longrightarrow> fsafe (Exists x p)"
 | fsafe_Diamond:"hpsafe a \<Longrightarrow> fsafe p \<Longrightarrow> fsafe (Diamond a p)"
 | fsafe_InContext:"fsafe f \<Longrightarrow> fsafe (InContext C f)"

inductive hpexec:: "('a, 'b, 'c) hp \<Rightarrow> bool"
  and     fexec::  "('a, 'b, 'c) formula \<Rightarrow> bool"
where
   hpexec_Assign:"dexec e \<Longrightarrow> hpexec (Assign x e)"
 | hpexec_Test:"fexec P \<Longrightarrow> hpexec (Test P)" 
 | hpexec_Choice:"hpexec a \<Longrightarrow> hpexec b \<Longrightarrow> hpexec (Choice a b )"
 | hpexec_Sequence:"hpexec a \<Longrightarrow> hpexec b \<Longrightarrow> hpexec (Sequence a b)"

 | fexec_Geq:"dexec t1 \<Longrightarrow> dexec t2 \<Longrightarrow> fexec (Geq t1 t2)"
 | fexec_Not:"fexec p \<Longrightarrow> fexec (Not p)"
 | fexec_And:"fexec p \<Longrightarrow> fexec q \<Longrightarrow> fexec (And p q)"

(* Auto-generated simplifier rules for safety predicates *)  
inductive_simps
      dfree_Plus_simps[simp]: "dfree (Plus a b)"
  and dfree_Neg_simps[simp]: "dfree (Neg a)"
  and dfree_Times_simps[simp]: "dfree (Times a b)"
  and dfree_Max_simps[simp]: "dfree (Max a b)"
  and dfree_Min_simps[simp]: "dfree (Min a b)"
  and dfree_Abs_simps[simp]: "dfree (Abs a)"
  and dfree_Var_simps[simp]: "dfree (Var x)"
  and dfree_DiffVar_simps[simp]: "dfree (DiffVar x)"
  and dfree_Differential_simps[simp]: "dfree (Differential x)"
(*  and dfree_DFunl_simps[simp]: "dfree (DFunctional i)"*)
  and dfree_Fun_simps[simp]: "dfree (Function i args)"
  and dfree_Const_simps[simp]: "dfree (Const r)"
  and dfree_Div_simps[simp]: "dfree (Div a b)"

inductive_simps
      dsafe_Plus_simps[simp]: "dsafe (Plus a b)"
  and dsafe_Neg_simps[simp]: "dsafe (Neg a)"
  and dsafe_Times_simps[simp]: "dsafe (Times a b)"
  and dsafe_Div_simps[simp]: "dsafe (Div a b)"
  and dsafe_Max_simps[simp]: "dsafe (Max a b)"
  and dsafe_Min_simps[simp]: "dsafe (Min a b)"
  and dsafe_Abs_simps[simp]: "dsafe (Abs a)"
  and dsafe_Var_simps[simp]: "dsafe (Var x)"
  and dsafe_DiffVar_simps[simp]: "dsafe (DiffVar x)"
  and dsafe_Fun_simps[simp]: "dsafe (Function i args)"
  and dsafe_Funl_simps[simp]: "dsafe ($$F i)"
  and dsafe_Diff_simps[simp]: "dsafe (Differential a)"
  and dsafe_Const_simps[simp]: "dsafe (Const r)"

inductive_simps
      dexec_Plus_simps[simp]: "dexec (Plus a b)"
  and dexec_Neg_simps[simp]: "dexec (Neg a)"
  and dexec_Times_simps[simp]: "dexec (Times a b)"
  and dexec_Div_simps[simp]: "dexec (Div a b)"
  and dexec_Max_simps[simp]: "dexec (Max a b)"
  and dexec_Var_simps[simp]: "dexec (Var x)"
  and dexec_Const_simps[simp]: "dexec (Const r)"

inductive_simps
      osafe_OVar_simps[simp]:"osafe (OVar c d)"
  and osafe_OSing_simps[simp]:"osafe (OSing x \<theta>)"
  and osafe_OProd_simps[simp]:"osafe (OProd ODE1 ODE2)"

inductive_simps
      hpsafe_Pvar_simps[simp]: "hpsafe (Pvar a)"
  and hpsafe_Sequence_simps[simp]: "hpsafe (a ;; b)"
  and hpsafe_Loop_simps[simp]: "hpsafe (a**)"
  and hpsafe_ODE_simps[simp]: "hpsafe (EvolveODE ODE p)"
  and hpsafe_Choice_simps[simp]: "hpsafe (a \<union>\<union> b)"
  and hpsafe_Assign_simps[simp]: "hpsafe (Assign x e)"
  and hpsafe_AssignAny_simps[simp]: "hpsafe (AssignAny e)"
  and hpsafe_DiffAssign_simps[simp]: "hpsafe (DiffAssign x e)"
  and hpsafe_Test_simps[simp]: "hpsafe (? p)"
  
  and fsafe_Geq_simps[simp]: "fsafe (Geq t1 t2)"
  and fsafe_Prop_simps[simp]: "fsafe (Prop p args)"
  and fsafe_Not_simps[simp]: "fsafe (Not p)"
  and fsafe_And_simps[simp]: "fsafe (And p q)"
  and fsafe_Exists_simps[simp]: "fsafe (Exists x p)"
  and fsafe_Diamond_simps[simp]: "fsafe (Diamond a p)"
  and fsafe_Context_simps[simp]: "fsafe (InContext C p)"

inductive_simps
      hpexec_Sequence_simps[simp]: "hpexec (a ;; b)"
  and hpexec_Choice_simps[simp]: "hpexec (a \<union>\<union> b)"
  and hpexec_Assign_simps[simp]: "hpexec (Assign x e)"
  and hpexec_Test_simps[simp]: "hpexec (? p)"
  
  and fexec_Geq_simps[simp]: "fexec (Geq t1 t2)"
  and fexec_Not_simps[simp]: "fexec (Not p)"
  and fexec_And_simps[simp]: "fexec (And p q)"
  and fexec_Le_simps[simp]: "fexec (Le p q)"
  and fexec_Ge_simps[simp]: "fexec (Ge p q)"
  and fexec_Leq_simps[simp]: "fexec (Leq p q)"

fun Ssafe::"('sf,'sc,'sz) sequent \<Rightarrow> bool"
where Ssafe_def:"Ssafe S =((\<forall>i. i \<ge> 0 \<longrightarrow> i < length (fst S) \<longrightarrow> fsafe (nth (fst S) i))
                 \<and>(\<forall>i. i \<ge> 0 \<longrightarrow> i < length (snd S) \<longrightarrow> fsafe (nth (snd S) i)))"

lemma index_list_induct:
  fixes P and n :: nat
  assumes BC:"\<And>L. 0 < length L \<Longrightarrow> P L 0"
  assumes IH:"\<And>x xs i. (i < length xs \<Longrightarrow> P xs i \<Longrightarrow> P (x # xs) (Suc i))" 
  assumes i:"n < length L"
  shows "P L n"
  using i
  apply(induction L arbitrary: n)
  subgoal for n using i BC[of "L"] by auto
  subgoal for x xs m 
      apply(cases "m = 0")
    subgoal using BC[of "x # xs"] by auto
    using IH[of "m-1"] i  by auto
  done



lemma nth_member:"n < List.length L \<Longrightarrow> List.member L (List.nth L n)"
  apply(induction L, auto simp add: member_rec)
  by (metis in_set_member length_Cons nth_mem set_ConsD)

lemma member_nth:"List.member L x \<Longrightarrow> \<exists>n. n < List.length L \<and> x = (List.nth L n)"
  apply(induction L, auto simp add: member_rec)
  using in_set_member length_Cons nth_mem set_ConsD 
  by auto

lemma member_nthE:"List.member L x \<Longrightarrow> (\<And>n.  (n < List.length L \<and> x = (List.nth L n)) \<Longrightarrow> P) \<Longrightarrow> P"
  using member_nth[of L x]  apply simp
  by(erule exE,auto)

lemma Ssafe_code[code]:
"Ssafe S =
 ((foldr (\<lambda> x acc. acc \<and> fsafe x) (fst S) True)
\<and> (foldr (\<lambda> x acc. acc \<and> fsafe x) (snd S) True))"
  apply(auto)
  subgoal
  proof -
    assume all:"\<forall>i<length (fst S). fsafe (fst S ! i)"
    have mem:"\<And>x. List.member (fst S) x \<Longrightarrow> fsafe x" 
      apply(erule member_nthE)
      using all by (auto)
    have memimp:"\<And>L. (\<forall>x. List.member L x \<longrightarrow> fsafe x) \<Longrightarrow>  (foldr (\<lambda>x acc. acc \<and> fsafe x)  L True)"
      subgoal for L
        apply(induction L)
        by(auto simp add: member_rec)
      done
    show "foldr (\<lambda>x acc. acc \<and> fsafe x)  (fst S) True" 
      using all mem memimp by auto
  qed
  proof -
    assume all:"\<forall>i<length (snd S). fsafe (snd S ! i)"
    have mem:"\<And>x. List.member (snd S) x \<Longrightarrow> fsafe x" 
      apply(erule member_nthE)
      using all by (auto)
    have memimp:"\<And>L. (\<forall>x. List.member L x \<longrightarrow> fsafe x) \<Longrightarrow>  (foldr (\<lambda>x acc. acc \<and> fsafe x)  L True)"
      subgoal for L
        apply(induction L)
        by(auto simp add: member_rec)
      done
    show "foldr (\<lambda>x acc. acc \<and> fsafe x)  (snd S) True" 
      using all mem memimp by auto
  next
    fix i
  assume fold:"foldr (\<lambda>x acc. acc \<and> fsafe x) (fst S) True"
  assume i:"i < length (fst S)"
  then have mem:"List.member (fst S) (fst S ! i)"
    using nth_member i by auto
  have memimp:"\<And>L x. (foldr (\<lambda>x acc. acc \<and> fsafe x)  L True) \<Longrightarrow>List.member L x \<Longrightarrow> fsafe x"
      subgoal for L
        apply(induction L)
        by(auto simp add: member_rec)
      done
  show "fsafe (fst S ! i)"
    using mem memimp  fold by auto  
next
  fix i
  assume fold:"foldr (\<lambda>x acc. acc \<and> fsafe x) (snd S) True"
  assume i:"i < length (snd S)"
  then have mem:"List.member (snd S) (snd S ! i)"
    using nth_member i by auto
  have memimp:"\<And>L x. (foldr (\<lambda>x acc. acc \<and> fsafe x)  L True) \<Longrightarrow>List.member L x \<Longrightarrow> fsafe x"
      subgoal for L
        apply(induction L)
        by(auto simp add: member_rec)
      done
  show "fsafe (snd S ! i)"
    using mem memimp  fold by auto  
qed
    
(*
lemma closeI_sub:"j < length \<Gamma> \<Longrightarrow> sublist (closeI \<Gamma> j) \<Gamma>"
proof -
  assume j:"j < length \<Gamma>"
  have imp:"j < length \<Gamma> \<Longrightarrow> sublist (closeI \<Gamma> j) \<Gamma>"
      apply(rule index_list_induct[of "(\<lambda> \<Gamma> j. sublist (closeI \<Gamma> j) \<Gamma>)"])
    subgoal for L by (auto simp add: sublist_def, cases L, auto simp add: member_rec)
    using j by(auto simp add: sublist_def member_rec j)
  then show ?thesis using j by auto
qed
*)
(* Basic reasoning principles about syntactic constructs, including inductive principles *)
lemma dfree_is_dsafe: "dfree \<theta> \<Longrightarrow> dsafe \<theta>"
  by (induction rule: dfree.induct) (auto intro: dsafe.intros)
  
lemma hp_induct [case_names Var Assign AssignAny DiffAssign Test Evolve Choice Compose Star]:
   "(\<And>x. P ($\<alpha> x)) \<Longrightarrow>
    (\<And>x1 x2. P (x1 := x2)) \<Longrightarrow>
    (\<And>x1. P (AssignAny x1 )) \<Longrightarrow>
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
  \<Longrightarrow> (\<And>C p. P p \<Longrightarrow> P (InContext C p))
  \<Longrightarrow> P \<phi>"
  by (induction rule: formula.induct) (auto)

context ids begin
lemma proj_sing1:"(singleton \<theta> vid1) = \<theta>"
  by (auto)

lemma proj_sing2:"vid1 \<noteq> y  \<Longrightarrow> (singleton \<theta> y) = (Const (bword_zero))"
  by (auto)
end

end