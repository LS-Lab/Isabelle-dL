theory "USubst"
imports
  Complex_Main HOL
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
  "./Ids"
  "./Lib"
  "./Syntax"
  "./Denotational_Semantics"
  "./Static_Semantics"
begin 
section \<open>Uniform Substitution Definitions\<close>
text\<open>This section defines substitutions and implements the substitution operation.
  Every part of substitution comes in two flavors. The "Nsubst" variant of each function
  returns a term/formula/ode/program which (as encoded in the type system) has less symbols
  that the input. We use this operation when substitution into functions and function-like
  constructs to make it easy to distinguish identifiers that stand for arguments to functions
  from other identifiers. In order to expose a simpler interface, we also have a "subst" variant
  which does not delete variables.
  
  Substitution is not always sound. The various admissibility predicates *admit describe conditions
  under which the various substitution operations are sound.
  \<close>

record ('a, 'b, 'c) subst =
  (* The RHS of a function or predicate substitution is a term or formula
   * with extra variables, which are used to refer to arguments. *)
  SFunctions       :: "'a \<rightharpoonup> ('a + 'c, 'c) trm"
  SPredicates      :: "'c \<rightharpoonup> ('a + 'c, 'b, 'c) formula"
  SContexts        :: "'b \<rightharpoonup> ('a, 'b + unit, 'c) formula"
  SPrograms        :: "'c \<rightharpoonup> ('a, 'b, 'c) hp"
  SODEs            :: "'c \<rightharpoonup> ('a, 'c) ODE"

context ids begin
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
    (case f of 
      Inl f' \<Rightarrow> Function f' (\<lambda> i. NTsubst (args i) \<sigma>) 
    | Inr f' \<Rightarrow> \<sigma> f')"  
| "NTsubst (Plus \<theta>1 \<theta>2) \<sigma> = Plus (NTsubst \<theta>1 \<sigma>) (NTsubst \<theta>2 \<sigma>)"  
| "NTsubst (Times \<theta>1 \<theta>2) \<sigma> = Times (NTsubst \<theta>1 \<sigma>) (NTsubst \<theta>2 \<sigma>)"  
| "NTsubst (Differential \<theta>) \<sigma> = Differential (NTsubst \<theta> \<sigma>)"

primrec Tsubst::"('a, 'c) trm \<Rightarrow> ('a, 'b, 'c) subst \<Rightarrow> ('a, 'c) trm"
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

primrec Osubst::"('a, 'c) ODE \<Rightarrow> ('a, 'b, 'c) subst \<Rightarrow> ('a, 'c) ODE"
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
| "NFsubst (Exists x \<phi>) \<sigma> = Exists x (NFsubst \<phi> \<sigma>)"
| "NFsubst (Diamond \<alpha> \<phi>) \<sigma> = Diamond (NPsubst \<alpha> \<sigma>) (NFsubst \<phi> \<sigma>)"
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
| "PFsubst (Exists x \<phi>) \<sigma> = Exists x (PFsubst \<phi> \<sigma>)"
| "PFsubst (Diamond \<alpha> \<phi>) \<sigma> = Diamond (PPsubst \<alpha> \<sigma>) (PFsubst \<phi> \<sigma>)"
| "PFsubst (DiffFormula \<phi>) \<sigma> = DiffFormula (PFsubst \<phi> \<sigma>)"
| "PFsubst (InContext C \<phi>) \<sigma> = (case C of Inl C' \<Rightarrow> InContext C' (PFsubst \<phi> \<sigma>) | Inr p' \<Rightarrow> \<sigma> p')"

  
fun Psubst::"('a, 'b, 'c) hp \<Rightarrow> ('a, 'b, 'c) subst \<Rightarrow> ('a, 'b, 'c) hp"
and Fsubst::"('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) subst \<Rightarrow> ('a, 'b, 'c) formula"
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
| "Fsubst (Exists x \<phi>) \<sigma> = Exists x (Fsubst \<phi> \<sigma>)"
| "Fsubst (Diamond \<alpha> \<phi>) \<sigma> = Diamond (Psubst \<alpha> \<sigma>) (Fsubst \<phi> \<sigma>)"
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
where "TUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> SIGT \<theta>. (case SFunctions \<sigma> i of Some f' \<Rightarrow> FVT f'  | None \<Rightarrow> {})) \<inter> U) = {}"

inductive Tadmit :: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'c) trm \<Rightarrow> bool"
where 
  Tadmit_Diff:"Tadmit \<sigma> \<theta> \<Longrightarrow> TUadmit \<sigma> \<theta> UNIV \<Longrightarrow> Tadmit \<sigma> (Differential \<theta>)"
| Tadmit_Fun1:"(\<And>i. Tadmit \<sigma> (args i)) \<Longrightarrow> SFunctions \<sigma> f = Some f' \<Longrightarrow> NTadmit (\<lambda> i. Tsubst (args i) \<sigma>) f' \<Longrightarrow> Tadmit \<sigma> (Function f args)"
| Tadmit_Fun2:"(\<And>i. Tadmit \<sigma> (args i)) \<Longrightarrow> SFunctions \<sigma> f = None \<Longrightarrow> Tadmit \<sigma> (Function f args)"
| Tadmit_Plus:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Tadmit \<sigma> (Plus \<theta>1 \<theta>2)"
| Tadmit_Times:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Tadmit \<sigma> (Times \<theta>1 \<theta>2)"
| Tadmit_DiffVar:"Tadmit \<sigma> (DiffVar x)"
| Tadmit_Var:"Tadmit \<sigma> (Var x)"
| Tadmit_Const:"Tadmit \<sigma> (Const r)"

inductive_simps
      Tadmit_Plus_simps[simp]: "Tadmit \<sigma> (Plus a b)"
  and Tadmit_Times_simps[simp]: "Tadmit \<sigma> (Times a b)"
  and Tadmit_Var_simps[simp]: "Tadmit \<sigma> (Var x)"
  and Tadmit_Fun_simps[simp]: "Tadmit \<sigma> (Function i args)"

inductive Oadmit:: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'c) ODE \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where 
  Oadmit_Var:"Oadmit \<sigma> (OVar c) U"
| Oadmit_Sing:"TUadmit \<sigma> \<theta> U \<Longrightarrow> Oadmit \<sigma> (OSing x \<theta>) U"
| Oadmit_Prod:"Oadmit \<sigma> ODE1 U \<Longrightarrow> Oadmit \<sigma> ODE2 U \<Longrightarrow> ODE_dom (Osubst ODE1 \<sigma>) \<inter> ODE_dom (Osubst ODE2 \<sigma>) = {} \<Longrightarrow> Oadmit \<sigma> (OProd ODE1 ODE2) U"

inductive_simps
      Oadmit_Var_simps[simp]: "Oadmit \<sigma> (OVar c) U"
  and Oadmit_Sing_simps[simp]: "Oadmit \<sigma> (OSing x e) U"
  and Oadmit_Prod_simps[simp]: "Oadmit \<sigma> (OProd ODE1 ODE2) U"

definition PUadmit :: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'b, 'c) hp \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "PUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> (SDom \<sigma> \<inter> SIGP \<theta>).  SFV \<sigma> i) \<inter> U) = {}"

definition FUadmit :: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "FUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> (SDom \<sigma> \<inter> SIGF \<theta>).  SFV \<sigma> i) \<inter> U) = {}"

definition NOUadmit :: "('d \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a + 'd,  'c) ODE \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "NOUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i. FVT (\<sigma> i)) \<inter> U) = {}"

definition NFUadmit :: "('d \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a + 'd, 'b, 'c) formula \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "NFUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i. FVT (\<sigma> i)) \<inter> U) = {}"

definition NPUadmit :: "('d \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a + 'd, 'b, 'c) hp \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "NPUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i. FVT (\<sigma> i)) \<inter> U) = {}"

inductive NPadmit :: "('d \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a + 'd, 'b, 'c) hp \<Rightarrow> bool" 
and NFadmit :: "('d \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a + 'd, 'b, 'c) formula \<Rightarrow> bool"
where
  NPadmit_Pvar:"NPadmit \<sigma> (Pvar a)"
| NPadmit_Sequence:"NPadmit \<sigma> a \<Longrightarrow> NPadmit \<sigma> b \<Longrightarrow> NPUadmit \<sigma> b (BVP (NPsubst a \<sigma>))\<Longrightarrow> NPadmit \<sigma> (Sequence a b)"  
| NPadmit_Loop:"NPadmit \<sigma> a \<Longrightarrow> NPUadmit \<sigma> a (BVP (NPsubst a \<sigma>)) \<Longrightarrow> NPadmit \<sigma> (Loop a)"        
| NPadmit_ODE:"NOUadmit \<sigma> ODE (ODE_vars ODE) \<Longrightarrow> NFadmit \<sigma> \<phi> \<Longrightarrow> NFUadmit \<sigma> \<phi> (ODE_vars ODE) \<Longrightarrow> NPadmit \<sigma> (EvolveODE ODE \<phi>)"
| NPadmit_Choice:"NPadmit \<sigma> a \<Longrightarrow> NPadmit \<sigma> b \<Longrightarrow> NPadmit \<sigma> (Choice a b)"            
| NPadmit_Assign:"NTadmit \<sigma> \<theta> \<Longrightarrow> NPadmit \<sigma> (Assign x \<theta>)"  
| NPadmit_DiffAssign:"NTadmit \<sigma> \<theta> \<Longrightarrow> NPadmit \<sigma> (DiffAssign x \<theta>)"  
| NPadmit_Test:"NFadmit \<sigma> \<phi> \<Longrightarrow> NPadmit \<sigma> (Test \<phi>)"

| NFadmit_Geq:"NTadmit \<sigma> \<theta>1 \<Longrightarrow> NTadmit \<sigma> \<theta>2 \<Longrightarrow> NFadmit \<sigma> (Geq \<theta>1 \<theta>2)"
| NFadmit_Prop:"(\<And>i. NTadmit \<sigma> (args i)) \<Longrightarrow> NFadmit \<sigma> (Prop f args)"
| NFadmit_Not:"NFadmit \<sigma> \<phi> \<Longrightarrow> NFadmit \<sigma> (Not \<phi>)"
| NFadmit_And:"NFadmit \<sigma> \<phi> \<Longrightarrow> NFadmit \<sigma> \<psi> \<Longrightarrow> NFadmit \<sigma> (And \<phi> \<psi>)"
| NFadmit_DiffFormula:"NFadmit \<sigma> \<phi> \<Longrightarrow> NFadmit \<sigma> (DiffFormula \<phi>)"
| NFadmit_Exists:"NFadmit \<sigma> \<phi> \<Longrightarrow> NFUadmit \<sigma> \<phi> {Inl x} \<Longrightarrow> NFadmit \<sigma> (Exists x \<phi>)"
| NFadmit_Diamond:"NFadmit \<sigma> \<phi> \<Longrightarrow> NPadmit \<sigma> a \<Longrightarrow> NFUadmit \<sigma> \<phi> (BVP (NPsubst a \<sigma>)) \<Longrightarrow> NFadmit \<sigma> (Diamond a \<phi>)"
| NFadmit_Context:"NFadmit \<sigma> \<phi> \<Longrightarrow> NFUadmit \<sigma> \<phi> UNIV \<Longrightarrow> NFadmit \<sigma> (InContext C \<phi>)"

definition PFUadmit :: "('d \<Rightarrow> ('a, 'b, 'c) formula) \<Rightarrow> ('a, 'b + 'd, 'c) formula \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "PFUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i. FVF (\<sigma> i)) \<inter> U) = {}"

definition PPUadmit :: "('d \<Rightarrow> ('a, 'b, 'c) formula) \<Rightarrow> ('a, 'b + 'd, 'c) hp \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "PPUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i. FVF (\<sigma> i)) \<inter> U) = {}"
  
inductive PPadmit:: "('d \<Rightarrow> ('a, 'b, 'c) formula) \<Rightarrow> ('a, 'b + 'd, 'c) hp \<Rightarrow> bool"
and PFadmit:: "('d \<Rightarrow> ('a, 'b, 'c) formula) \<Rightarrow> ('a, 'b + 'd, 'c) formula \<Rightarrow> bool"
where 
  PPadmit_Pvar:"PPadmit \<sigma> (Pvar a)"
| PPadmit_Sequence:"PPadmit \<sigma> a \<Longrightarrow> PPadmit \<sigma> b \<Longrightarrow> PPUadmit \<sigma> b (BVP (PPsubst a \<sigma>))\<Longrightarrow> PPadmit \<sigma> (Sequence a b)"  
| PPadmit_Loop:"PPadmit \<sigma> a \<Longrightarrow> PPUadmit \<sigma> a (BVP (PPsubst a \<sigma>)) \<Longrightarrow> PPadmit \<sigma> (Loop a)"        
| PPadmit_ODE:"PFadmit \<sigma> \<phi> \<Longrightarrow> PFUadmit \<sigma> \<phi> (ODE_vars ODE) \<Longrightarrow> PPadmit \<sigma> (EvolveODE ODE \<phi>)"
| PPadmit_Choice:"PPadmit \<sigma> a \<Longrightarrow> PPadmit \<sigma> b \<Longrightarrow> PPadmit \<sigma> (Choice a b)"            
| PPadmit_Assign:"PPadmit \<sigma> (Assign x \<theta>)"  
| PPadmit_DiffAssign:"PPadmit \<sigma> (DiffAssign x \<theta>)"  
| PPadmit_Test:"PFadmit \<sigma> \<phi> \<Longrightarrow> PPadmit \<sigma> (Test \<phi>)"

| PFadmit_Geq:"PFadmit \<sigma> (Geq \<theta>1 \<theta>2)"
| PFadmit_Prop:"PFadmit \<sigma> (Prop f args)"
| PFadmit_Not:"PFadmit \<sigma> \<phi> \<Longrightarrow> PFadmit \<sigma> (Not \<phi>)"
| PFadmit_And:"PFadmit \<sigma> \<phi> \<Longrightarrow> PFadmit \<sigma> \<psi> \<Longrightarrow> PFadmit \<sigma> (And \<phi> \<psi>)"
| PFadmit_DiffFormula:"PFadmit \<sigma> \<phi> \<Longrightarrow> PFadmit \<sigma> (DiffFormula \<phi>)"
| PFadmit_Exists:"PFadmit \<sigma> \<phi> \<Longrightarrow> PFUadmit \<sigma> \<phi> {Inl x} \<Longrightarrow> PFadmit \<sigma> (Exists x \<phi>)"
| PFadmit_Diamond:"PFadmit \<sigma> \<phi> \<Longrightarrow> PPadmit \<sigma> a \<Longrightarrow> PFUadmit \<sigma> \<phi> (BVP (PPsubst a \<sigma>)) \<Longrightarrow> PFadmit \<sigma> (Diamond a \<phi>)"
| PFadmit_Context:"PFadmit \<sigma> \<phi> \<Longrightarrow> PFUadmit \<sigma> \<phi> UNIV \<Longrightarrow> PFadmit \<sigma> (InContext C \<phi>)"

  
inductive Padmit:: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'b, 'c) hp \<Rightarrow> bool"
and Fadmit:: "('a, 'b, 'c) subst \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> bool"
where
  Padmit_Pvar:"Padmit \<sigma> (Pvar a)"
| Padmit_Sequence:"Padmit \<sigma> a \<Longrightarrow> Padmit \<sigma> b \<Longrightarrow> PUadmit \<sigma> b (BVP (Psubst a \<sigma>))\<Longrightarrow> Padmit \<sigma> (Sequence a b)"  
| Padmit_Loop:"Padmit \<sigma> a \<Longrightarrow> PUadmit \<sigma> a (BVP (Psubst a \<sigma>)) \<Longrightarrow> Padmit \<sigma> (Loop a)"        
| Padmit_ODE:"Oadmit \<sigma> ODE (ODE_vars ODE) \<Longrightarrow> Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> (ODE_vars ODE) \<Longrightarrow> Padmit \<sigma> (EvolveODE ODE \<phi>)"
| Padmit_Choice:"Padmit \<sigma> a \<Longrightarrow> Padmit \<sigma> b \<Longrightarrow> Padmit \<sigma> (Choice a b)"            
| Padmit_Assign:"Tadmit \<sigma> \<theta> \<Longrightarrow> Padmit \<sigma> (Assign x \<theta>)"  
| Padmit_DiffAssign:"Tadmit \<sigma> \<theta> \<Longrightarrow> Padmit \<sigma> (DiffAssign x \<theta>)"  
| Padmit_Test:"Fadmit \<sigma> \<phi> \<Longrightarrow> Padmit \<sigma> (Test \<phi>)"

| Fadmit_Geq:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Fadmit \<sigma> (Geq \<theta>1 \<theta>2)"
| Fadmit_Prop1:"(\<And>i. Tadmit \<sigma> (args i)) \<Longrightarrow> SPredicates \<sigma> p = Some p' \<Longrightarrow> NFadmit (\<lambda> i. Tsubst (args i) \<sigma>) p' \<Longrightarrow> Fadmit \<sigma> (Prop p args)"
| Fadmit_Prop2:"(\<And>i. Tadmit \<sigma> (args i)) \<Longrightarrow> SPredicates \<sigma> p = None \<Longrightarrow> Fadmit \<sigma> (Prop p args)"
| Fadmit_Not:"Fadmit \<sigma> \<phi> \<Longrightarrow> Fadmit \<sigma> (Not \<phi>)"
| Fadmit_And:"Fadmit \<sigma> \<phi> \<Longrightarrow> Fadmit \<sigma> \<psi> \<Longrightarrow> Fadmit \<sigma> (And \<phi> \<psi>)"
| Fadmit_DiffFormula:"Fadmit \<sigma> \<phi> \<Longrightarrow> Fadmit \<sigma> (DiffFormula \<phi>)"
| Fadmit_Exists:"Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> {Inl x} \<Longrightarrow> Fadmit \<sigma> (Exists x \<phi>)"
| Fadmit_Diamond:"Fadmit \<sigma> \<phi> \<Longrightarrow> Padmit \<sigma> a \<Longrightarrow> FUadmit \<sigma> \<phi> (BVP (Psubst a \<sigma>)) \<Longrightarrow> Fadmit \<sigma> (Diamond a \<phi>)"
| Fadmit_Context1:"Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> UNIV \<Longrightarrow> SContexts \<sigma> C = Some C' \<Longrightarrow> PFadmit (\<lambda> (). Fsubst \<phi> \<sigma>) C' \<Longrightarrow> Fadmit \<sigma> (InContext C \<phi>)"
| Fadmit_Context2:"Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> UNIV \<Longrightarrow> SContexts \<sigma> C = None \<Longrightarrow> Fadmit \<sigma> (InContext C \<phi>)"
  
inductive_simps
      Padmit_Pvar_simps[simp]: "Padmit \<sigma> (Pvar a)"
  and Padmit_Sequence_simps[simp]: "Padmit \<sigma> (a ;; b)"
  and Padmit_Loop_simps[simp]: "Padmit \<sigma> (a**)"
  and Padmit_ODE_simps[simp]: "Padmit \<sigma> (EvolveODE ODE p)"
  and Padmit_Choice_simps[simp]: "Padmit \<sigma> (a \<union>\<union> b)"
  and Padmit_Assign_simps[simp]: "Padmit \<sigma> (Assign x e)"
  and Padmit_DiffAssign_simps[simp]: "Padmit \<sigma> (DiffAssign x e)"
  and Padmit_Test_simps[simp]: "Padmit \<sigma> (? p)"
  
  and Fadmit_Geq_simps[simp]: "Fadmit \<sigma> (Geq t1 t2)"
  and Fadmit_Prop_simps[simp]: "Fadmit \<sigma> (Prop p args)"
  and Fadmit_Not_simps[simp]: "Fadmit \<sigma> (Not p)"
  and Fadmit_And_simps[simp]: "Fadmit \<sigma> (And p q)"
  and Fadmit_DiffFormula_simps[simp]: "Fadmit \<sigma> (DiffFormula p)"
  and Fadmit_Exists_simps[simp]: "Fadmit \<sigma> (Exists x p)"
  and Fadmit_Diamond_simps[simp]: "Fadmit \<sigma> (Diamond a p)"
  and Fadmit_Context_simps[simp]: "Fadmit \<sigma> (InContext C p)"
  
  
  
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
 Predicates = (\<lambda>p. case SPredicates \<sigma> p of Some p' \<Rightarrow> (\<lambda>R. \<nu> \<in> fml_sem (extendf I R) p') | None \<Rightarrow> Predicates I p),
 Contexts =   (\<lambda>c. case SContexts \<sigma> c of Some c' \<Rightarrow> (\<lambda>R. fml_sem (extendc I R) c') | None \<Rightarrow> Contexts I c),
 Programs =   (\<lambda>a. case SPrograms \<sigma> a of Some a' \<Rightarrow> prog_sem I a' | None \<Rightarrow> Programs I a),
 ODEs =     (\<lambda>ode. case SODEs \<sigma> ode of Some ode' \<Rightarrow> ODE_sem I ode' | None \<Rightarrow> ODEs I ode)\<rparr>"

lemma dsem_to_ssem:"dfree \<theta> \<Longrightarrow> dterm_sem I \<theta> \<nu> = sterm_sem I \<theta> (fst \<nu>)"
  by (induct rule: dfree.induct) (auto)

definition NTadjoint::"('sf, 'sc, 'sz) interp \<Rightarrow> ('d::finite \<Rightarrow> ('sf, 'sz) trm) \<Rightarrow> 'sz state \<Rightarrow> ('sf + 'd, 'sc, 'sz) interp" 
where "NTadjoint I \<sigma> \<nu> =
\<lparr>Functions =   (\<lambda>f. case f of Inl f' \<Rightarrow> Functions I f' | Inr f' \<Rightarrow> (\<lambda>_. dterm_sem I (\<sigma> f') \<nu>)),
 Predicates = Predicates I,
 Contexts = Contexts I,
 Programs = Programs I,
 ODEs = ODEs I\<rparr>"

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
\<lparr>Functions =   (\<lambda>f. case f of Inl f' \<Rightarrow> Functions I f' | Inr f' \<Rightarrow> (\<lambda>_. sterm_sem I (\<sigma> f') (fst \<nu>))),
 Predicates = Predicates I,
 Contexts = Contexts I,
 Programs = Programs I,
 ODEs = ODEs I\<rparr>)" 
  by (auto simp add: dsem_to_ssem NTadjoint_def)

definition PFadjoint::"('sf, 'sc, 'sz) interp \<Rightarrow> ('d::finite \<Rightarrow> ('sf, 'sc, 'sz) formula) \<Rightarrow> ('sf, 'sc  + 'd, 'sz) interp" 
where "PFadjoint I \<sigma> =
\<lparr>Functions =  Functions I,
 Predicates = Predicates I,
 Contexts = (\<lambda>f. case f of Inl f' \<Rightarrow> Contexts I f' | Inr f' \<Rightarrow> (\<lambda>_. fml_sem I (\<sigma> f'))),
 Programs = Programs I,
 ODEs = ODEs I\<rparr>"

end end