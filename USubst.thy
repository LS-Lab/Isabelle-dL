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
where "TUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> SIGT \<theta>. (case SFunctions \<sigma> i of Some f' \<Rightarrow> FVT f')) \<inter> U) = {}"

inductive Tadmit :: "('sf, 'sc, 'sz) subst \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> bool"
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
| "Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> {Inl x} \<Longrightarrow> Fadmit \<sigma> (Exists x \<phi>)"
| "Fadmit \<sigma> \<phi> \<Longrightarrow> Padmit \<sigma> a \<Longrightarrow> FUadmit \<sigma> \<phi> (BVP a) \<Longrightarrow> Fadmit \<sigma> (Diamond a \<phi>)"
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

end end