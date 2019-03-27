theory "USubst"
imports
  Ordinary_Differential_Equations.ODE_Analysis
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
  
  Naive substitution without side conditions would not always be sound. The various admissibility 
  predicates *admit describe conditions under which the various substitution operations are sound.
  \<close>

text\<open> 
Explicit data structure for substitutions.

The RHS of a function or predicate substitution is a term or formula
with extra variables, which are used to refer to arguments. \<close>
record subst =
  SFunctions       :: "ident \<rightharpoonup> trm"
  SFunls           :: "ident \<rightharpoonup> trm"
  SPredicates      :: "ident \<rightharpoonup> formula"
  SContexts        :: "ident \<rightharpoonup> formula"
  SPrograms        :: "ident \<rightharpoonup> hp"
  SODEs            :: "ident \<Rightarrow> space \<Rightarrow> ODE option"


(* ident_expose *)

(*
record  subst =
  SFunctions       :: "'a \<rightharpoonup> ('a + 'c, 'c) trm"
  SFunls           :: "'a \<rightharpoonup> ('a, 'c) trm"
  SPredicates      :: "'c \<rightharpoonup> ('a + 'c, 'b, 'c) formula"
  SContexts        :: "'b \<rightharpoonup> ('a, 'b + unit, 'c) formula"
  SPrograms        :: "'c \<rightharpoonup> ('a, 'b, 'c) hp"
  SODEs            :: "'c \<Rightarrow> 'c space \<Rightarrow> ('a, 'c) ODE option"*)


(* definition NTUadmit :: "('d \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a + 'd, 'c) trm \<Rightarrow> ('c + 'c) set \<Rightarrow> bool" *)
definition NTUadmit :: "(ident \<Rightarrow> trm) \<Rightarrow>  trm \<Rightarrow> (ident + ident) set \<Rightarrow> bool"
where "NTUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> {i. (debase i) \<in> SIGT \<theta> \<or> (Debase i) \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<inter> U) = {}"


(* TadmitFFO :: "('d \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a + 'd, 'c) trm \<Rightarrow> bool *)
inductive TadmitFFO :: "(ident \<Rightarrow> trm) \<Rightarrow> trm \<Rightarrow> bool"
where 
  TadmitFFO_Diff:"TadmitFFO \<sigma> \<theta> \<Longrightarrow> NTUadmit \<sigma> \<theta> UNIV \<Longrightarrow> TadmitFFO \<sigma> (Differential \<theta>)"
| TadmitFFO_Fun:"(\<forall>i. TadmitFFO \<sigma> (args i)) \<Longrightarrow> ilength f < MAX_STR \<Longrightarrow> nonbase f \<Longrightarrow> dfree (\<sigma> (rebase f)) \<Longrightarrow> TadmitFFO \<sigma> (Function f args)"
(*| TadmitFFO_Fun2:"(\<forall>i. TadmitFFO \<sigma> (args i)) \<Longrightarrow> ilength f < MAX_STR \<Longrightarrow> nonbase f \<Longrightarrow> dfree (\<sigma> (rebase f)) \<Longrightarrow> TadmitFFO \<sigma> (Function f args)"*)
| TadmitFFO_Plus:"TadmitFFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFFO \<sigma> \<theta>2 \<Longrightarrow> TadmitFFO \<sigma> (Plus \<theta>1 \<theta>2)"
| TadmitFFO_Times:"TadmitFFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFFO \<sigma> \<theta>2 \<Longrightarrow> TadmitFFO \<sigma> (Times \<theta>1 \<theta>2)"
| TadmitFFO_Max:"TadmitFFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFFO \<sigma> \<theta>2 \<Longrightarrow> TadmitFFO \<sigma> (Max \<theta>1 \<theta>2)"
| TadmitFFO_Min:"TadmitFFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFFO \<sigma> \<theta>2 \<Longrightarrow> TadmitFFO \<sigma> (Min \<theta>1 \<theta>2)"
| TadmitFFO_Abs:"TadmitFFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFFO \<sigma> (Abs \<theta>1)"
| TadmitFFO_Div:"TadmitFFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFFO \<sigma> \<theta>2 \<Longrightarrow> TadmitFFO \<sigma> (Div \<theta>1 \<theta>2)"
| TadmitFFO_Neg:"TadmitFFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFFO \<sigma> (Neg \<theta>1)"
| TadmitFFO_Var:"TadmitFFO \<sigma> (Var x)"
| TadmitFFO_Const:"TadmitFFO \<sigma> (Const r)"

inductive_simps
  TadmitFFO_Diff_simps[simp]: "TadmitFFO \<sigma> (Differential \<theta>)"
and TadmitFFO_Fun_simps[simp]: "TadmitFFO \<sigma> (Function f args)"
and TadmitFFO_Plus_simps[simp]: "TadmitFFO \<sigma> (Plus t1 t2)"
and TadmitFFO_Times_simps[simp]: "TadmitFFO \<sigma> (Times t1 t2)"
and TadmitFFO_Div_simps[simp]: "TadmitFFO \<sigma> (Div t1 t2)"
and TadmitFFO_Var_simps[simp]: "TadmitFFO \<sigma> (Var x)"
and TadmitFFO_Abs_simps[simp]: "TadmitFFO \<sigma> (Abs x)"
and TadmitFFO_Neg_simps[simp]: "TadmitFFO \<sigma> (Neg x)"
and TadmitFFO_Const_simps[simp]: "TadmitFFO \<sigma> (Const r)"

(* primrec TsubstFO::"('a + 'b, 'c) trm \<Rightarrow> ('b \<Rightarrow> ('a, 'c) trm) \<Rightarrow> ('a, 'c) trm" *)

primrec TsubstFO::" trm \<Rightarrow> (ident \<Rightarrow> trm) \<Rightarrow> trm"
where
  TFO_Var:"TsubstFO (Var v) \<sigma> = Var v"
| TFO_DiffVar:"TsubstFO (DiffVar v) \<sigma> = DiffVar v"
| TFO_Const:"TsubstFO (Const r) \<sigma> = Const r"  
(* TODO: So weird to replicate between function vs. funl case but might actually work*)
| TFO_Funl:"TsubstFO ($$F f) \<sigma> = (case args_to_id f of Some (Inl ff) \<Rightarrow> ($$F f) | Some (Inr ff) \<Rightarrow> \<sigma> ff)"
| TFO_Funl_rep:"TsubstFO (Function f args) \<sigma> =
    (case args_to_id f of 
      Some (Inl f') \<Rightarrow> Function f (\<lambda> i. TsubstFO (args i) \<sigma>) 
    | Some (Inr f') \<Rightarrow> \<sigma> f')"  
| TFO_Neg:"TsubstFO (Neg \<theta>1) \<sigma> = Neg (TsubstFO \<theta>1 \<sigma>)"  
| TFO_Plus:"TsubstFO (Plus \<theta>1 \<theta>2) \<sigma> = Plus (TsubstFO \<theta>1 \<sigma>) (TsubstFO \<theta>2 \<sigma>)"  
| TFO_Times:"TsubstFO (Times \<theta>1 \<theta>2) \<sigma> = Times (TsubstFO \<theta>1 \<sigma>) (TsubstFO \<theta>2 \<sigma>)"  
| TFO_Div:"TsubstFO (Div \<theta>1 \<theta>2) \<sigma> = Div (TsubstFO \<theta>1 \<sigma>) (TsubstFO \<theta>2 \<sigma>)"  
| TFO_Max:"TsubstFO (Max \<theta>1 \<theta>2) \<sigma> = Max (TsubstFO \<theta>1 \<sigma>) (TsubstFO \<theta>2 \<sigma>)"  
| TFO_Min:"TsubstFO (Min \<theta>1 \<theta>2) \<sigma> = Min (TsubstFO \<theta>1 \<sigma>) (TsubstFO \<theta>2 \<sigma>)"  
| TFO_Abs:"TsubstFO (Abs \<theta>1) \<sigma> = Abs (TsubstFO \<theta>1 \<sigma>)"  
| TFO_Diff:"TsubstFO (Differential \<theta>) \<sigma> = Differential (TsubstFO \<theta> \<sigma>)"

inductive TadmitFO :: "(ident \<Rightarrow> trm) \<Rightarrow> trm \<Rightarrow> bool"
where 
  TadmitFO_Diff:"TadmitFFO \<sigma> \<theta> \<Longrightarrow> NTUadmit \<sigma> \<theta> UNIV \<Longrightarrow> dfree (TsubstFO \<theta> \<sigma>) \<Longrightarrow> TadmitFO \<sigma> (Differential \<theta>)"
| TadmitFO_Fun:"(\<forall>i. TadmitFO \<sigma> (args i)) \<Longrightarrow> TadmitFO \<sigma> (Function f args)"
| TadmitFO_Funl:"TadmitFO \<sigma> ($$F f)" (*Inl *)
| TadmitFO_Neg:"TadmitFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFO \<sigma> (Neg \<theta>1)"
| TadmitFO_Plus:"TadmitFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFO \<sigma> \<theta>2 \<Longrightarrow> TadmitFO \<sigma> (Plus \<theta>1 \<theta>2)"
| TadmitFO_Times:"TadmitFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFO \<sigma> \<theta>2 \<Longrightarrow> TadmitFO \<sigma> (Times \<theta>1 \<theta>2)"
| TadmitFO_Div:"TadmitFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFO \<sigma> \<theta>2 \<Longrightarrow> TadmitFO \<sigma> (Div \<theta>1 \<theta>2)"
| TadmitFO_Max:"TadmitFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFO \<sigma> \<theta>2 \<Longrightarrow> TadmitFO \<sigma> (Max \<theta>1 \<theta>2)"
| TadmitFO_Min:"TadmitFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFO \<sigma> \<theta>2 \<Longrightarrow> TadmitFO \<sigma> (Min \<theta>1 \<theta>2)"
| TadmitFO_Abs:"TadmitFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFO \<sigma> (Abs \<theta>1)"
| TadmitFO_DiffVar:"TadmitFO \<sigma> (DiffVar x)"
| TadmitFO_Var:"TadmitFO \<sigma> (Var x)"
| TadmitFO_Const:"TadmitFO \<sigma> (Const r)"

inductive_simps
      TadmitFO_Plus_simps[simp]: "TadmitFO \<sigma> (Plus a b)"
  and TadmitFO_Times_simps[simp]: "TadmitFO \<sigma> (Times a b)"
  and TadmitFO_Max_simps[simp]: "TadmitFO \<sigma> (Max a b)"
  and TadmitFO_Div_simps[simp]: "TadmitFO \<sigma> (Div a b)"
  and TadmitFO_Min_simps[simp]: "TadmitFO \<sigma> (Min a b)"
  and TadmitFO_Abs_simps[simp]: "TadmitFO \<sigma> (Abs a)"
  and TadmitFO_Var_simps[simp]: "TadmitFO \<sigma> (Var x)"
  and TadmitFO_DiffVar_simps[simp]: "TadmitFO \<sigma> (DiffVar x)"
  and TadmitFO_Differential_simps[simp]: "TadmitFO \<sigma> (Differential \<theta>)"
  and TadmitFO_Const_simps[simp]: "TadmitFO \<sigma> (Const r)"
  and TadmitFO_Fun_simps[simp]: "TadmitFO \<sigma> (Function i args)"
  and TadmitFO_Funl_simps[simp]: "TadmitFO \<sigma> ($$F f)"

primrec Tsubst::" trm \<Rightarrow> subst \<Rightarrow> trm"
where
  TVar:"Tsubst (Var x) \<sigma> = Var x"
| TDiffVar:"Tsubst (DiffVar x) \<sigma> = DiffVar x"  
| TConst:"Tsubst (Const r) \<sigma> = Const r"  
| TFun:"Tsubst (Function f args) \<sigma> = (case SFunctions \<sigma> f of Some f' \<Rightarrow> TsubstFO f' | None \<Rightarrow> Function f) (\<lambda> i. Tsubst (args i) \<sigma>)"  
| TFunl:"Tsubst ($$F f) \<sigma> = (case SFunls \<sigma> f of Some f' \<Rightarrow>  f' | None \<Rightarrow>  ($$F f))"  
| TNeg:"Tsubst (Neg \<theta>1) \<sigma> = Neg (Tsubst \<theta>1 \<sigma>)"  
| TPlus:"Tsubst (Plus \<theta>1 \<theta>2) \<sigma> = Plus (Tsubst \<theta>1 \<sigma>) (Tsubst \<theta>2 \<sigma>)"  
| TTimes:"Tsubst (Times \<theta>1 \<theta>2) \<sigma> = Times (Tsubst \<theta>1 \<sigma>) (Tsubst \<theta>2 \<sigma>)"  
| TDiv:"Tsubst (Div \<theta>1 \<theta>2) \<sigma> = Div (Tsubst \<theta>1 \<sigma>) (Tsubst \<theta>2 \<sigma>)"  
| TMax:"Tsubst (Max \<theta>1 \<theta>2) \<sigma> = Max (Tsubst \<theta>1 \<sigma>) (Tsubst \<theta>2 \<sigma>)"  
| TMin:"Tsubst (Min \<theta>1 \<theta>2) \<sigma> = Min (Tsubst \<theta>1 \<sigma>) (Tsubst \<theta>2 \<sigma>)"  
| TAbs:"Tsubst (Abs \<theta>1) \<sigma> = Abs (Tsubst \<theta>1 \<sigma>) "  
| TDiff:"Tsubst (Differential \<theta>) \<sigma> = Differential (Tsubst \<theta> \<sigma>)"
  
primrec OsubstFO::"ODE \<Rightarrow> (ident \<Rightarrow> trm) \<Rightarrow> ODE"
where
  "OsubstFO (OVar c sp) \<sigma> = OVar c sp"
| "OsubstFO (OSing x \<theta>) \<sigma> = OSing x (TsubstFO \<theta> \<sigma>)"
| "OsubstFO (OProd ODE1 ODE2) \<sigma> = oprod (OsubstFO ODE1 \<sigma>) (OsubstFO ODE2 \<sigma>)"

primrec Osubst::"ODE \<Rightarrow> subst \<Rightarrow> ODE"
where
  "Osubst (OVar c sp ) \<sigma> = (case SODEs \<sigma> c sp of Some c' \<Rightarrow> c' | None \<Rightarrow> OVar c sp)"
| "Osubst (OSing x \<theta>) \<sigma> = OSing x (Tsubst \<theta> \<sigma>)"
| "Osubst (OProd ODE1 ODE2) \<sigma> = oprod (Osubst ODE1 \<sigma>) (Osubst ODE2 \<sigma>)"
  
fun PsubstFO::"hp \<Rightarrow> (ident \<Rightarrow> trm) \<Rightarrow> hp"
and FsubstFO::"formula \<Rightarrow> (ident \<Rightarrow> trm) \<Rightarrow> formula"
where
  "PsubstFO (Pvar a) \<sigma> = Pvar a"
| "PsubstFO (Assign x \<theta>) \<sigma> = Assign x (TsubstFO \<theta> \<sigma>)"
| "PsubstFO (AssignAny x) \<sigma> = AssignAny x"
| "PsubstFO (DiffAssign x \<theta>) \<sigma> = DiffAssign x (TsubstFO \<theta> \<sigma>)"
| "PsubstFO (Test \<phi>) \<sigma> = Test (FsubstFO \<phi> \<sigma>)"
| "PsubstFO (EvolveODE ODE \<phi>) \<sigma> = EvolveODE (OsubstFO ODE \<sigma>) (FsubstFO \<phi> \<sigma>)"
| "PsubstFO (Choice \<alpha> \<beta>) \<sigma> = Choice (PsubstFO \<alpha> \<sigma>) (PsubstFO \<beta> \<sigma>)"
| "PsubstFO (Sequence \<alpha> \<beta>) \<sigma> = Sequence (PsubstFO \<alpha> \<sigma>) (PsubstFO \<beta> \<sigma>)"
| "PsubstFO (Loop \<alpha>) \<sigma> = Loop (PsubstFO \<alpha> \<sigma>)"

| "FsubstFO (Geq \<theta>1 \<theta>2) \<sigma> = Geq (TsubstFO \<theta>1 \<sigma>) (TsubstFO \<theta>2 \<sigma>)"
| "FsubstFO (Prop p args) \<sigma> = Prop p (\<lambda>i. TsubstFO (args i) \<sigma>)"
| "FsubstFO (Not \<phi>) \<sigma> = Not (FsubstFO \<phi> \<sigma>)"
| "FsubstFO (And \<phi> \<psi>) \<sigma> = And (FsubstFO \<phi> \<sigma>) (FsubstFO \<psi> \<sigma>)"
| "FsubstFO (Exists x \<phi>) \<sigma> = Exists x (FsubstFO \<phi> \<sigma>)"
| "FsubstFO (Diamond \<alpha> \<phi>) \<sigma> = Diamond (PsubstFO \<alpha> \<sigma>) (FsubstFO \<phi> \<sigma>)"
| "FsubstFO (InContext C \<phi>) \<sigma> = InContext C (FsubstFO \<phi> \<sigma>)"
  
fun PPsubst::"hp \<Rightarrow> (ident \<Rightarrow> formula) \<Rightarrow> hp"
and PFsubst::"formula \<Rightarrow> (ident \<Rightarrow> formula) \<Rightarrow> formula"
where
  "PPsubst (Pvar a) \<sigma> = Pvar a"
| "PPsubst (Assign x \<theta>) \<sigma> = Assign x \<theta>"
| "PPsubst (AssignAny x) \<sigma> = AssignAny x"
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
| "PFsubst (InContext C \<phi>) \<sigma> = (case args_to_id C of Some (Inl C') \<Rightarrow> InContext C' (PFsubst \<phi> \<sigma>) | Some (Inr p') \<Rightarrow> \<sigma> p')"

  
fun Psubst::"hp \<Rightarrow> subst \<Rightarrow> hp"
and Fsubst::"formula \<Rightarrow> subst \<Rightarrow> formula"
where
  "Psubst (Pvar a) \<sigma> = (case SPrograms \<sigma> a of Some a' \<Rightarrow> a' | None \<Rightarrow> Pvar a)"
| "Psubst (Assign x \<theta>) \<sigma> = Assign x (Tsubst \<theta> \<sigma>)"
| "Psubst (AssignAny x) \<sigma> = AssignAny x"
| "Psubst (DiffAssign x \<theta>) \<sigma> = DiffAssign x (Tsubst \<theta> \<sigma>)"
| "Psubst (Test \<phi>) \<sigma> = Test (Fsubst \<phi> \<sigma>)"
| "Psubst (EvolveODE ODE \<phi>) \<sigma> = EvolveODE (Osubst ODE \<sigma>) (Fsubst \<phi> \<sigma>)"
| "Psubst (Choice \<alpha> \<beta>) \<sigma> = Choice (Psubst \<alpha> \<sigma>) (Psubst \<beta> \<sigma>)"
| "Psubst (Sequence \<alpha> \<beta>) \<sigma> = Sequence (Psubst \<alpha> \<sigma>) (Psubst \<beta> \<sigma>)"
| "Psubst (Loop \<alpha>) \<sigma> = Loop (Psubst \<alpha> \<sigma>)"

| "Fsubst (Geq \<theta>1 \<theta>2) \<sigma> = Geq (Tsubst \<theta>1 \<sigma>) (Tsubst \<theta>2 \<sigma>)"
| "Fsubst (Prop p args) \<sigma> = (case SPredicates \<sigma> p of Some p' \<Rightarrow> FsubstFO p' (\<lambda>i. Tsubst (args i) \<sigma>) | None \<Rightarrow> Prop p (\<lambda>i. Tsubst (args i) \<sigma>))"
| "Fsubst (Not \<phi>) \<sigma> = Not (Fsubst \<phi> \<sigma>)"
| "Fsubst (And \<phi> \<psi>) \<sigma> = And (Fsubst \<phi> \<sigma>) (Fsubst \<psi> \<sigma>)"
| "Fsubst (Exists x \<phi>) \<sigma> = Exists x (Fsubst \<phi> \<sigma>)"
| "Fsubst (Diamond \<alpha> \<phi>) \<sigma> = Diamond (Psubst \<alpha> \<sigma>) (Fsubst \<phi> \<sigma>)"
| "Fsubst (InContext C \<phi>) \<sigma> = (case SContexts \<sigma> C of Some C' \<Rightarrow> PFsubst C' (\<lambda> _. (Fsubst \<phi> \<sigma>)) | None \<Rightarrow>  InContext C (Fsubst \<phi> \<sigma>))"

definition FVA :: "(ident \<Rightarrow> trm) \<Rightarrow> (ident + ident) set"
where "FVA args = (\<Union> i. FVT (args i))"

fun SFV :: "subst \<Rightarrow> (ident + ident + ident) \<Rightarrow> (ident + ident) set"
where "SFV \<sigma> (Inl i) = (case SFunctions \<sigma> i of Some f' \<Rightarrow> FVT f' | None \<Rightarrow> {}) \<union> (case SFunls \<sigma> i of Some f' \<Rightarrow> FVT f' | None \<Rightarrow> {})"
| "SFV \<sigma> (Inr (Inl i)) = {}"
| "SFV \<sigma> (Inr (Inr i)) = (case SPredicates \<sigma> i of Some p' \<Rightarrow> FVF p' | None \<Rightarrow> {})"

definition FVS :: "subst \<Rightarrow> (ident + ident) set"
where "FVS \<sigma> = (\<Union>i. SFV \<sigma> i)"

definition SDom :: "subst \<Rightarrow> (ident + ident + ident) set"
where "SDom \<sigma> = 
   {Inl x | x. x \<in> dom (SFunctions \<sigma>)}
 \<union> {Inl x | x. x \<in> dom (SFunls \<sigma>)}
 \<union> {Inr (Inl x) | x. x \<in> dom (SContexts \<sigma>)}
 \<union> {Inr (Inr x) | x. x \<in> dom (SPredicates \<sigma>)} 
 \<union> {Inr (Inr x) | x. x \<in> dom (SPrograms \<sigma>)}"

definition TUadmit :: "subst \<Rightarrow> trm \<Rightarrow> (ident + ident) set \<Rightarrow> bool"
  where "TUadmit \<sigma> \<theta> U \<longleftrightarrow> 
  ((\<Union> i \<in> SIGT \<theta>. (case SFunctions \<sigma> i of Some f' \<Rightarrow> FVT f'  | None \<Rightarrow> {}) 
                \<union> (case SFunls \<sigma> i of Some f' \<Rightarrow> FVT f'  | None \<Rightarrow> {})) \<inter> U) = {}"

inductive Tadmit :: "subst \<Rightarrow> trm \<Rightarrow> bool"
where 
  Tadmit_Diff:"Tadmit \<sigma> \<theta> \<Longrightarrow> TUadmit \<sigma> \<theta> UNIV \<Longrightarrow> Tadmit \<sigma> (Differential \<theta>)"
| Tadmit_Fun1:"(\<forall>i. Tadmit \<sigma> (args i)) \<Longrightarrow> SFunctions \<sigma> f = Some f' \<Longrightarrow> TadmitFO (\<lambda> i. Tsubst (args i) \<sigma>) f' \<Longrightarrow> Tadmit \<sigma> (Function f args)"
| Tadmit_Fun2:"(\<forall>i. Tadmit \<sigma> (args i)) \<Longrightarrow> SFunctions \<sigma> f = None \<Longrightarrow> Tadmit \<sigma> (Function f args)"
| Tadmit_Funl:"SFunls \<sigma> f = Some f' \<Longrightarrow> Tadmit \<sigma> f' \<Longrightarrow> Tadmit \<sigma> ($$F f)"
| Tadmit_Neg:"Tadmit \<sigma> \<theta>1 \<Longrightarrow>  Tadmit \<sigma> (Neg \<theta>1)"
| Tadmit_Plus:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Tadmit \<sigma> (Plus \<theta>1 \<theta>2)"
| Tadmit_Times:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Tadmit \<sigma> (Times \<theta>1 \<theta>2)"
| Tadmit_Max:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Tadmit \<sigma> (Max \<theta>1 \<theta>2)"
| Tadmit_Min:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Tadmit \<sigma> (Min \<theta>1 \<theta>2)"
| Tadmit_Abs:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> (Abs \<theta>1)"
| Tadmit_DiffVar:"Tadmit \<sigma> (DiffVar x)"
| Tadmit_Var:"Tadmit \<sigma> (Var x)"
| Tadmit_Const:"Tadmit \<sigma> (Const r)"

inductive_simps
      Tadmit_Plus_simps[simp]: "Tadmit \<sigma> (Plus a b)"
  and Tadmit_Neg_simps[simp]: "Tadmit \<sigma> (Neg a)"
  and Tadmit_Times_simps[simp]: "Tadmit \<sigma> (Times a b)"
  and Tadmit_Max_simps[simp]: "Tadmit \<sigma> (Max a b)"
  and Tadmit_Min_simps[simp]: "Tadmit \<sigma> (Min a b)"
  and Tadmit_Abs_simps[simp]: "Tadmit \<sigma> (Abs a)"
  and Tadmit_Var_simps[simp]: "Tadmit \<sigma> (Var x)"
  and Tadmit_DiffVar_simps[simp]: "Tadmit \<sigma> (DiffVar x)"
  and Tadmit_Differential_simps[simp]: "Tadmit \<sigma> (Differential \<theta>)"
  and Tadmit_Const_simps[simp]: "Tadmit \<sigma> (Const r)"
  and Tadmit_Fun_simps[simp]: "Tadmit \<sigma> (Function i args)"
  and Tadmit_Funl_simps[simp]: "Tadmit \<sigma> ($$F i)"

inductive TadmitF :: "subst \<Rightarrow> trm \<Rightarrow> bool"
where 
  TadmitF_Diff:"TadmitF \<sigma> \<theta> \<Longrightarrow> TUadmit \<sigma> \<theta> UNIV \<Longrightarrow> TadmitF \<sigma> (Differential \<theta>)"
| TadmitF_Fun1:"(\<forall>i. TadmitF \<sigma> (args i)) \<Longrightarrow> SFunctions \<sigma> f = Some f' \<Longrightarrow> nonbase f \<Longrightarrow> ilength f < MAX_STR \<Longrightarrow> (\<forall>i. dfree (Tsubst (args i) \<sigma>)) \<Longrightarrow> TadmitFFO (\<lambda> i. Tsubst (args i) \<sigma>) f' \<Longrightarrow> TadmitF \<sigma> (Function f args)"
| TadmitF_Fun2:"(\<forall>i. TadmitF \<sigma> (args i)) \<Longrightarrow> SFunctions \<sigma> f = None    \<Longrightarrow> nonbase f \<Longrightarrow> ilength f < MAX_STR \<Longrightarrow> TadmitF \<sigma> (Function f args)"
| TadmitF_Neg:"TadmitF \<sigma> \<theta>1 \<Longrightarrow> TadmitF \<sigma> (Neg \<theta>1)"
| TadmitF_Plus:"TadmitF \<sigma> \<theta>1 \<Longrightarrow> TadmitF \<sigma> \<theta>2 \<Longrightarrow> TadmitF \<sigma> (Plus \<theta>1 \<theta>2)"
| TadmitF_Times:"TadmitF \<sigma> \<theta>1 \<Longrightarrow> TadmitF \<sigma> \<theta>2 \<Longrightarrow> TadmitF \<sigma> (Times \<theta>1 \<theta>2)"
| TadmitF_Max:"TadmitF \<sigma> \<theta>1 \<Longrightarrow> TadmitF \<sigma> \<theta>2 \<Longrightarrow> TadmitF \<sigma> (Max \<theta>1 \<theta>2)"
| TadmitF_Min:"TadmitF \<sigma> \<theta>1 \<Longrightarrow> TadmitF \<sigma> \<theta>2 \<Longrightarrow> TadmitF \<sigma> (Min \<theta>1 \<theta>2)"
| TadmitF_Abs:"TadmitF \<sigma> \<theta>1 \<Longrightarrow> TadmitF \<sigma> (Abs \<theta>1)"
| TadmitF_DiffVar:"TadmitF \<sigma> (DiffVar x)"
| TadmitF_Var:"TadmitF \<sigma> (Var x)"
| TadmitF_Const:"TadmitF \<sigma> (Const r)"

inductive_simps
      TadmitF_Plus_simps[simp]: "TadmitF \<sigma> (Plus a b)"
  and TadmitF_Times_simps[simp]: "TadmitF \<sigma> (Times a b)"
  and TadmitF_Neg_simps[simp]: "TadmitF \<sigma> (Neg a)"
  and TadmitF_Max_simps[simp]: "TadmitF \<sigma> (Max a b)"
  and TadmitF_Min_simps[simp]: "TadmitF \<sigma> (Min a b)"
  and TadmitF_Abs_simps[simp]: "TadmitF \<sigma> (Abs a)"
  and TadmitF_Var_simps[simp]: "TadmitF \<sigma> (Var x)"
  and TadmitF_DiffVar_simps[simp]: "TadmitF \<sigma> (DiffVar x)"
  and TadmitF_Differential_simps[simp]: "TadmitF \<sigma> (Differential \<theta>)"
  and TadmitF_Const_simps[simp]: "TadmitF \<sigma> (Const r)"
  and TadmitF_Fun_simps[simp]: "TadmitF \<sigma> (Function i args)"
  and TadmitF_Funl_simps[simp]: "TadmitF \<sigma> ($$F i)"

inductive Oadmit:: "subst \<Rightarrow> ODE \<Rightarrow> (ident + ident) set \<Rightarrow> bool"
where 
  Oadmit_Var:"Oadmit \<sigma> (OVar c None) U"
| Oadmit_VarNB:"(case SODEs \<sigma> c (Some x) of Some ode \<Rightarrow> Inl x \<notin> BVO ode | None \<Rightarrow> False) \<Longrightarrow> Oadmit \<sigma> (OVar c (Some x)) U"
| Oadmit_Sing:"TUadmit \<sigma> \<theta> U \<Longrightarrow> TadmitF \<sigma> \<theta> \<Longrightarrow> Oadmit \<sigma> (OSing x \<theta>) U"
| Oadmit_Prod:"Oadmit \<sigma> ODE1 U \<Longrightarrow> Oadmit \<sigma> ODE2 U \<Longrightarrow> ODE_dom (Osubst ODE1 \<sigma>) \<inter> ODE_dom (Osubst ODE2 \<sigma>) = {} \<Longrightarrow> Oadmit \<sigma> (OProd ODE1 ODE2) U"

inductive_simps
      Oadmit_Var_simps[simp]: "Oadmit \<sigma> (OVar c sp) U"
  and Oadmit_Sing_simps[simp]: "Oadmit \<sigma> (OSing x e) U"
  and Oadmit_Prod_simps[simp]: "Oadmit \<sigma> (OProd ODE1 ODE2) U"

definition PUadmit :: "subst \<Rightarrow> hp \<Rightarrow> (ident + ident) set \<Rightarrow> bool"
where "PUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> (SDom \<sigma> \<inter> SIGP \<theta>).  SFV \<sigma> i) \<inter> U) = {}"

definition FUadmit :: "subst \<Rightarrow> formula \<Rightarrow> (ident + ident) set \<Rightarrow> bool"
where "FUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> (SDom \<sigma> \<inter> SIGF \<theta>).  SFV \<sigma> i) \<inter> U) = {}"

definition OUadmitFO :: "(ident \<Rightarrow> trm) \<Rightarrow> ODE \<Rightarrow> (ident + ident) set \<Rightarrow> bool"
where "OUadmitFO \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> {i. Inl (debase i) \<in> SIGO \<theta>}. FVT (\<sigma> i)) \<inter> U) = {}"
 
inductive OadmitFO :: "(ident \<Rightarrow> trm) \<Rightarrow> ODE \<Rightarrow> (ident + ident) set \<Rightarrow> bool"
where 
  OadmitFO_OVar:"OUadmitFO \<sigma> (OVar c sp) U \<Longrightarrow> OadmitFO \<sigma> (OVar c sp) U"
| OadmitFO_OSing:"OUadmitFO \<sigma> (OSing x \<theta>) U \<Longrightarrow> TadmitFFO \<sigma> \<theta> \<Longrightarrow> OadmitFO \<sigma> (OSing x \<theta>) U"
| OadmitFO_OProd:"OadmitFO \<sigma> ODE1 U \<Longrightarrow> OadmitFO \<sigma> ODE2 U \<Longrightarrow> OadmitFO \<sigma> (OProd ODE1 ODE2) U"

inductive_simps
      OadmitFO_OVar_simps[simp]: "OadmitFO \<sigma> (OVar a sp) U"
  and OadmitFO_OProd_simps[simp]: "OadmitFO \<sigma> (OProd ODE1 ODE2) U"
  and OadmitFO_OSing_simps[simp]: "OadmitFO \<sigma> (OSing x e) U"
  
definition FUadmitFO :: "(ident \<Rightarrow> trm) \<Rightarrow> formula \<Rightarrow> (ident + ident) set \<Rightarrow> bool"
where "FUadmitFO \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> {i. Inl (debase i) \<in> SIGF \<theta> \<or> Inl (Debase i) \<in> SIGF \<theta>}. FVT (\<sigma> i)) \<inter> U) = {}"

definition PUadmitFO :: "(ident \<Rightarrow> trm) \<Rightarrow> hp \<Rightarrow> (ident + ident) set \<Rightarrow> bool"
where "PUadmitFO \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i  \<in> {i. Inl (debase i) \<in> SIGP \<theta> \<or> Inl (Debase i) \<in> SIGP \<theta>}. FVT (\<sigma> i)) \<inter> U) = {}"

inductive NPadmit :: "(ident \<Rightarrow> trm) \<Rightarrow> hp \<Rightarrow> bool" 
and NFadmit :: "(ident \<Rightarrow> trm) \<Rightarrow> formula \<Rightarrow> bool"
where
  NPadmit_Pvar:"NPadmit \<sigma> (Pvar a)"
| NPadmit_Sequence:"NPadmit \<sigma> a \<Longrightarrow> NPadmit \<sigma> b \<Longrightarrow> PUadmitFO \<sigma> b (BVP (PsubstFO a \<sigma>))\<Longrightarrow> hpsafe (PsubstFO a \<sigma>) \<Longrightarrow> NPadmit \<sigma> (Sequence a b)"  
| NPadmit_Loop:"NPadmit \<sigma> a \<Longrightarrow> PUadmitFO \<sigma> a (BVP (PsubstFO a \<sigma>)) \<Longrightarrow> hpsafe (PsubstFO a \<sigma>) \<Longrightarrow> NPadmit \<sigma> (Loop a)"        
| NPadmit_ODE:"OadmitFO \<sigma> ODE (BVO ODE) \<Longrightarrow> NFadmit \<sigma> \<phi> \<Longrightarrow> FUadmitFO \<sigma> \<phi> (BVO ODE) \<Longrightarrow> fsafe (FsubstFO \<phi> \<sigma>) \<Longrightarrow> osafe (OsubstFO ODE \<sigma>) \<Longrightarrow> NPadmit \<sigma> (EvolveODE ODE \<phi>)"
| NPadmit_Choice:"NPadmit \<sigma> a \<Longrightarrow> NPadmit \<sigma> b \<Longrightarrow> NPadmit \<sigma> (Choice a b)"            
| NPadmit_Assign:"TadmitFO \<sigma> \<theta> \<Longrightarrow> NPadmit \<sigma> (Assign x \<theta>)"  
| NPadmit_AssignAny:" NPadmit \<sigma> (AssignAny x)"  
| NPadmit_DiffAssign:"TadmitFO \<sigma> \<theta> \<Longrightarrow> NPadmit \<sigma> (DiffAssign x \<theta>)"  
| NPadmit_Test:"NFadmit \<sigma> \<phi> \<Longrightarrow> NPadmit \<sigma> (Test \<phi>)"

| NFadmit_Geq:"TadmitFO \<sigma> \<theta>1 \<Longrightarrow> TadmitFO \<sigma> \<theta>2 \<Longrightarrow> NFadmit \<sigma> (Geq \<theta>1 \<theta>2)"
| NFadmit_Prop:"(\<forall>i. TadmitFO \<sigma> (args i)) \<Longrightarrow> NFadmit \<sigma> (Prop f args)"
| NFadmit_Not:"NFadmit \<sigma> \<phi> \<Longrightarrow> NFadmit \<sigma> (Not \<phi>)"
| NFadmit_And:"NFadmit \<sigma> \<phi> \<Longrightarrow> NFadmit \<sigma> \<psi> \<Longrightarrow> NFadmit \<sigma> (And \<phi> \<psi>)"
| NFadmit_Exists:"NFadmit \<sigma> \<phi> \<Longrightarrow> FUadmitFO \<sigma> \<phi> {Inl x} \<Longrightarrow> NFadmit \<sigma> (Exists x \<phi>)"
| NFadmit_Diamond:"NFadmit \<sigma> \<phi> \<Longrightarrow> NPadmit \<sigma> a \<Longrightarrow> FUadmitFO \<sigma> \<phi> (BVP (PsubstFO a \<sigma>)) \<Longrightarrow> hpsafe (PsubstFO a \<sigma>) \<Longrightarrow> NFadmit \<sigma> (Diamond a \<phi>)"
| NFadmit_Context:"NFadmit \<sigma> \<phi> \<Longrightarrow> FUadmitFO \<sigma> \<phi> UNIV \<Longrightarrow> NFadmit \<sigma> (InContext C \<phi>)"

inductive_simps
      NPadmit_Pvar_simps[simp]: "NPadmit \<sigma> (Pvar a)"
  and NPadmit_Sequence_simps[simp]: "NPadmit \<sigma> (a ;; b)"
  and NPadmit_Loop_simps[simp]: "NPadmit \<sigma> (a**)"
  and NPadmit_ODE_simps[simp]: "NPadmit \<sigma> (EvolveODE ODE p)"
  and NPadmit_Choice_simps[simp]: "NPadmit \<sigma> (a \<union>\<union> b)"
  and NPadmit_Assign_simps[simp]: "NPadmit \<sigma> (Assign x e)"
  and NPadmit_AssignAny_simps[simp]: "NPadmit \<sigma> (AssignAny x)"
  and NPadmit_DiffAssign_simps[simp]: "NPadmit \<sigma> (DiffAssign x e)"
  and NPadmit_Test_simps[simp]: "NPadmit \<sigma> (? p)"
  
  and NFadmit_Geq_simps[simp]: "NFadmit \<sigma> (Geq t1 t2)"
  and NFadmit_Prop_simps[simp]: "NFadmit \<sigma> (Prop p args)"
  and NFadmit_Not_simps[simp]: "NFadmit \<sigma> (Not p)"
  and NFadmit_And_simps[simp]: "NFadmit \<sigma> (And p q)"
  and NFadmit_Exists_simps[simp]: "NFadmit \<sigma> (Exists x p)"
  and NFadmit_Diamond_simps[simp]: "NFadmit \<sigma> (Diamond a p)"
  and NFadmit_Context_simps[simp]: "NFadmit \<sigma> (InContext C p)"

definition PFUadmit :: "(ident \<Rightarrow> formula) \<Rightarrow> formula \<Rightarrow> (ident + ident) set \<Rightarrow> bool"
where "PFUadmit \<sigma> \<theta> U \<longleftrightarrow> True"

definition PPUadmit :: "(ident \<Rightarrow> formula) \<Rightarrow> hp \<Rightarrow> (ident + ident) set \<Rightarrow> bool"
where "PPUadmit \<sigma> \<theta> U \<longleftrightarrow> ((\<Union> i \<in> {i | i. Inr(Inl(debase i)) \<in> SIGP \<theta>}. FVF (\<sigma> i)) \<inter> U) = {}"

inductive PPadmit:: "(ident \<Rightarrow> formula) \<Rightarrow> hp \<Rightarrow> bool"
and PFadmit:: "(ident \<Rightarrow> formula) \<Rightarrow>  formula \<Rightarrow> bool"
where 
  PPadmit_Pvar:"PPadmit \<sigma> (Pvar a)"
| PPadmit_Sequence:"PPadmit \<sigma> a \<Longrightarrow> PPadmit \<sigma> b \<Longrightarrow> PPUadmit \<sigma> b (BVP (PPsubst a \<sigma>))\<Longrightarrow> hpsafe (PPsubst a \<sigma>) \<Longrightarrow> PPadmit \<sigma> (Sequence a b)"  
| PPadmit_Loop:"PPadmit \<sigma> a \<Longrightarrow> PPUadmit \<sigma> a (BVP (PPsubst a \<sigma>)) \<Longrightarrow> hpsafe (PPsubst a \<sigma>) \<Longrightarrow> PPadmit \<sigma> (Loop a)"        
| PPadmit_ODE:"PFadmit \<sigma> \<phi> \<Longrightarrow> PFUadmit \<sigma> \<phi> (BVO ODE) \<Longrightarrow> PPadmit \<sigma> (EvolveODE ODE \<phi>)"
| PPadmit_Choice:"PPadmit \<sigma> a \<Longrightarrow> PPadmit \<sigma> b \<Longrightarrow> PPadmit \<sigma> (Choice a b)"            
| PPadmit_Assign:"PPadmit \<sigma> (Assign x \<theta>)"  
| PPadmit_AssignAny:"PPadmit \<sigma> (AssignAny x)"  
| PPadmit_DiffAssign:"PPadmit \<sigma> (DiffAssign x \<theta>)"  
| PPadmit_Test:"PFadmit \<sigma> \<phi> \<Longrightarrow> PPadmit \<sigma> (Test \<phi>)"

| PFadmit_Geq:"PFadmit \<sigma> (Geq \<theta>1 \<theta>2)"
| PFadmit_Prop:"PFadmit \<sigma> (Prop f args)"
| PFadmit_Not:"PFadmit \<sigma> \<phi> \<Longrightarrow> PFadmit \<sigma> (Not \<phi>)"
| PFadmit_And:"PFadmit \<sigma> \<phi> \<Longrightarrow> PFadmit \<sigma> \<psi> \<Longrightarrow> PFadmit \<sigma> (And \<phi> \<psi>)"
| PFadmit_Exists:"PFadmit \<sigma> \<phi> \<Longrightarrow> PFUadmit \<sigma> \<phi> {Inl x} \<Longrightarrow> PFadmit \<sigma> (Exists x \<phi>)"
| PFadmit_Diamond:"PFadmit \<sigma> \<phi> \<Longrightarrow> PPadmit \<sigma> a \<Longrightarrow> PFUadmit \<sigma> \<phi> (BVP (PPsubst a \<sigma>)) \<Longrightarrow> PFadmit \<sigma> (Diamond a \<phi>)"
| PFadmit_Context:"PFadmit \<sigma> \<phi> \<Longrightarrow> PFUadmit \<sigma> \<phi> UNIV \<Longrightarrow> PFadmit \<sigma> (InContext C \<phi>)"

inductive_simps
      PPadmit_Pvar_simps[simp]: "PPadmit \<sigma> (Pvar a)"
  and PPadmit_Sequence_simps[simp]: "PPadmit \<sigma> (a ;; b)"
  and PPadmit_Loop_simps[simp]: "PPadmit \<sigma> (a**)"
  and PPadmit_ODE_simps[simp]: "PPadmit \<sigma> (EvolveODE ODE p)"
  and PPadmit_Choice_simps[simp]: "PPadmit \<sigma> (a \<union>\<union> b)"
  and PPadmit_Assign_simps[simp]: "PPadmit \<sigma> (Assign x e)"
  and PPadmit_AssignAny_simps[simp]: "PPadmit \<sigma> (AssignAny x)"
  and PPadmit_DiffAssign_simps[simp]: "PPadmit \<sigma> (DiffAssign x e)"
  and PPadmit_Test_simps[simp]: "PPadmit \<sigma> (? p)"
  
  and PFadmit_Geq_simps[simp]: "PFadmit \<sigma> (Geq t1 t2)"
  and PFadmit_Prop_simps[simp]: "PFadmit \<sigma> (Prop p args)"
  and PFadmit_Not_simps[simp]: "PFadmit \<sigma> (Not p)"
  and PFadmit_And_simps[simp]: "PFadmit \<sigma> (And p q)"
  and PFadmit_Exists_simps[simp]: "PFadmit \<sigma> (Exists x p)"
  and PFadmit_Diamond_simps[simp]: "PFadmit \<sigma> (Diamond a p)"
  and PFadmit_Context_simps[simp]: "PFadmit \<sigma> (InContext C p)"
  
inductive Padmit:: "subst \<Rightarrow> hp \<Rightarrow> bool"
and Fadmit:: "subst \<Rightarrow> formula \<Rightarrow> bool"
where
  Padmit_Pvar:"Padmit \<sigma> (Pvar a)"
| Padmit_Sequence:"Padmit \<sigma> a \<Longrightarrow> Padmit \<sigma> b \<Longrightarrow> PUadmit \<sigma> b (BVP (Psubst a \<sigma>))\<Longrightarrow> hpsafe (Psubst a \<sigma>) \<Longrightarrow> Padmit \<sigma> (Sequence a b)"  
| Padmit_Loop:"Padmit \<sigma> a \<Longrightarrow> PUadmit \<sigma> a (BVP (Psubst a \<sigma>)) \<Longrightarrow> hpsafe (Psubst a \<sigma>) \<Longrightarrow> Padmit \<sigma> (Loop a)"        
| Padmit_ODE:"Oadmit \<sigma> ODE (BVO ODE) \<Longrightarrow> Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> (BVO ODE) \<Longrightarrow> Padmit \<sigma> (EvolveODE ODE \<phi>)"
| Padmit_Choice:"Padmit \<sigma> a \<Longrightarrow> Padmit \<sigma> b \<Longrightarrow> Padmit \<sigma> (Choice a b)"            
| Padmit_Assign:"Tadmit \<sigma> \<theta> \<Longrightarrow> Padmit \<sigma> (Assign x \<theta>)"  
| Padmit_AssignAny:" Padmit \<sigma> (AssignAny x)"  
| Padmit_DiffAssign:"Tadmit \<sigma> \<theta> \<Longrightarrow> Padmit \<sigma> (DiffAssign x \<theta>)"  
| Padmit_Test:"Fadmit \<sigma> \<phi> \<Longrightarrow> Padmit \<sigma> (Test \<phi>)"

| Fadmit_Geq:"Tadmit \<sigma> \<theta>1 \<Longrightarrow> Tadmit \<sigma> \<theta>2 \<Longrightarrow> Fadmit \<sigma> (Geq \<theta>1 \<theta>2)"
| Fadmit_Prop1:"(\<forall>i. Tadmit \<sigma> (args i)) \<Longrightarrow> SPredicates \<sigma> p = Some p' \<Longrightarrow> NFadmit (\<lambda> i. Tsubst (args i) \<sigma>) p' \<Longrightarrow> (\<forall>i. dsafe (Tsubst (args i) \<sigma>))\<Longrightarrow> Fadmit \<sigma> (Prop p args)"
| Fadmit_Prop2:"(\<forall>i. Tadmit \<sigma> (args i)) \<Longrightarrow> SPredicates \<sigma> p = None \<Longrightarrow> Fadmit \<sigma> (Prop p args)"
| Fadmit_Not:"Fadmit \<sigma> \<phi> \<Longrightarrow> Fadmit \<sigma> (Not \<phi>)"
| Fadmit_And:"Fadmit \<sigma> \<phi> \<Longrightarrow> Fadmit \<sigma> \<psi> \<Longrightarrow> Fadmit \<sigma> (And \<phi> \<psi>)"
| Fadmit_Exists:"Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> {Inl x} \<Longrightarrow> Fadmit \<sigma> (Exists x \<phi>)"
| Fadmit_Diamond:"Fadmit \<sigma> \<phi> \<Longrightarrow> Padmit \<sigma> a \<Longrightarrow> FUadmit \<sigma> \<phi> (BVP (Psubst a \<sigma>)) \<Longrightarrow> hpsafe (Psubst a \<sigma>) \<Longrightarrow> Fadmit \<sigma> (Diamond a \<phi>)"
| Fadmit_Context1:"Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> UNIV \<Longrightarrow> SContexts \<sigma> C = Some C' \<Longrightarrow> PFadmit (\<lambda> _. Fsubst \<phi> \<sigma>) C' \<Longrightarrow> fsafe(Fsubst \<phi> \<sigma>) \<Longrightarrow> Fadmit \<sigma> (InContext C \<phi>)"
| Fadmit_Context2:"Fadmit \<sigma> \<phi> \<Longrightarrow> FUadmit \<sigma> \<phi> UNIV \<Longrightarrow> SContexts \<sigma> C = None \<Longrightarrow> Fadmit \<sigma> (InContext C \<phi>)"
  
inductive_simps
      Padmit_Pvar_simps[simp]: "Padmit \<sigma> (Pvar a)"
  and Padmit_Sequence_simps[simp]: "Padmit \<sigma> (a ;; b)"
  and Padmit_Loop_simps[simp]: "Padmit \<sigma> (a**)"
  and Padmit_ODE_simps[simp]: "Padmit \<sigma> (EvolveODE ODE p)"
  and Padmit_Choice_simps[simp]: "Padmit \<sigma> (a \<union>\<union> b)"
  and Padmit_Assign_simps[simp]: "Padmit \<sigma> (Assign x e)"
  and Padmit_AssignAny_simps[simp]: "Padmit \<sigma> (AssignAny x)"
  and Padmit_DiffAssign_simps[simp]: "Padmit \<sigma> (DiffAssign x e)"
  and Padmit_Test_simps[simp]: "Padmit \<sigma> (? p)"
  
  and Fadmit_Geq_simps[simp]: "Fadmit \<sigma> (Geq t1 t2)"
  and Fadmit_Prop_simps[simp]: "Fadmit \<sigma> (Prop p args)"
  and Fadmit_Not_simps[simp]: "Fadmit \<sigma> (Not p)"
  and Fadmit_And_simps[simp]: "Fadmit \<sigma> (And p q)"
  and Fadmit_Exists_simps[simp]: "Fadmit \<sigma> (Exists x p)"
  and Fadmit_Diamond_simps[simp]: "Fadmit \<sigma> (Diamond a p)"
  and Fadmit_Context_simps[simp]: "Fadmit \<sigma> (InContext C p)"
    
fun extendf :: "interp \<Rightarrow>  Rvec \<Rightarrow> interp"
where "extendf I R =
\<lparr>Functions = (\<lambda>f. case args_to_id f of Some (Inl f') \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> (\<lambda>_. R $ f') | None \<Rightarrow> Functions I f),
 Funls = (\<lambda>f. case args_to_id f of Some (Inl f') \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> (\<lambda>_. R $ f')  | None \<Rightarrow> Funls I f),
 Predicates = Predicates I,
 Contexts = Contexts I,
 Programs = Programs I,
 ODEs = ODEs I,
 ODEBV = ODEBV I
 \<rparr>"

fun extendc :: "interp \<Rightarrow> state set \<Rightarrow> interp"
where "extendc I R =
\<lparr>Functions =  Functions I,
 Funls = Funls I,
 Predicates = Predicates I,
 Contexts = (\<lambda>C. case args_to_id C of Some (Inl C') \<Rightarrow> Contexts I C' | Some (Inr _) \<Rightarrow> (\<lambda>_.  R) | None \<Rightarrow> Contexts I C),
 Programs = Programs I,
 ODEs = ODEs I,
 ODEBV = ODEBV I\<rparr>"

definition adjoint :: "interp \<Rightarrow> subst \<Rightarrow> state \<Rightarrow> interp" 
where adjoint_def:"adjoint I \<sigma> \<nu> =
\<lparr>Functions =   (\<lambda>f. case SFunctions \<sigma> f of Some f' \<Rightarrow> (\<lambda>R. dterm_sem (extendf I R) f' \<nu>) | None \<Rightarrow> Functions I f),
 Funls =       (\<lambda>f. case SFunls \<sigma> f of Some f' \<Rightarrow> (\<lambda>R. dterm_sem I f' \<nu>) | None \<Rightarrow> Funls I f),
 Predicates = (\<lambda>p. case SPredicates \<sigma> p of Some p' \<Rightarrow> (\<lambda>R. \<nu> \<in> fml_sem (extendf I R) p') | None \<Rightarrow> Predicates I p),
 Contexts =   (\<lambda>c. case SContexts \<sigma> c of Some c' \<Rightarrow> (\<lambda>R. fml_sem (extendc I R) c') | None \<Rightarrow> Contexts I c),
 Programs =   (\<lambda>a. case SPrograms \<sigma> a of Some a' \<Rightarrow> prog_sem I a' | None \<Rightarrow> Programs I a),
 ODEs =     (\<lambda>ode sp. case SODEs \<sigma> ode sp of Some ode' \<Rightarrow> ODE_sem I ode' | None \<Rightarrow> ODEs I ode sp),
 ODEBV = (\<lambda>ode sp . case SODEs \<sigma> ode sp of Some ode' \<Rightarrow> ODE_vars I ode' | None \<Rightarrow> ODEBV I ode sp)
 \<rparr>"

lemma dsem_to_ssem:"dfree \<theta> \<Longrightarrow> dterm_sem I \<theta> \<nu> = sterm_sem I \<theta> (fst \<nu>)"
    by (induct rule: dfree.induct) (auto)

definition adjointFO::"interp \<Rightarrow> (ident \<Rightarrow> trm) \<Rightarrow> state \<Rightarrow> interp" 
where "adjointFO I \<sigma> \<nu> =
\<lparr>Functions =   (\<lambda>f. case args_to_id f of Some (Inl f') \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> (\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) | None \<Rightarrow> Functions I f),
 Funls =  (\<lambda>f. case args_to_id f of Some (Inl f') \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> (\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) | None \<Rightarrow> Funls I f),
 Predicates = Predicates I,
 Contexts = Contexts I,
 Programs = Programs I,
 ODEs = ODEs I,
 ODEBV = ODEBV I
 \<rparr>"

lemma adjoint_free:
  assumes sfree:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
  shows "adjoint I \<sigma> \<nu> =
  \<lparr>Functions =  (\<lambda>f. case SFunctions \<sigma> f of Some f' \<Rightarrow> (\<lambda>R. sterm_sem (extendf I R) f' (fst \<nu>)) | None \<Rightarrow> Functions I f),
   Funls =  (\<lambda>f. case SFunls \<sigma> f of Some f' \<Rightarrow> (\<lambda>R. dterm_sem I f' \<nu>) | None \<Rightarrow> Funls I f),
   Predicates = (\<lambda>p. case SPredicates \<sigma> p of Some p' \<Rightarrow> (\<lambda>R. \<nu> \<in> fml_sem (extendf I R) p') | None \<Rightarrow> Predicates I p),
   Contexts =   (\<lambda>c. case SContexts \<sigma> c of Some c' \<Rightarrow> (\<lambda>R. fml_sem (extendc I R) c') | None \<Rightarrow> Contexts I c),
   Programs =   (\<lambda>a. case SPrograms \<sigma> a of Some a' \<Rightarrow> prog_sem I a' | None \<Rightarrow> Programs I a),
   ODEs =     (\<lambda>ode sp. case SODEs \<sigma> ode sp of Some ode' \<Rightarrow> ODE_sem I ode' | None \<Rightarrow> ODEs I ode sp),
   ODEBV = (\<lambda>ode sp. case SODEs \<sigma> ode sp of Some ode' \<Rightarrow> ODE_vars I ode' | None \<Rightarrow> ODEBV I ode sp)\<rparr>"
  using dsem_to_ssem[OF sfree] 
  apply (cases \<nu>)
  by (auto simp add: adjoint_def fun_eq_iff   dsem_to_ssem sfree split: option.split)
(*  subgoal for a b x x2
(*   apply (simp add: dsem_to_ssem sfree)*)
  using sfree[of x ]  sledgehammer*)
                                                 
lemma adjointFO_free:"(\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (adjointFO I \<sigma> \<nu> =
\<lparr>Functions =   (\<lambda>f. case args_to_id f of Some (Inl f') \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> (\<lambda>_. sterm_sem I (\<sigma> f') (fst \<nu>)) | None \<Rightarrow> Functions I f),
 Funls =   (\<lambda>f. case args_to_id f of Some (Inl f') \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> (\<lambda>_. sterm_sem I (\<sigma> f') (fst \<nu>)) | None \<Rightarrow> Funls I f),
 Predicates = Predicates I,
 Contexts = Contexts I,
 Programs = Programs I,
 ODEs = ODEs I,
 ODEBV = ODEBV I\<rparr>)" 
  apply (auto simp add: dsem_to_ssem adjointFO_def)
  using dsem_to_ssem by presburger+

definition PFadjoint::"interp \<Rightarrow> (ident \<Rightarrow> formula) \<Rightarrow> interp" 
where "PFadjoint I \<sigma> =
\<lparr>Functions =  Functions I,
 Funls =  Funls I,
 Predicates = Predicates I,
 Contexts = (\<lambda>f. case args_to_id f of Some (Inl f') \<Rightarrow> Contexts I f' | Some (Inr f') \<Rightarrow> (\<lambda>_. fml_sem I (\<sigma> f')) | None \<Rightarrow> Contexts I f),
 Programs = Programs I,
 ODEs = ODEs I,
 ODEBV = ODEBV I\<rparr>"


fun Ssubst::"sequent \<Rightarrow> subst \<Rightarrow> sequent"
where "Ssubst (\<Gamma>,\<Delta>) \<sigma> = (map (\<lambda> \<phi>. Fsubst \<phi> \<sigma>) \<Gamma>, map (\<lambda> \<phi>. Fsubst \<phi> \<sigma>) \<Delta>)"
  
fun Rsubst::"rule \<Rightarrow> subst \<Rightarrow> rule"
where "Rsubst (SG,C) \<sigma> = (map (\<lambda> \<phi>. Ssubst \<phi> \<sigma>) SG, Ssubst C \<sigma>)"

definition Sadmit::"subst \<Rightarrow> sequent \<Rightarrow> bool"
where "Sadmit \<sigma> S \<longleftrightarrow> ((\<forall>i. i \<ge> 0 \<longrightarrow> i < length (fst S) \<longrightarrow> Fadmit \<sigma> (nth (fst S) i))
                      \<and>(\<forall>i. i \<ge> 0 \<longrightarrow> i < length (snd S) \<longrightarrow> Fadmit \<sigma> (nth (snd S) i)))"

lemma Sadmit_code[code]:"Sadmit \<sigma> (A,S) \<longleftrightarrow> (list_all (Fadmit \<sigma>) A \<and> list_all (Fadmit \<sigma>) S)"
  apply (auto simp add: Sadmit_def)
  using list_all_length by blast+


definition Radmit::"subst \<Rightarrow> rule \<Rightarrow> bool"
where "Radmit \<sigma> R \<longleftrightarrow> (((\<forall>i. i \<ge> 0 \<longrightarrow> i < length (fst R) \<longrightarrow> Sadmit \<sigma> (nth (fst R) i)) 
                   \<and> Sadmit \<sigma> (snd R)))"

lemma Radmit_code[code]:"
Radmit \<sigma> R \<longleftrightarrow> (list_all (Sadmit \<sigma>) (fst R) \<and> Sadmit \<sigma> (snd R))"
  apply (auto simp add: Radmit_def)
  using list_all_length by blast+


end