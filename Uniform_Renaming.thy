theory "Uniform_Renaming" 
imports
  Complex_Main
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
  "./Ids"
  "./Lib"
  "./Syntax"
  "./Denotational_Semantics"
  "./Frechet_Correctness"
  "./Static_Semantics"
  "./Coincidence"
  "./Bound_Effect"
begin

fun swap ::"'sz \<Rightarrow> 'sz \<Rightarrow> 'sz \<Rightarrow> 'sz"
where "swap x y z = (if z = x then  y else if z = y then x else z)"
  
primrec TUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> ('sf, 'sz) trm"
where 
  "TUrename x y (Var z) = Var (swap x y z)"
| "TUrename x y (DiffVar z) = DiffVar (swap x y z)"
| "TUrename x y (Const r) = (Const r)"
| "TUrename x y (Function f args) = Function f (\<lambda>i. TUrename x y (args i))"
| "TUrename x y (Plus \<theta>1 \<theta>2) = Plus (TUrename x y \<theta>1) (TUrename x y \<theta>2)"
| "TUrename x y (Times \<theta>1 \<theta>2) = Times (TUrename x y \<theta>1) (TUrename x y \<theta>2)"
| "TUrename x y (Differential \<theta>) = Differential (TUrename x y \<theta>)"
  
primrec OUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sz) ODE \<Rightarrow> ('sf, 'sz) ODE"
where
  "OUrename x y (OVar c) = undefined"
| "OUrename x y (OSing z \<theta>) = OSing (swap x y z) (TUrename x y \<theta>)"
| "OUrename x y (OProd ODE1 ODE2) = OProd (OUrename x y ODE1) (OUrename x y ODE2)"
  
primrec PUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sc, 'sz) hp \<Rightarrow> ('sf, 'sc, 'sz) hp"
and FUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sc, 'sz) formula \<Rightarrow> ('sf, 'sc, 'sz) formula"
where
  "PUrename x y (Pvar a) = undefined"
| "PUrename x y (Assign z \<theta>) = Assign (swap x y z) (TUrename x y \<theta>)"
| "PUrename x y (DiffAssign z \<theta>) = DiffAssign (swap x y z) (TUrename x y \<theta>)"
| "PUrename x y (Test \<phi>) = Test (FUrename x y \<phi>)"
| "PUrename x y (EvolveODE ODE \<phi>) = EvolveODE (OUrename x y ODE) (FUrename x y \<phi>)"
| "PUrename x y (Choice a b) = Choice (PUrename x y a) (PUrename x y b)"
| "PUrename x y (Sequence a b) = Sequence (PUrename x y a) (PUrename x y b)"
| "PUrename x y (Loop a) = Loop (PUrename x y a)"

| "FUrename x y (Geq \<theta>1 \<theta>2) = Geq (TUrename x y \<theta>1) (TUrename x y \<theta>2)"
| "FUrename x y (Prop p args) = Prop p (\<lambda>i. TUrename x y (args i))"
| "FUrename x y (Not \<phi>) = Not (FUrename x y \<phi>)"
| "FUrename x y (And \<phi> \<psi>) = And (FUrename x y \<phi>) (FUrename x y \<psi>)"
| "FUrename x y (Exists z \<phi>) = Exists (swap x y z) (FUrename x y \<phi>)"
| "FUrename x y (Diamond \<alpha> \<phi>) = Diamond (PUrename x y \<alpha>) (FUrename x y \<phi>)"
| "FUrename x y (DiffFormula \<phi>) = undefined"
| "FUrename x y (InContext C \<phi>) = undefined"


end