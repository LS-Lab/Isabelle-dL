theory "Scratch"
imports Main 
begin
type_synonym arity = Enum.finite_5

datatype exp = 
   Const nat
 | Sum "arity \<Rightarrow> exp"

primrec eval :: "exp \<Rightarrow> nat"
  where
   "eval (Const n) = n"
 | "eval (Sum f) = (\<Sum>i\<in>(UNIV::arity set). eval (f i))"

\<theta>
end