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

 (*
code_thms dl.ids.NTsubst
print_codesetup
ex
port_code dl.ids.NTsubst in Haskell
module_name Example file "examples/"
*)
(*
definition x::Enum.finite_5 where "x = finite_5.a\<^sub>1"
global_interpretation ddl:ids x x x x x x x x x
  defines Tsubst = ddl.Tsubst
  done

term ddl.Tsubst
export_code "ddl.Tsubst" in SML
*)

(*definition foo::real where "foo = 1.234"
export_code foo in SML*)
end