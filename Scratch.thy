theory "Scratch"
imports Main  "./Proof_Checker"
begin
type_synonym arity = Enum.finite_5

(*code_thms dl.Proof_Checker.proof_result dl.Proof_Checker.proof_ok*)
(*print_codesetup*)
(*export_code dl.Proof_Checker.proof_ok dl.Proof_Checker.proof_result in SML*)
(*module_name Example file "examples/"**)
  
datatype myvars =
    i1
  | i2
  | i3
  | i4
  | i5
  
instantiation myvars :: finite begin
instance proof
  have "UNIV = {i1, i2, i3, i4, i5}"
    unfolding UNIV_def 
    using myvars.exhaust
    by (blast)
  moreover have "finite {i1, i2, i3, i4, i5}"
    by(auto)
  ultimately show "finite (UNIV:: myvars set)"
    by auto
qed
end
    
instantiation myvars :: linorder begin
definition less_eq_myvars where
  "x \<le> y \<equiv> 
  (case (x,y) of 
    (i1, _) \<Rightarrow> True
  | (i2, i1) \<Rightarrow> False
  | (i2, _) \<Rightarrow> True
  | (i3, i2) \<Rightarrow> False
  | (i3, i1) \<Rightarrow> False
  | (i3, _) \<Rightarrow> True
  | (i4, i4) \<Rightarrow> True
  | (i4, i5) \<Rightarrow> True
  | (i4, _) \<Rightarrow> False
  | (i5, i5) \<Rightarrow> True
  | (i5, _) \<Rightarrow> False)"

definition less_myvars where
  "x < y \<equiv> 
  (case (x,y) of 
    (i1, i1) \<Rightarrow> False 
  | (i1, _) \<Rightarrow> True
  | (i2, i1) \<Rightarrow> False
  | (i2, i2) \<Rightarrow> False
  | (i2, _) \<Rightarrow> True
  | (i3, i3) \<Rightarrow> False
  | (i3, i2) \<Rightarrow> False
  | (i3, i1) \<Rightarrow> False
  | (i3, _) \<Rightarrow> True
  | (i4, i5) \<Rightarrow> True
  | (i4, _) \<Rightarrow> False
  | (i5, _) \<Rightarrow> False)"

instance
  apply(standard)
  subgoal for x y    by(cases x, cases y, auto simp add: less_myvars_def less_eq_myvars_def, (metis myvars.exhaust myvars.simps)+)
  subgoal for x      by(cases x, auto simp add: less_myvars_def less_eq_myvars_def)
  subgoal for x y z  by(cases x, cases y, cases z, auto simp add: less_myvars_def less_eq_myvars_def, (metis myvars.exhaust myvars.simps)+)
  subgoal for x y    by(cases x, cases y, auto simp add: less_myvars_def less_eq_myvars_def, (metis myvars.exhaust myvars.simps)+)
  subgoal for x y    by(cases x, cases y, auto simp add: less_myvars_def less_eq_myvars_def, (metis myvars.exhaust myvars.simps)+)
  done
end
 
  

definition x::myvars where "x = i1"
definition y::myvars where "y = i2"
definition z::myvars where "z = i3"
definition w::myvars where "w = i4"
  
global_interpretation ddl:ids x y z x y z x y z w 
  by(standard, auto simp add: x_def y_def z_def w_def)
(* defines Tsubst = ddl.Tsubst*)

export_code "Differential_Dynamic_Logic.proof_result" in SML

(*definition foo::real where "foo = 1.234"
export_code foo in SML*)
end