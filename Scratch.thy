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
    
  (*   fixes enum :: "'a list"
  fixes enum_all :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  fixes enum_ex :: "('a \<Rightarrow> bool) \<Rightarrow> bool"
  assumes UNIV_enum: "UNIV = set enum"
    and enum_distinct: "distinct enum"
  assumes enum_all_UNIV: "enum_all P \<longleftrightarrow> Ball UNIV P"
  assumes enum_ex_UNIV: "enum_ex P \<longleftrightarrow> Bex UNIV P" *)
instantiation myvars :: enum begin
definition enum_myvars where   "enum_myvars \<equiv> [i1, i2, i3, i4, i5]"
definition enum_all_myvars where "enum_all_myvars P \<equiv> list_all P [i1, i2, i3, i4, i5]"
definition enum_ex_myvars where "enum_ex_myvars P \<equiv> list_ex P [i1, i2, i3, i4, i5]"
instance
  apply(standard)
  subgoal apply auto
    subgoal for x
      by(cases x, auto simp add: enum_myvars_def)
    done
    apply (auto simp add: enum_myvars_def)
  subgoal for P x
    by(cases x, auto simp add: enum_myvars_def enum_all_myvars_def)
  subgoal for P
    by(auto simp add: enum_myvars_def enum_all_myvars_def)
  subgoal for P
    by(auto simp add: enum_myvars_def enum_ex_myvars_def)
  subgoal for P x
    by(cases x, auto simp add: enum_myvars_def enum_ex_myvars_def)
  done
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
  defines ddl_proof_result = "ddl.proof_result"
  and ddl_deriv_result = "ddl.deriv_result"
  and ddl_start_proof = "ddl.start_proof"
  and ddl_step_result = "ddl.step_result"
  and ddl_Rrule_result = "ddl.Rrule_result"
  and ddl_Lrule_result = "ddl.Lrule_result"
  by(standard, auto simp add: x_def y_def z_def w_def)
(* defines Tsubst = ddl.Tsubst*)

declare ddl.proof_result.simps[code_pred_simp]  ddl.deriv_result.simps[code_pred_simp] ddl.start_proof.simps[code_pred_simp] ddl.step_result.simps[code_pred_simp]
export_code "ddl_proof_result" in Scala

(*definition foo::real where "foo = 1.234"
export_code foo in SML*)
end