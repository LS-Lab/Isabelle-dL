theory "Scratch"
imports Main  "./Proof_Checker"
begin
  


type_synonym arity = Enum.finite_5


datatype myvars =
    i1
  | i2
  | i3
  | i4
  | i5

    
instantiation myvars :: enum begin
definition "enum_myvars == [i1, i2, i3, i4, i5]"
definition "enum_all_myvars = (\<lambda>f. f i1 \<and> f i2 \<and> f i3 \<and> f i4 \<and> f i5)"
definition "enum_ex_myvars = (\<lambda>f. f i1 \<or> f i2 \<or> f i3 \<or> f i4 \<or> f i5)"
instance 
  apply(standard)
  subgoal 
    apply(auto simp add: enum_myvars_def)
    using myvars.exhaust enum_myvars_def by blast
  subgoal
    by(auto simp add: enum_myvars_def) 
  subgoal for P
    apply(unfold enum_all_myvars_def)
    by (metis UNIV_I myvars.exhaust)
  subgoal for P
    apply(unfold enum_ex_myvars_def)
    by (metis UNIV_I myvars.exhaust)
  done      
end
  
(*instantiation myvars :: finite begin
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
  *)
    
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


  
global_interpretation ddl : ids x y z x y z x y z w
  defines proof_result   = ddl.proof_result
    and   step_ok        = ddl.step_ok
    and   deriv_ok       = ddl.deriv_ok
    and   proof_ok       = ddl.proof_ok
    and   start_proof    = ddl.start_proof
    and   deriv_result   = ddl.deriv_result
    and   step_result    = ddl.step_result
    and   Rrule_result   = ddl.Rrule_result
    and   Lrule_result   = ddl.Lrule_result
  by(standard, auto simp add: x_def y_def z_def w_def)

code_pred (modes: i \<Rightarrow> bool as is_dsafe) dsafe.    
    
export_code is_dsafe in Scala
declare ddl.step_ok.intros [code_pred_intro]
declare ddl.deriv_ok.intros [code_pred_intro]
declare ddl.proof_ok.intros [code_pred_intro]

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as is_step_ok)
  step_ok
  by (rule ddl.step_ok.cases)

    
export_code "step_ok.equation" in Scala

code_pred deriv_ok 
   apply(auto simp add: ddl.deriv_ok.cases)
   apply (metis ddl.deriv_ok.cases fst_conv)
    sorry
(*   apply (meson ddl.step_ok.cases fst_conv insert_disjoint(2) snd_conv)*)*

export_code "deriv_ok" in Scala

code_pred proof_ok 
  sorry
    sorry

(*  apply(auto)
  subgoal
    by (simp add: ddl.proof_ok_simps)
  subgoal
    by (metis ddl.deriv_ok.cases fst_conv)
(*  apply(auto simp add: ddl.step_ok.cases fst_conv insert_disjoint(2) snd_conv)*)
    sorry
    *)
             
(*definition deriv_result::"((myvars, myvars, myvars) formula list \<times> (myvars, myvars, myvars) formula list) list \<times>
  (myvars, myvars, myvars) formula list \<times> (myvars, myvars, myvars) formula list
  \<Rightarrow> (nat \<times> (myvars, myvars, myvars) ddl.step) list
     \<Rightarrow> ((myvars, myvars, myvars) formula list \<times> (myvars, myvars, myvars) formula list) list \<times>
        (myvars, myvars, myvars) formula list \<times> (myvars, myvars, myvars) formula list"
where "deriv_result = ids.deriv_result"

*)
(*lemmas [code] = ddl.deriv_result.simps[folded  proof_result_def]
lemmas [code] = ddl.proof_result.simps[folded deriv_result_def proof_result_def]
lemmas [code] = deriv_result_def[symmetric]*)

(*lemmas [code] = ddl.proof_result.simps[folded proof_result_def]
lemmas [code] = proof_result_def[symmetric]*)
lemmas [code] = enum_all_myvars_def enum_ex_myvars_def enum_myvars_def  
  
code_pred "proof_ok"

(*code_pred "ddl.proof_ok"*)
export_code "proof_result"  "proof_ok" in SML

definition test 
where "test = ddl.get_axiom"
(*code_thms "ids.get_axioms"*)
(*print_codesetup*)
(*export_code dl.Proof_Checker.proof_ok dl.Proof_Checker.proof_result in SML*)
(*module_name Example file "examples/"**)
  
(*print_codesetup*)
(*=export_code "ids.Tsubst" in SM*)
export_code "ddl.Tsubst" in SML

(* defines Tsubst = ddl.Tsubst*)

(*definition foo::real where "foo = 1.234"
export_code foo in SML*)
end