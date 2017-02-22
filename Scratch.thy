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
    and   rrule_ok       = ddl.rrule_ok
    and   lrule_ok       = ddl.lrule_ok
    and   step_ok        = ddl.step_ok
    and   deriv_ok       = ddl.deriv_ok
    and   proof_ok       = ddl.proof_ok
    and   start_proof    = ddl.start_proof
    and   deriv_result   = ddl.deriv_result
    and   step_result    = ddl.step_result
    and   get_axiom      = ddl.get_axiom
    and   Rrule_result   = ddl.Rrule_result
    and   Lrule_result   = ddl.Lrule_result
    and   ssafe          = ddl.ssafe
    and   Padmit_Fadmit  = ddl.Padmit_Fadmit
    and   Padmit         = ddl.Padmit
    and   Fadmit         = ddl.Fadmit
    and   diff_times_axiom = ddl.diff_times_axiom
    and   diff_const_axiom = ddl.diff_const_axiom
    and   diff_plus_axiom = ddl.diff_plus_axiom
    and   DIGeqaxiom = ddl.DIGeqaxiom
    and   DIGraxiom = ddl.DIGraxiom
    and   DWaxiom = ddl.DWaxiom
    and   DSaxiom = ddl.DSaxiom
    and   DGaxiom = ddl.DGaxiom
    and   DEaxiom = ddl.DEaxiom
    and   DCaxiom = ddl.DCaxiom
    and   loop_iterate_axiom = ddl.loop_iterate_axiom
    and   diff_assign_axiom = ddl.diff_assign_axiom
    and   choice_axiom = ddl.choice_axiom
    and   assign_axiom = ddl.assign_axiom
    and   test_axiom = ddl.test_axiom
    and   box_axiom = ddl.box_axiom
    and   Vaxiom = ddl.Vaxiom
    and   Kaxiom = ddl.Kaxiom
    and   Iaxiom = ddl.Iaxiom
    and   state_fun = ddl.state_fun
    and   singleton = ddl.singleton
    and   p1 = ddl.p1
    and   f1 = ddl.f1
    and   f0 = ddl.f0
    and   P = ddl.P
  by(standard, auto simp add: x_def y_def z_def w_def)

declare ddl.deriv_ok.intros [code_pred_intro]
declare ddl.proof_ok.intros [code_pred_intro]
declare ddl.Padmit_Fadmit.intros [code_pred_intro]
(*declare ddl.step_ok.intros [code_pred_intro]*)
declare ddl.step_ok.Step_Axiom [code_pred_intro]
declare ddl.step_ok.Step_AxSubst [code_pred_intro]
declare ddl.step_ok.Step_Cut [code_pred_intro]
declare ddl.step_ok.Step_CloseId [code_pred_intro]
declare ddl.Step_G_code[code_pred_intro]
declare ddl.step_ok.Step_DEAxiom_schema [code_pred_intro]
declare ddl.step_ok.Step_Lrule[code_pred_intro]
declare ddl.Lrule_And_code[code_pred_intro]
declare ddl.Lrule_Imply_code[code_pred_intro]
declare ddl.Lrule_EquivForward_code[code_pred_intro]
declare ddl.Lrule_EquivBackward_code[code_pred_intro]
declare ddl.step_ok.Step_Rrule[code_pred_intro]
declare ddl.Rrule_And_code[code_pred_intro]
declare ddl.Rrule_Imply_code[code_pred_intro]
declare ddl.Rrule_Equiv_code[code_pred_intro]
declare ddl.Rrule_Cohide_code[code_pred_intro]
declare ddl.Rrule_CohideRR_code[code_pred_intro]
declare ddl.Rrule_True[code_pred_intro]


(*declare ddl.step_ok.Step_Rrule[code_pred_intro]*)

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as is_rrule_ok)
  rrule_ok
  sorry

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as is_step_ok)
  step_ok
  sorry

code_pred 
  (modes: i  \<Rightarrow> bool as is_proof_ok)
  proof_ok
  sorry
(*declare ddl.step_ok.Step_G [code_pred_intro]*)

  
(*  Step_Axiom:"(nth SG i) = ([], [get_axiom a]) \<Longrightarrow> step_ok (SG,C) i (Axiom a)"
| Step_AxSubst:"(nth SG i) = ([], [Fsubst (get_axiom a) \<sigma>]) \<Longrightarrow> Fadmit \<sigma> (get_axiom a) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> step_ok (SG,C) i (AxSubst a \<sigma>)"
| Step_Lrule:"lrule_ok SG C i j L \<Longrightarrow> j < length (fst (nth SG i)) \<Longrightarrow> step_ok (SG,C) i (Lrule L j)"
| Step_Rrule:"rrule_ok SG C i j L \<Longrightarrow> j < length (snd (nth SG i)) \<Longrightarrow> step_ok (SG,C) i (Rrule L j)"
| Step_Cut:"fsafe \<phi> \<Longrightarrow> i < length SG \<Longrightarrow> step_ok (SG,C) i (Cut \<phi>)"
| Step_CloseId:"nth (fst (nth SG i)) j = nth (snd (nth SG i)) k \<Longrightarrow> j < length (fst (nth SG i)) \<Longrightarrow> k < length (snd (nth SG i)) \<Longrightarrow> step_ok (SG,C) i (CloseId j k) "
| Step_G:"\<And>a p. nth SG i = ([], [([[a]]p)]) \<Longrightarrow> step_ok (SG,C) i G"
| Step_DEAxiom_schema:*)

export_code is_proof_ok proof_result in Scala



    
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