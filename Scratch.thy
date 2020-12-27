theory "Scratch"
imports Main  "./Proof_Checker"
begin
type_synonym arity = Enum.finite_5

(* Code snippet for coset code generation credit to Andreas Lochbihler *) 
lemma set_fold_remove1:
  "distinct ys \<Longrightarrow> set (fold remove1 xs ys) = set ys - set xs"
  by(induction xs arbitrary: ys) auto

lemma coset_enum:
  "List.coset xs = set (fold remove1 xs Enum.enum)"
  by(auto simp add: set_fold_remove1 enum_distinct UNIV_enum[symmetric])

lemma image_coset [code]:
  "f ` List.coset xs = set (map f (fold remove1 xs Enum.enum))"
  by(simp only: coset_enum set_map)    

instantiation bword :: equal begin
definition equal_bword :: "bword \<Rightarrow> bword \<Rightarrow> bool"
  where "equal_bword \<equiv> (\<lambda>x y. sint (Rep_bword x) = sint (Rep_bword y))"
instance
  apply(standard)
  by(auto simp add: equal_bword_def Rep_bword_inject)
end

 
  




inductive is_i1::"ident \<Rightarrow> bool"
  where i1_is_i1:"is_i1 x"
(*
definition x::myvars where "x = i1"
definition y::myvars where "y = i2"
definition z::myvars where "z = i3"
definition w::myvars where "w = i4"

inductive is_i1::"myvars \<Rightarrow> bool"
  where i1_is_i1:"is_i1 i1"*)
(*
global_interpretation ddl: ids Ix Iy Iz "is_i1" Ix Iy Iz Ix Iy Iz Iw
  defines ddl_pt_result = "ddl.pt_result"
  and ddl_rule_result = "ddl.rule_result"
  and ddl_start_proof = "ddl.start_proof"
  and ddl_RightRule_result = "ddl.RightRule_result"
  and ddl_LeftRule_result = "ddl.LeftRule_result"
  and ddl_merge_rules = "ddl.merge_rules"
  and ddl_get_axrule = "ddl.get_axrule"
  and ddl_pro = "ddl.pro"
  and ddl_fnc = "ddl.fnc"
  and ddl_Radmit = "ddl.Radmit"
  and ddl_Sadmit = "ddl.Sadmit"
  and ddl_Rsubst = "ddl.Rsubst"
  and ddl_Ssubst = "ddl.Ssubst"
  and ddl_TUrename = "ddl.TUrename"
  and ddl_PUrename = "ddl.PUrename"
  and ddl_swap = "ddl.swap"
  and ddl_SUrename = "ddl.SUrename"
  and ddl_SBrename = "ddl.SBrename"
  and ddl_FUrename = "ddl.FUrename"
  and ddl_OUrename = "ddl.OUrename"
  and ddl_FBrename = "ddl.FBrename"
  and ddl_is_singleton = "ddl.is_singleton"
  and ddl_sing_at = "ddl.sing_at"
  and ddl_ssafe = "ddl.ssafe"

  and ddl_singleton = "ddl.singleton"
  and ddl_get_axiom = "ddl.get_axiom"
  and ddl_p1 = "ddl.p1"
  and ddl_f1 = "ddl.f1"
  and ddl_P = "ddl.P"  

  and ddl_diff_times_axiom = "ddl.diff_times_axiom"
  and ddl_diff_const_axiom = "ddl.diff_const_axiom"
  and ddl_diff_plus_axiom = "ddl.diff_plus_axiom"
  and ddl_DIGeqaxiom = ddl.DIGeqaxiom
  and ddl_DIGraxiom =  ddl.DIGraxiom
  and ddl_DWaxiom =  ddl.DWaxiom
  and ddl_DSaxiom =  ddl.DSaxiom
  and ddl_DGaxiom =  ddl.DGaxiom
  and ddl_DEaxiom =  ddl.DEaxiom
  and ddl_DCaxiom =  ddl.DCaxiom
  and ddl_loop_iterate_axiom =  ddl.loop_iterate_axiom
  and ddl_diff_assign_axiom =  ddl.diff_assign_axiom
  and ddl_choice_axiom =   ddl.choice_axiom
  and ddl_assign_axiom =   ddl.assign_axiom
  and ddl_test_axiom =   ddl.test_axiom
  and ddl_box_axiom =   ddl.box_axiom
  and ddl_Vaxiom =   ddl.Vaxiom
  and ddl_Kaxiom =  ddl.Kaxiom
  and ddl_Iaxiom =  ddl.Iaxiom
  and ddl_CTaxrule = ddl.CTaxrule
  and ddl_CQaxrule = ddl.CQaxrule
  and ddl_CEaxrule = ddl.CEaxrule 
  and ddl_Gaxrule = ddl.Gaxrule
  and ddl_state_fun = ddl.state_fun
  and ddl_constFcongAxiom = ddl.constFcongAxiom
  and ddl_DiffLinearAxiom = ddl.DiffLinearAxiom
  and ddl_compose_axiom = ddl.compose_axiom
  and ddl_assignEqAxiom = ddl.assignEqAxiom
  and ddl_BoxSplitAxiom = ddl.BoxSplitAxiom
  and ddl_allInstAxiom = ddl.allInstAxiom
  and ddl_ImpSelfAxiom = ddl.ImpSelfAxiom
  and ddl_AllElimAxiom = ddl.AllElimAxiom
  and ddl_dMinusAxiom = ddl.dMinusAxiom
  and ddl_diamondModusPonensAxiom = ddl.diamondModusPonensAxiom
  and ddl_lessEqualReflAxiom = ddl.lessEqualReflAxiom
  and ddl_equalReflAxiom = ddl.equalReflAxiom
  and ddl_TrueImplyAxiom = ddl.TrueImplyAxiom
  and ddl_composedAxiom = ddl.composedAxiom
  and ddl_randomdAxiom = ddl.randomdAxiom
  and ddl_diamondAxiom = ddl.diamondAxiom
  and ddl_choicedAxiom = ddl.choicedAxiom
  and ddl_assigndAxiom = ddl.assigndAxiom
  and ddl_testdAxiom = ddl.testdAxiom

  and ddl_f0 = ddl.f0

  and ddl_diff_var_axiom = "ddl.diff_var_axiom"
  and ddl_EquivReflexiveAxiom = "ddl.EquivReflexiveAxiom"
  and ddl_DiffEffectSysAxiom = "ddl.DiffEffectSysAxiom"
  and ddl_monbrule = "ddl.monbrule"
 and ddl_join = "ddl.join"
 and ddl_vid_to_string = "ddl.vid_to_string"
 and  ddl_oid_to_string = "ddl.oid_to_string"
 and ddl_cid_to_string = "ddl.cid_to_string"
 and ddl_ppid_to_string = "ddl.ppid_to_string"
 and ddl_hpid_to_string = "ddl.hpid_to_string"
 and ddl_fid_to_string = "ddl.fid_to_string"
and ddl_trm_to_string = "ddl.trm_to_string"
and ddl_ode_to_string = "ddl.ode_to_string"
and ddl_fml_to_string = "ddl.fml_to_string"
 and ddl_hp_to_string = "ddl.hp_to_string"
and ddl_seq_to_string = "ddl.seq_to_string"
and ddl_rule_to_string = "ddl.rule_to_string"
and ddl_Oadmit = "ddl.Oadmit"
and ddl_Fadmit = "ddl.Fadmit"
and ddl_TRadmit = "ddl.TRadmit"
and ddl_FRadmit = "ddl.FRadmit"
and ddl_assignAnyAxiom = "ddl.assignAnyAxiom"
and ddl_equalCommuteAxiom = "ddl.equalCommuteAxiom"
and ddl_Rsafe = "ddl.Rsafe"
  apply(standard, auto simp add: Ix_def Iy_def Iz_def Iw_def is_i1.intros)
  using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq Iy.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq Iz_def Iw_def Ix_def Iy_def apply auto
  done


*)
  (*  
declare 
ddl.pt_result.simps[code_pred_simp]  
ddl.rule_result.simps[code_pred_simp] 
ddl.start_proof.simps[code_pred_simp] 
singleton_def[code_pred_simp]
ddl.get_axiom.simps[code_pred_simp]
ddl.p1_def[code_pred_simp]
ddl.f1_def[code_pred_simp]
ddl.P_def[code_pred_simp]  
singleton_def[code_pred_simp]
Syntax.hpsafe_fsafe.intros[code_pred_intro]
Syntax.osafe.intros[code_pred_intro]
Syntax.dsafe.intros[code_pred_intro]
Syntax.dfree.intros[code_pred_intro]
ddl.Oadmit.intros[code_pred_intro]
ddl.Padmit_Fadmit.intros[code_pred_intro]
ddl.TRadmit.intros[code_pred_intro]
ddl.PRadmit_FRadmit.intros[code_pred_intro]

Syntax.hpsafe_fsafe.intros[code_pred_intro]
Syntax.osafe.intros[code_pred_intro]
Syntax.dsafe.intros[code_pred_intro]
Syntax.dfree.intros[code_pred_intro]

*)
declare 
(*ddl.is_singleton.intros[code_pred_intro]
ddl.sing_at.intros[code_pred_intro]*)
is_i1.intros[code_pred_intro]


code_pred (modes: i \<Rightarrow> bool as is1_i) "is_i1"
by (rule is_i1.cases)

(*code_pred (modes: i \<Rightarrow> i  \<Rightarrow> i \<Rightarrow> bool as sing_at_i) "ddl_sing_at"
  by(rule ddl.sing_at.cases)

code_pred (modes: o \<Rightarrow> i \<Rightarrow> bool as is_singleton_i) "ddl_is_singleton"
  by(rule ddl.is_singleton.cases)*)

code_pred "Syntax.dfree".
code_pred "Syntax.osafe".
code_pred "Syntax.fsafe".


code_pred "TRadmit".
code_pred  (modes: i \<Rightarrow>  bool as fradmit_i) "FRadmit".


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as oadmit_i) "Oadmit".

code_pred (modes: i \<Rightarrow> i \<Rightarrow>  bool as fadmit_i) "Fadmit".
(*
  *)  
(*

definition ssafe ::"('sf, 'sc, 'sz) subst \<Rightarrow> bool"
where "ssafe \<sigma> \<equiv>
  (\<forall> i. case SFunctions \<sigma> i  of Some f' \<Rightarrow> dfree f' | None \<Rightarrow> True) \<and> 
  (\<forall> f. case SPredicates \<sigma> f of Some f' \<Rightarrow> fsafe f' | None \<Rightarrow> True) \<and>
  (\<forall> F. case SFunls \<sigma> F of Some f' \<Rightarrow> dsafe f' | None \<Rightarrow> True) \<and>
  (\<forall> f. case SPrograms \<sigma> f   of Some f' \<Rightarrow> hpsafe f'| None \<Rightarrow> True) \<and>
  (\<forall> f sp. case SODEs \<sigma> f sp  of Some f' \<Rightarrow> osafe f' | None \<Rightarrow> True) \<and>
  (\<forall> f x. case SODEs \<sigma> f (Some x)  of Some f' \<Rightarrow> Inl x \<notin> BVO f' | None \<Rightarrow> True) \<and>
  (\<forall> C. case SContexts \<sigma> C   of Some C' \<Rightarrow> fsafe C' | None \<Rightarrow> True)"
*)

(*
definition string_enum :: "string list" 
  where "string_enum = vals_inner"
definition string_enum_all :: "(string \<Rightarrow> bool) \<Rightarrow> bool"
  where "string_enum_all = (\<lambda> f. list_all f vals_inner)"
definition string_enum_ex :: "(string \<Rightarrow> bool) \<Rightarrow> bool"
  where "string_enum_ex = (\<lambda> f. list_ex f vals_inner)"

lift_definition ident_enum::"ident list" is string_enum
  done
lift_definition ident_enum_all::"(ident \<Rightarrow> bool) \<Rightarrow> bool" is string_enum_all
  done
lift_definition ident_enum_ex::"(ident \<Rightarrow> bool) \<Rightarrow> bool" is string_enum_ex
  done
*)
(*declare  ident_expose_def[code]  *)

(*export_code "pt_result" in Scala*)
(*
export_code "ddl_ssafe" in Scala
export_code "ddl_start_proof" in Scala
  code_pred (modes: i \<Rightarrow> i \<Rightarrow> bool as fadmit_i) "ddl.Fadmit" 
  done
*)
(*export_code "ddl_pt_result" in Scala*)


(*export_code ddl_rule_to_string in Scala*)

(* 
subsection \<open>Implementation of Polynomial Mappings as Association Lists\<close>

lift_definition Pm_fmap::"('a, 'b::zero) fmap \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b" is lookup0
  by (rule finite_lookup_default)

lemmas [simp] = Pm_fmap.rep_eq

code_datatype Pm_fmap

lemma PM_clearjunk0_cong:
  "Pm_fmap (clearjunk0 xs) = Pm_fmap xs"
  by (metis Pm_fmap.rep_eq lookup0_clearjunk0 poly_mapping_eqI)

*)

(*definition "blerh =  (\<chi> i::3. ((5)::real))"
export_code blerh in Scala*)

end