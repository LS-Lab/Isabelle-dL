theory "Example_System"
imports "./Proof_Checker"
begin
context ids begin

  section \<open>Example 2: Concrete Hybrid System\<close>

(* v \<ge> 0 \<and> A() \<ge> 0 \<longrightarrow> [v' = A, x' = v]v' \<ge> 0*)
definition SystemConcl::"('sf,'sc,'sz) sequent"
where "SystemConcl = 
  ([],[
  Implies (And (Geq (Var vid1) (Const 0)) (Geq (f0 fid1) (Const 0)))
  ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (TT)]]Geq (Var vid1) (Const 0))
  ])"

definition SystemDICut :: "('sf,'sc,'sz) formula"
where "SystemDICut =
  Implies
  (Implies TT ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]]
     (Geq (Differential (Var vid1)) (Differential (Const 0)))))
  (Implies
     (Implies TT (Geq (Var vid1) (Const 0)))
     ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (Var vid1) (Const 0))))"
(*
    (Implies (Geq (Var vid1) (Const 0)) 
      (Implies (And TT ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]]
                  (Geq (Differential (Var vid1)) (Differential (Const 0)))
   )) ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (Var vid1) (Const 0)))))"
*)  
definition SystemDCCut::"('sf,'sc,'sz) formula"
where "SystemDCCut =
(([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (f0 fid1) (Const 0))) \<rightarrow>
   (([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]]((Geq (Differential (Var vid1)) (Differential (Const 0))))) 
   \<leftrightarrow>  
   ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]](Geq (Differential (Var vid1)) (Differential (Const 0))))))"
  
definition SystemVCut::"('sf,'sc,'sz) formula"
where "SystemVCut = 
  Implies (Geq (f0 fid1) (Const 0)) ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]](Geq (f0 fid1) (Const 0)))" 

definition SystemVCut2::"('sf,'sc,'sz) formula"
where "SystemVCut2 = 
  Implies (Geq (f0 fid1) (Const 0)) ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (f0 fid1) (Const 0)))" 

definition SystemDECut::"('sf,'sc,'sz) formula"
where "SystemDECut = (([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]] ((Geq (Differential (Var vid1)) (Differential (Const 0))))) \<leftrightarrow>
 ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]]
    [[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential (Const 0)))))"

definition SystemKCut::"('sf,'sc,'sz) formula"
where "SystemKCut =
  (Implies ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]]
                (Implies ((And TT (Geq (f0 fid1) (Const 0)))) ([[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential (Const 0))))))
      (Implies ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]] ((And TT (Geq (f0 fid1) (Const 0)))))
               ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]] ([[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential (Const 0)))))))"

definition SystemEquivCut::"('sf,'sc,'sz) formula"
where "SystemEquivCut =
  (Equiv (Implies ((And TT (Geq (f0 fid1) (Const 0)))) ([[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential (Const 0)))))
         (Implies ((And TT (Geq (f0 fid1) (Const 0)))) ([[DiffAssign vid1 (f0 fid1)]](Geq (DiffVar vid1) (Const 0)))))"

definition SystemDiffAssignCut::"('sf,'sc,'sz) formula"
where "SystemDiffAssignCut =
  (([[DiffAssign vid1  ($f fid1 empty)]] (Geq (DiffVar vid1) (Const 0)))
\<leftrightarrow> (Geq ($f fid1 empty) (Const 0)))"
  
definition SystemCEFml1::"('sf,'sc,'sz) formula"
where "SystemCEFml1 = Geq (Differential (Var vid1)) (Differential (Const 0))"

definition SystemCEFml2::"('sf,'sc,'sz) formula"
where "SystemCEFml2 = Geq (DiffVar vid1) (Const 0)"


(*
definition diff_const_axiom :: "formula"
  where [axiom_defs]:"diff_const_axiom \<equiv> Equals (Differential ($f fid1 empty)) (Const 0)"

definition diff_var_axiom :: "formula"
  where [axiom_defs]:"diff_var_axiom \<equiv> Equals (Differential (Var vid1)) (DiffVar vid1)"*)

  
definition CQ1Concl::"('sf,'sc,'sz) formula"
where "CQ1Concl = (Geq (Differential (Var vid1)) (Differential (Const 0)) \<leftrightarrow> Geq (DiffVar vid1) (Differential (Const 0)))"

definition CQ2Concl::"('sf,'sc,'sz) formula"
where "CQ2Concl = (Geq (DiffVar vid1) (Differential (Const 0)) \<leftrightarrow> Geq ($' vid1) (Const 0))"

definition CEReq::"('sf,'sc,'sz) formula"
where "CEReq = (Geq (Differential (trm.Var vid1)) (Differential (Const 0)) \<leftrightarrow> Geq ($' vid1) (Const 0))"

definition CQRightSubst::"('sf,'sc,'sz) subst"
where "CQRightSubst = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>p. (if p = vid1 then (Some (Geq (DiffVar vid1) (Function  (Inr vid1)  empty))) else None)),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"


definition CQLeftSubst::"('sf,'sc,'sz) subst"
where "CQLeftSubst = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>p. (if p = vid1 then (Some (Geq  (Function  (Inr vid1)  empty) (Differential (Const 0)))) else None)),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

definition CEProof::"('sf,'sc,'sz) pf"
where "CEProof = (([],[CEReq]), [
  (0, Cut CQ1Concl)
 ,(0, Cut CQ2Concl)
 ,(1, Rrule CohideRR 0)
 ,(Suc (Suc 0), CQ (Differential (Const 0)) (Const 0) CQRightSubst)
 ,(1, Rrule CohideRR 0)
 ,(1, CQ (Differential (Var vid1)) (DiffVar vid1) CQLeftSubst)
 ,(0, Rrule EquivR 0)
 ,(0, Lrule EquivForwardL 1)
 ,(Suc (Suc 0), Lrule EquivForwardL 1)
 ,(Suc (Suc (Suc 0)), CloseId 0 0)
 ,(Suc (Suc 0), CloseId 0 0)
 ,(Suc 0, CloseId 0 0)
 ,(0, Lrule EquivBackwardL (Suc (Suc 0)))
 ,(0, CloseId 0 0)
 ,(0, Lrule EquivBackwardL (Suc 0))
 ,(0, CloseId 0 0)
 ,(0, CloseId 0 0)
 ])"  

lemma CE_result_correct:"proof_result CEProof = ([],([],[CEReq]))"
  unfolding CEProof_def CEReq_def CQ1Concl_def  CQ2Concl_def Implies_def Or_def f0_def TT_def Equiv_def Box_def CQRightSubst_def
  by (auto simp add: id_simps)

definition DiffConstSubst::"('sf,'sc,'sz) subst"
where "DiffConstSubst = \<lparr>
    SFunctions = (\<lambda>f. (if f = fid1 then (Some (Const 0)) else None)),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

definition DiffConstProof::"('sf,'sc,'sz) pf"
where "DiffConstProof = (([],[(Equals (Differential (Const 0)) (Const 0))]), [
  (0, AxSubst AdConst DiffConstSubst)])"

lemma diffconst_result_correct:"proof_result DiffConstProof = ([], ([],[Equals (Differential (Const 0)) (Const 0)]))"
  by(auto simp add: prover DiffConstProof_def)

lemma diffconst_sound_lemma:"sound (proof_result DiffConstProof)"
  apply(rule proof_sound)
  unfolding DiffConstProof_def
  by (auto simp add: prover DiffConstProof_def DiffConstSubst_def Equals_def empty_def TUadmit_def)
  
lemma valid_of_sound:"sound ([], ([],[\<phi>])) \<Longrightarrow> valid \<phi>"
  unfolding valid_def sound_def TT_def FF_def 
  apply (auto simp add: TT_def FF_def Or_def)
  subgoal for I a b
    apply(erule allE[where x=I])
    by(auto)
  done

lemma almost_diff_const_sound:"sound ([], ([], [Equals (Differential (Const 0)) (Const 0)]))"
  using diffconst_result_correct diffconst_sound_lemma by simp

lemma almost_diff_const:"valid (Equals (Differential (Const 0)) (Const 0))"
  using almost_diff_const_sound valid_of_sound by auto

(* Note: this is just unpacking the definition: the axiom is defined as literally this formula *)
lemma almost_diff_var:"valid (Equals (Differential (trm.Var vid1)) ($' vid1))"
  using diff_var_axiom_valid unfolding diff_var_axiom_def by auto

lemma CESound_lemma:"sound (proof_result CEProof)"
  apply(rule proof_sound)
  unfolding CEProof_def CEReq_def CQ1Concl_def CQ2Concl_def Equiv_def CQRightSubst_def diff_const_axiom_valid diff_var_axiom_valid empty_def Or_def expand_singleton 
  diff_var_axiom_def
  by (auto simp add: prover CEProof_def CEReq_def CQ1Concl_def CQ2Concl_def Equiv_def
    CQRightSubst_def diff_const_axiom_valid diff_var_axiom_valid empty_def Or_def expand_singleton 
    TUadmit_def NTUadmit_def almost_diff_const CQLeftSubst_def almost_diff_var)

lemma sound_to_valid:"sound ([], ([], [\<phi>])) \<Longrightarrow> valid \<phi>"
  unfolding  valid_def apply auto
  apply(drule soundD_mem)
  by (auto simp add: member_rec(2))
  
lemma CE1pre:"sound ([], ([], [CEReq]))"  
  using CE_result_correct CESound_lemma 
  by simp
                            
lemma CE1pre_valid:"valid CEReq"
  by (rule sound_to_valid[OF CE1pre])
    
lemma CE1pre_valid2:"valid (! (! (Geq (Differential (trm.Var vid1)) (Differential (Const 0)) && Geq ($' vid1) (Const 0)) &&
              ! (! (Geq (Differential (trm.Var vid1)) (Differential (Const 0))) && ! (Geq ($' vid1) (Const 0))))) "
  using CE1pre_valid unfolding CEReq_def Equiv_def Or_def by auto

definition SystemDISubst::"('sf,'sc,'sz) subst"
where "SystemDISubst = 
  \<lparr> SFunctions = (\<lambda>f. 
    (     if f = fid1 then Some(Function (Inr vid1) empty)
     else if f = fid2 then Some(Const 0)
     else None)),
    SPredicates = (\<lambda>p. if p = vid1 then Some TT else None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>c. if c = vid1 then Some (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (trm.Var vid1))) else None)
  \<rparr>"
  
  (*
  Implies 
  (Implies (Prop vid1 empty) ([[EvolveODE (OVar vid1) (Prop vid1 empty)]](Geq (Differential (f1 fid1 vid1)) (Differential (f1 fid2 vid1)))))
  (Implies
     (Implies(Prop vid1 empty) (Geq (f1 fid1 vid1) (f1 fid2 vid1)))
     ([[EvolveODE (OVar vid1) (Prop vid1 empty)]](Geq (f1 fid1 vid1) (f1 fid2 vid1))))"
*)
(*
Implies
  (Implies TT ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]]
     (Geq (Differential (Var vid1)) (Differential (Const 0)))))
  (Implies
     (Implies TT (Geq (Var vid1) (Const 0)))
     ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (Var vid1) (Const 0))))
*)

definition SystemDCSubst::"('sf,'sc,'sz) subst"
where "SystemDCSubst = 
  \<lparr> SFunctions = (\<lambda>
  f.  None),
    SPredicates = (\<lambda>p.  None),
    SContexts = (\<lambda>C. 
    if C = pid1 then
      Some TT
    else if C = pid2 then
      Some (Geq (Differential (Var vid1)) (Differential (Const 0)))
    else if C = pid3 then
      Some (Geq (Function fid1 empty) (Const 0)) 
    else 
     None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>c. if c = vid1 then Some (OProd (OSing vid1 (Function fid1 empty)) (OSing vid2 (trm.Var vid1))) else None)
  \<rparr>"

definition SystemVSubst::"('sf,'sc,'sz) subst"
where "SystemVSubst = 
  \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>p. if p = vid1 then Some (Geq (Function (Inl fid1) empty) (Const 0)) else None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>a. if a = vid1 then 
      Some (EvolveODE (OProd 
                         (OSing vid1 (Function fid1 empty)) 
                         (OSing vid2 (Var vid1))) 
                      (And TT (Geq (Function fid1 empty) (Const 0)))) 
                      else None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

definition SystemVSubst2::"('sf,'sc,'sz) subst"
where "SystemVSubst2 = 
  \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>p. if p = vid1 then Some (Geq (Function (Inl fid1) empty) (Const 0)) else None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>a. if a = vid1 then 
      Some (EvolveODE (OProd 
                         (OSing vid1 (Function fid1 empty)) 
                         (OSing vid2 (Var vid1))) 
                      TT) 
                      else None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

definition SystemDESubst::"('sf,'sc,'sz) subst"
where "SystemDESubst = 
  \<lparr> SFunctions = (\<lambda>f. if f = fid1 then Some(Function (Inl fid1) empty) else None),
    SPredicates = (\<lambda>p. if p = vid2 then Some(And TT (Geq (Function (Inl fid1) empty) (Const 0))) else None),
    SContexts = (\<lambda>C. if C = pid1 then Some(Geq (Differential (Var vid1)) (Differential (Const 0))) else None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

lemma systemdesubst_correct:"\<exists> ODE.(([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]] ((Geq (Differential (Var vid1)) (Differential (Const 0))))) \<leftrightarrow>
 ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]]
    [[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential (Const 0)))))
    = Fsubst ((([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1)) ODE) (p1 vid2 vid1)]] (P pid1)) \<leftrightarrow>
          ([[EvolveODE ((OProd  (OSing vid1 (f1 fid1 vid1))) ODE) (p1 vid2 vid1)]]
               [[DiffAssign vid1 (f1 fid1 vid1)]]P pid1))) SystemDESubst"
  apply(rule exI[where x="OSing vid2 (trm.Var vid1)"])
  by(auto simp add: f0_def f1_def Box_def Or_def Equiv_def empty_def TT_def P_def p1_def SystemDESubst_def empty_def)
  
(*[{dx=, dy=x&r>=r&>=r}]r>=r&>=r->[D{x}:=]D{x}>=D{r}->
  [{dx=, dy=x&r>=r&>=r}]r>=r&>=r->
  [{dx=, dy=x&r>=r&>=r}][D{x}:=]D{x}>=D{r}
  ([[$\<alpha> vid1]]((Predicational pid1) \<rightarrow> (Predicational pid2)))
    \<rightarrow> ([[$\<alpha> vid1]]Predicational pid1) \<rightarrow> ([[$\<alpha> vid1]]Predicational pid2)
  *)
definition SystemKSubst::"('sf,'sc,'sz) subst"
where "SystemKSubst = \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. if C = pid1 then 
        (Some (And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0)))) 
      else if C = pid2 then 
        (Some ([[DiffAssign vid1 (Function fid1 empty)]](Geq (Differential (Var vid1)) (Differential (Const 0))))) else None),
    SPrograms = (\<lambda>c. if c = vid1 then Some (EvolveODE (OProd (OSing vid1 (Function fid1 empty)) (OSing vid2 (Var vid1))) (And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0)))) else None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

lemma subst_imp_simp:"Fsubst (Implies p q) \<sigma> = (Implies (Fsubst p \<sigma>) (Fsubst q \<sigma>))"
  unfolding Implies_def Or_def by auto

lemma subst_equiv_simp:"Fsubst (Equiv p q) \<sigma> = (Equiv (Fsubst p \<sigma>) (Fsubst q \<sigma>))"
  unfolding Implies_def Or_def Equiv_def by auto

lemma subst_box_simp:"Fsubst (Box p q) \<sigma> = (Box (Psubst p \<sigma>) (Fsubst q \<sigma>))"
  unfolding Box_def Or_def by auto

lemma pfsubst_box_simp:"PFsubst (Box p q) \<sigma> = (Box (PPsubst p \<sigma>) (PFsubst q \<sigma>))"
  unfolding Box_def Or_def by auto

lemma pfsubst_imp_simp:"PFsubst (Implies p q) \<sigma> = (Implies (PFsubst p \<sigma>) (PFsubst q \<sigma>))"
  unfolding Box_def Implies_def Or_def by auto

definition SystemDWSubst::"('sf,'sc,'sz) subst"
where "SystemDWSubst = \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. if C = pid1 then Some (And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0))) else None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>c. if c = vid1 then Some (OProd (OSing vid1 (Function fid1 empty)) (OSing vid2 (Var vid1))) else None)
  \<rparr>"

definition SystemCESubst::"('sf,'sc,'sz) subst"
where "SystemCESubst = \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. if C = pid1 then Some(Implies(And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0))) ([[DiffAssign vid1 (Function fid1 empty)]](Predicational (Inr ())))) else None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

lemma SystemCESubstOK:
  "step_ok 
  ([([],[Equiv (Implies(And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0))) ([[DiffAssign vid1 (Function fid1 empty)]]( SystemCEFml1))) 
         (Implies(And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0))) ([[DiffAssign vid1 (Function fid1 empty)]]( (SystemCEFml2))))
         ])],
         ([],[]))
         
         0 
         (CE SystemCEFml1 SystemCEFml2 SystemCESubst)"
  apply(rule Step_CE)
       subgoal by(auto simp add: subst_equiv_simp subst_imp_simp subst_box_simp SystemCESubst_def SystemCEFml1_def SystemCEFml2_def pfsubst_imp_simp pfsubst_box_simp)
      subgoal using CE1pre_valid 
        by (auto simp add: CEReq_def SystemCEFml1_def SystemCEFml2_def CE1pre_valid)
     subgoal unfolding SystemCEFml1_def by auto
    subgoal unfolding SystemCEFml2_def by auto
   subgoal unfolding SystemCESubst_def ssafe_def Implies_def Box_def Or_def empty_def by auto
  unfolding SystemCESubst_def Equiv_def Or_def SystemCEFml1_def SystemCEFml2_def TUadmit_def apply (auto simp add: TUadmit_def FUadmit_def Box_def Implies_def Or_def)
     unfolding PFUadmit_def by auto
  
(* [D{x}:=f]Dv{x}>=r<->f>=r
 [[DiffAssign vid1  ($f fid1 empty)]] (Prop vid1 (singleton (DiffVar vid1))))
      \<leftrightarrow> Prop vid1 (singleton ($f fid1 empty))*)
definition SystemDiffAssignSubst::"('sf,'sc,'sz) subst"
where "SystemDiffAssignSubst = \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>p. if p = vid1 then Some (Geq (Function (Inr vid1) empty) (Const 0)) else None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

lemma SystemDICutCorrect:"SystemDICut = Fsubst DIGeqaxiom SystemDISubst"
  unfolding SystemDICut_def DIGeqaxiom_def SystemDISubst_def 
  by (auto simp add: f1_def p1_def f0_def Implies_def Or_def id_simps TT_def Box_def empty_def)

(* v\<ge>0 \<and> A()\<ge>0 \<rightarrow> [{x'=v, v'=A()}]v\<ge>0 *)
definition SystemProof :: "('sf, 'sc, 'sz) pf"
where "SystemProof =
  (SystemConcl, [
  (0, Rrule ImplyR 0)
  ,(0, Lrule AndL 0)
  ,(0, Cut SystemDICut)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, Lrule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc 0, AxSubst ADIGeq SystemDISubst) (* 8 *)
  ,(Suc 0, Rrule ImplyR 0)
(*  ,(0, CloseId 0 0)        *)
  ,(Suc 0, CloseId 1 0)        
(*  ,(0, Rrule AndR 0)*)
  ,(0, Rrule ImplyR 0)   
  ,(0, Cut SystemDCCut)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, Lrule EquivBackwardL 0)
  ,(0, Rrule CohideR 0)
  ,(0, AxSubst ADC SystemDCSubst) (* 17 *)
  ,(0, CloseId 0 0)
  ,(0, Rrule CohideRR 0)
  ,(0, Cut SystemVCut)
  ,(0, Lrule ImplyL 0) 
  ,(0, Rrule CohideRR 0)
  ,(0, Cut SystemDECut)
  ,(0, Lrule EquivBackwardL 0)
  ,(0, Rrule CohideRR 0)
  ,(1, CloseId (Suc 1) 0) (* Last step *)
  ,(Suc 1, CloseId 0 0)
  ,(1, AxSubst AV SystemVSubst) (* 28 *)
  ,(0, Cut SystemVCut2)
  
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc 1, CloseId 0 0)
  ,(Suc 1, CloseId (Suc 2) 0)
  
  ,(Suc 1, AxSubst AV SystemVSubst2) (* 34 *)
  ,(0, Rrule CohideRR 0)
  ,(0, DEAxiomSchema (OSing vid2 (trm.Var vid1)) SystemDESubst) (* 36 *)
  ,(0, Cut SystemKCut)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, AxSubst AK SystemKSubst) (* 42 *)
  ,(0, CloseId 0 0)
  ,(0, Rrule CohideR 0)
  ,(1, AxSubst ADW SystemDWSubst) (* 45 *)
  ,(0, G)
  ,(0, Cut SystemEquivCut)
  ,(0, Lrule EquivBackwardL 0)
  ,(0, Rrule CohideR 0)
  ,(0, CloseId 0 0)
  ,(0, Rrule CohideR 0)
  ,(0, CE SystemCEFml1 SystemCEFml2 SystemCESubst) (* 52 *)
  ,(0, Rrule ImplyR 0)
  ,(0, Lrule AndL 0)
  ,(0, Cut SystemDiffAssignCut) 
  ,(0, Lrule EquivBackwardL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, CloseId 0 0)
  ,(0, CloseId 1 0)
  ,(0, AxSubst Adassign SystemDiffAssignSubst) (* 60 *)
  ])"
  
lemma system_result_correct:"proof_result SystemProof = 
  ([],
  ([],[Implies (And (Geq (Var vid1) (Const 0)) (Geq (f0 fid1) (Const 0)))
        ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (TT)]]Geq (Var vid1) (Const 0))]))"
  unfolding SystemProof_def SystemConcl_def Implies_def Or_def f0_def TT_def Equiv_def SystemDICut_def SystemDCCut_def
  proof_result.simps deriv_result.simps start_proof.simps  Box_def SystemDCSubst_def SystemVCut_def SystemDECut_def SystemKCut_def SystemEquivCut_def
  SystemDiffAssignCut_def SystemVCut2_def
    (* slow *)
  apply( simp add:  prover)
  done

lemma SystemSound_lemma:"sound (proof_result SystemProof)"
  apply(rule proof_sound)
  unfolding SystemProof_def SystemConcl_def CQ1Concl_def CQ2Concl_def Equiv_def CQRightSubst_def diff_const_axiom_valid diff_var_axiom_valid empty_def Or_def expand_singleton 
  diff_var_axiom_def SystemDICut_def
  (* slow *)
  apply (auto simp add: prover CEProof_def CEReq_def CQ1Concl_def CQ2Concl_def Equiv_def
    CQRightSubst_def diff_const_axiom_valid diff_var_axiom_valid empty_def Or_def expand_singleton 
    TUadmit_def NTUadmit_def almost_diff_const CQLeftSubst_def almost_diff_var f0_def TT_def SystemDISubst_def f1_def p1_def SystemDCCut_def SystemDCSubst_def
    SystemVCut_def SystemDECut_def SystemVSubst_def
    SystemVCut2_def SystemVSubst2_def  SystemDESubst_def P_def SystemKCut_def  SystemKSubst_def SystemDWSubst_def SystemEquivCut_def
    SystemCESubst_def SystemCEFml1_def SystemCEFml2_def CE1pre_valid2 SystemDiffAssignCut_def SystemDiffAssignSubst_def)
  done

lemma system_sound:"sound ([], SystemConcl)"
  using SystemSound_lemma system_result_correct unfolding SystemConcl_def by auto
  

  
end end