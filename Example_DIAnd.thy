theory "Example_DIAnd"
imports "./Proof_Checker"
begin
context ids begin
  section \<open>Example 1: Differential Invariants\<close>

definition DIAndConcl::"('sf,'sc,'sz) sequent"
where "DIAndConcl = ([], [Implies (And (Predicational pid1) (Predicational pid2)) 
       (Implies ([[Pvar vid1]](And (Predicational pid3) (Predicational pid4))) 
                ([[Pvar vid1]](And (Predicational pid1) (Predicational pid2))))])"

definition DIAndSG1::"('sf,'sc,'sz) formula"
where "DIAndSG1 = (Implies (Predicational pid1) (Implies ([[Pvar vid1]](Predicational pid3)) ([[Pvar vid1]](Predicational pid1))))"

definition DIAndSG2::"('sf,'sc,'sz) formula"
where "DIAndSG2 = (Implies (Predicational pid2) (Implies ([[Pvar vid1]](Predicational pid4)) ([[Pvar vid1]](Predicational pid2))))"

definition DIAndCut::"('sf,'sc,'sz) formula"
where "DIAndCut = 
  (([[$\<alpha> vid1]]((And (Predicational ( pid3)) (Predicational ( pid4)))) \<rightarrow> (And (Predicational ( pid1)) (Predicational ( pid2))))
    \<rightarrow> ([[$\<alpha> vid1]](And (Predicational ( pid3)) (Predicational ( pid4)))) \<rightarrow> ([[$\<alpha> vid1]](And (Predicational (pid1)) (Predicational ( pid2)))))"
  
definition DIAndSubst::"('sf,'sc,'sz) subst"
where "DIAndSubst = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. (if C = pid1 then Some(And (Predicational (Inl pid3)) (Predicational (Inl pid4))) 
                else (if C = pid2 then Some(And (Predicational (Inl pid1)) (Predicational (Inl pid2))) else None))),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"
  
(*[a]R&H->R->[a]R&H->[a]R DIAndSubst34*)

definition DIAndSubst341::"('sf,'sc,'sz) subst"
where "DIAndSubst341 = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. (if C = pid1 then Some(And (Predicational (Inl pid3)) (Predicational (Inl pid4))) 
                else (if C = pid2 then Some(Predicational (Inl pid3)) else None))),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"
definition DIAndSubst342::"('sf,'sc,'sz) subst"
where "DIAndSubst342 = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. (if C = pid1 then Some(And (Predicational (Inl pid3)) (Predicational (Inl pid4))) 
                else (if C = pid2 then Some(Predicational (Inl pid4)) else None))),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"
  
(*[a]P, [a]R&H, P, Q |- [a]Q->P&Q->[a]Q->[a]P&Q, [a]P&Q;;*)
definition DIAndSubst12::"('sf,'sc,'sz) subst"
where "DIAndSubst12 = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. (if C = pid1 then Some(Predicational (Inl pid2)) 
                else (if C = pid2 then Some(Predicational (Inl pid1) && Predicational (Inl pid2)) else None))),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

  (*  P ->  Q->P&Q *)
definition DIAndCurry12::"('sf,'sc,'sz) subst"
where "DIAndCurry12 = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. (if C = pid1 then Some(Predicational (Inl pid1)) 
                else (if C = pid2 then Some(Predicational (Inl pid2) \<rightarrow> (Predicational (Inl pid1) && Predicational (Inl pid2))) else None))),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"
  
definition DIAnd :: "rule" 
where "DIAnd = 
  ([([],[DIAndSG1]),([],[DIAndSG2])], 
  DIAndConcl)"

definition DIAndCutP1 :: "('sf,'sc,'sz) formula"
where "DIAndCutP1 = ([[Pvar vid1]](Predicational pid1))" 

definition DIAndCutP2 :: "('sf,'sc,'sz) formula"
where "DIAndCutP2 = ([[Pvar vid1]](Predicational pid2))" 

definition DIAndCutP12 :: "('sf,'sc,'sz) formula"
where "DIAndCutP12 = (([[Pvar vid1]](Pc pid1) \<rightarrow> (Pc pid2 \<rightarrow> (And (Pc pid1) (Pc pid2))))
  \<rightarrow> (([[Pvar vid1]]Pc pid1) \<rightarrow> ([[Pvar vid1]](Pc pid2 \<rightarrow> (And (Pc pid1) (Pc pid2))))))" 

definition DIAndCut34Elim1 :: "('sf,'sc,'sz) formula"
where "DIAndCut34Elim1 = (([[Pvar vid1]](Pc pid3 && Pc pid4) \<rightarrow> (Pc pid3))
  \<rightarrow> (([[Pvar vid1]](Pc pid3 && Pc pid4)) \<rightarrow> ([[Pvar vid1]](Pc pid3))))" 

definition DIAndCut34Elim2 :: "('sf,'sc,'sz) formula"
where "DIAndCut34Elim2 = (([[Pvar vid1]](Pc pid3 && Pc pid4) \<rightarrow> (Pc pid4))
  \<rightarrow> (([[Pvar vid1]](Pc pid3 && Pc pid4)) \<rightarrow> ([[Pvar vid1]](Pc pid4))))" 

definition DIAndCut12Intro :: "('sf,'sc,'sz) formula"
where "DIAndCut12Intro = (([[Pvar vid1]](Pc pid2  \<rightarrow> (Pc pid1 && Pc pid2)))
  \<rightarrow> (([[Pvar vid1]](Pc pid2)) \<rightarrow> ([[Pvar vid1]](Pc pid1 && Pc pid2))))" 

definition DIAndProof :: "('sf, 'sc, 'sz) pf"
where "DIAndProof =
  (DIAndConcl, [
   (0, Rrule ImplyR 0)  (* 1 *)
  ,(0, Lrule AndL 0)
  ,(0, Rrule ImplyR 0)
  ,(0, Cut DIAndCutP1)
  ,(1, Cut DIAndSG1)
  ,(0, Rrule CohideR 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc (Suc (Suc 0)), CloseId 1 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc (Suc 0), Cut DIAndCut34Elim1) (* 11 *)
  ,(0, Lrule ImplyL 0)
  ,(Suc (Suc (Suc 0)), Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc 0, Rrule CohideRR 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), G)  
  ,(0, Rrule ImplyR 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), Lrule AndL 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), CloseId 0 0)
  ,(Suc (Suc (Suc 0)), AxSubst AK DIAndSubst341) (* 21 *)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc 0, CloseId 0 0)
  ,(0, Cut DIAndCut12Intro)
  ,(Suc 0, Rrule CohideRR 0)
  ,(Suc (Suc 0), AxSubst AK DIAndSubst12)
  ,(0, Lrule ImplyL 0)
  ,(1, Lrule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc 0, Cut DIAndCutP12)
  ,(0, Lrule ImplyL 0) (* 31 *)
  ,(0, Rrule CohideRR 0)
  ,(Suc (Suc (Suc (Suc 0))), AxSubst AK DIAndCurry12)
  ,(Suc (Suc (Suc 0)), Rrule CohideRR 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc (Suc 0), G)  
  ,(0, Rrule ImplyR 0)  
  ,(Suc (Suc (Suc (Suc 0))), Rrule ImplyR 0)  
  ,(Suc (Suc (Suc (Suc 0))), Rrule AndR 0)  
  ,(Suc (Suc (Suc (Suc (Suc 0)))), CloseId 0 0)
  ,(Suc (Suc (Suc (Suc 0))), CloseId 1 0) (* 41 *)
  ,(Suc (Suc  0), CloseId 0 0)   
  ,(Suc 0, Cut DIAndCut34Elim2)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc (Suc (Suc (Suc 0))), AxSubst AK DIAndSubst342) (* 46 *)
  ,(Suc (Suc (Suc 0)), Rrule CohideRR 0)
  ,(Suc (Suc (Suc 0)), G) (* 48 *)
  ,(0, Rrule ImplyR 0)
  ,(Suc (Suc (Suc 0)), Lrule AndL 0) (* 50 *)
  ,(Suc (Suc (Suc 0)), CloseId 1 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc 0, CloseId 0 0)
  ,(1, Cut DIAndSG2)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc (Suc (Suc 0)), CloseId 4 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc (Suc (Suc 0)), CloseId 0 0)
  ,(Suc (Suc (Suc 0)), CloseId 0 0)
  ,(1, CloseId 1 0)
  ])
  "

fun proof_take :: "nat \<Rightarrow> ('sf,'sc,'sz) pf \<Rightarrow> ('sf,'sc,'sz) pf"
where "proof_take n (C,D) = (C,List.take n D)"

fun last_step::"('sf,'sc,'sz) pf \<Rightarrow> nat \<Rightarrow> nat * ('sf,'sc,'sz ) step"
where "last_step (C,D) n = List.last (take n D)"

lemma DIAndSound_lemma:"sound (proof_result (proof_take 61 DIAndProof))"
  apply(rule proof_sound)
  unfolding DIAndProof_def DIAndConcl_def  DIAndCutP1_def DIAndSG1_def DIAndCut34Elim1_def  DIAndSubst341_def DIAndCut12Intro_def DIAndSubst12_def
    DIAndCutP12_def DIAndCurry12_def DIAndSubst342_def
    DIAndCut34Elim2_def (* 43*)
    DIAndSG2_def (* 54*)(* slow *)
  apply (auto simp add: prover)
  done
  
    
lemma DIAnd_result_correct:"proof_result (proof_take 61 DIAndProof) = DIAnd"
  unfolding DIAndProof_def DIAndConcl_def Implies_def Or_def 
  proof_result.simps deriv_result.simps start_proof.simps DIAndCutP12_def  DIAndSG1_def DIAndSG2_def DIAndCutP1_def Box_def DIAndCut34Elim1_def DIAndCut12Intro_def DIAndCut34Elim2_def DIAnd_def
  using pne12 pne13 pne14 pne23 pne24 pne34 by (auto)

theorem DIAnd_sound: "sound DIAnd"
  using DIAndSound_lemma DIAnd_result_correct by auto

end
end