theory "Proof_Checker" 
imports
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
  "./Ids"
  "./Lib"
  "./Syntax"
  "./Denotational_Semantics"
  "./Axioms"
  "./Differential_Axioms"
  "./Frechet_Correctness"
  "./Static_Semantics"
  "./Coincidence"
  "./Bound_Effect"
  "./Uniform_Renaming"
  "./USubst_Lemma"
  "./Pretty_Printer"
  
begin context ids begin

type_synonym ('a,'b,'c) sequent = "('a,'b,'c) formula list * ('a,'b,'c) formula list"

fun seq2fml :: "('a,'b,'c) sequent \<Rightarrow> ('a,'b,'c) formula"
where
  "seq2fml (ante,succ) = Implies (fold And ante TT) (fold Or succ FF)"
  
fun seq_sem ::"('sf, 'sc, 'sz) interp \<Rightarrow> ('sf, 'sc, 'sz) sequent \<Rightarrow> 'sz state set"
where "seq_sem I S = fml_sem I (seq2fml S)"
 
definition seq_valid
where "seq_valid S \<equiv> \<forall>I. is_interp I \<longrightarrow> seq_sem I S = UNIV"  

(* Rule: assumptions, then conclusion *)
type_synonym ('a,'b,'c) rule = "('a,'b,'c) sequent list * ('a,'b,'c) sequent"
  
definition sound :: "('sf, 'sc, 'sz) rule \<Rightarrow> bool"
where "sound R \<longleftrightarrow> (\<forall>I. is_interp I \<longrightarrow> (\<forall>i. i \<in> {0..(length (fst R)-1)} \<longrightarrow> seq_sem I (nth (fst R) i) = UNIV) \<longrightarrow> seq_sem I (snd R) = UNIV)"

lemma soundI:"(\<And>I. is_interp I \<Longrightarrow> (\<And>i. i \<in> {0..(length SG-1)} \<Longrightarrow> seq_sem I (nth SG i) = UNIV) \<Longrightarrow> seq_sem I G = UNIV) \<Longrightarrow> sound (SG,G)"
  unfolding sound_def by auto

fun start_proof::"('sf,'sc,'sz) sequent \<Rightarrow> ('sf,'sc,'sz) rule"
where "start_proof S = ([S], S)"
  
lemma start_proof_sound:"seq_valid S \<Longrightarrow> sound (start_proof S)"
  unfolding sound_def seq_valid_def by auto
  
datatype axiom =
    AloopIter | AI | Atest | Abox | Achoice | AK | AV | Aassign
  | AdConst | AdPlus | AdMult
  | ADW | ADE | ADC | ADS | ADIGeq | ADIGr | ADG
  
fun get_axiom:: "axiom \<Rightarrow> ('sf,'sc,'sz) formula"
where 
  "get_axiom AloopIter = loop_iterate_axiom"
| "get_axiom AI = Iaxiom"
| "get_axiom Atest = test_axiom"
| "get_axiom Abox = box_axiom"
| "get_axiom Achoice = choice_axiom"
| "get_axiom AK = Kaxiom"
| "get_axiom AV = Vaxiom"
| "get_axiom Aassign = assign_axiom"
| "get_axiom AdConst = diff_const_axiom"
| "get_axiom AdPlus = diff_plus_axiom"
| "get_axiom AdMult = diff_times_axiom"
| "get_axiom ADW = DWaxiom"
| "get_axiom ADE = DEaxiom"
| "get_axiom ADC = DCaxiom"
| "get_axiom ADS = DSaxiom"
| "get_axiom ADIGeq = DIGeqaxiom"
| "get_axiom ADIGr = DIGraxiom"
| "get_axiom ADG = DGaxiom"
  
datatype rrule = ImplyR | AndR | CohideR | CohideRR
datatype lrule = ImplyL | AndL
  
datatype ('a, 'b, 'c) step =
  Axiom axiom
| MP
| G
| CT
| CQ
| CE
| Skolem
(* Apply Usubst to some other (valid) formula *)
(* TODO: I don't think I want this, might be easier to do an axiom instantiation rule *)
| VSubst "('a, 'b, 'c) formula" "('a, 'b, 'c) subst"
| URename
| BRename
| Rrule rrule nat
| Lrule lrule nat
| CloseId nat nat
| Cut "('a, 'b, 'c) formula"
  
type_synonym ('a, 'b, 'c) derivation = "(nat * ('a, 'b, 'c) step) list"
type_synonym ('a, 'b, 'c) pf = "('a,'b,'c) sequent * ('a, 'b, 'c) derivation"
fun seq_to_string :: "('sf, 'sc, 'sz) sequent \<Rightarrow> char list"
where "seq_to_string (A,S) = join '', '' (map fml_to_string A) @ '' |- '' @ join '', '' (map fml_to_string S)"
  
fun rule_to_string :: "('sf, 'sc, 'sz) rule \<Rightarrow> char list"
where "rule_to_string (SG, C) = (join '';;   '' (map seq_to_string SG)) @ ''            '' @  (*[char_of_nat 10] @ *)seq_to_string C"

fun close :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
where 
  "close (SG # SGs) 0 m = SGs"
| "close (SG # SGs) (Suc n) m = SG # (close SGs n m)"
| "close _ _ _ = undefined"

fun Lrule_result :: "lrule \<Rightarrow> nat \<Rightarrow> ('sf, 'sc, 'sz) sequent \<Rightarrow> ('sf, 'sc, 'sz) sequent list"
where "Lrule_result AndL j (A,S) = (case (nth A j) of And p q \<Rightarrow> [(p # q # (close A j (length A)), S)])"
  | "Lrule_result ImplyL j (A,S) = (case (nth A j) of Not (And (Not q) (Not (Not p))) \<Rightarrow> 
     [(q # (close A j (length A)), S), (close A j (length A), p # S)])"
  
(* Note: Some of the pattern-matching here is... interesting. The reason for this is that we can only
   match on things in the base grammar, when we would quite like to check things in the derived grammar.
   So all the pattern-matches have the definitions expanded, sometimes in a silly way. *)
fun Rrule_result :: "rrule \<Rightarrow> nat \<Rightarrow> ('sf, 'sc, 'sz) sequent \<Rightarrow> ('sf, 'sc, 'sz) sequent list"
where 
  "Rrule_result ImplyR j (A,S) = (case (nth S j) of Not (And (Not q) (Not (Not p))) \<Rightarrow> [(p # A, q # (close S j (length A)))] | _ \<Rightarrow> undefined)"
| "Rrule_result AndR j (A,S) = (case (nth S j) of (And p q) \<Rightarrow> [(A, p # (close S j (length A))), (A, q # (close S j (length A)))])"
| "Rrule_result CohideR j (A,S) = [(A, [nth S 0])]"
| "Rrule_result CohideRR j (A,S) = [([], [nth S 0])]"

fun step_result :: "('sf, 'sc, 'sz) rule \<Rightarrow> (nat * ('sf, 'sc, 'sz) step) \<Rightarrow>  ('sf, 'sc, 'sz) rule"
where
  "step_result (SG,C) (i,Axiom a)   = (close SG i (length SG), C)"
| "step_result (SG,C) (i,Lrule L j) = (append (close SG i (length SG)) (Lrule_result L j (nth SG i)), C)"
| "step_result (SG,C) (i,Rrule L j) = (append (close SG i (length SG)) (Rrule_result L j (nth SG i)), C)" 
| "step_result (SG,C) (i,Cut \<phi>) = (let (A,S) = nth SG i in ((\<phi> # A, S) # ((A, \<phi> # S) # (close SG i (length SG))), C))"
| "step_result (SG,C) (i,VSubst \<phi> \<sigma>) = (close SG i (length SG), C)"
| "step_result (SG,C) (i,CloseId j k) = (close SG i (length SG), C)"
| "step_result (SG,C) (i,G) = (case nth SG i of (_, (Not (Diamond q (Not p))) # Nil) \<Rightarrow> (([], [p]) # close SG i (length SG), C))"
| "step_result R (i,S) = R"
  
fun deriv_result :: "('sf, 'sc, 'sz) rule \<Rightarrow> ('sf, 'sc, 'sz) derivation \<Rightarrow> ('sf, 'sc, 'sz) rule"
where 
  "deriv_result R [] = R"
| "deriv_result R (s # ss) = deriv_result (step_result R s) (ss)" 
  
fun proof_result :: "('sf, 'sc, 'sz) pf \<Rightarrow> ('sf, 'sc, 'sz) rule"
where "proof_result (D,S) = deriv_result (start_proof D) S"
  
inductive lrule_ok ::"('sf,'sc,'sz) rule \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> lrule \<Rightarrow> bool"
where
  Lrule_And:"\<And>p q. nth (fst (nth SG i)) j = (p && q) \<Longrightarrow> lrule_ok (SG,C) i j AndL"
| Lrule_Imply:"\<And>p q. nth (fst (nth SG i)) j = (p \<rightarrow> q) \<Longrightarrow> lrule_ok (SG,C) i j AndL"

inductive rrule_ok ::"('sf,'sc,'sz) rule \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rrule \<Rightarrow> bool"
where
  Rrule_And:"\<And>p q. nth (snd (nth SG i)) j = (p && q) \<Longrightarrow> rrule_ok (SG,C) i j AndR"
| Rrule_Imply:"\<And>p q. nth (snd (nth SG i)) j = (p \<rightarrow> q) \<Longrightarrow> rrule_ok (SG,C) i j AndR"
| Rrule_Cohide:"length (snd (nth SG i)) > j  \<Longrightarrow> rrule_ok (SG,C) i j CohideR"
| Rrule_CohideRR:"length (snd (nth SG i)) > j  \<Longrightarrow> rrule_ok (SG,C) i j CohideRR"
  
inductive step_ok  :: "('sf, 'sc, 'sz) rule \<Rightarrow> nat \<Rightarrow> ('sf, 'sc, 'sz) step \<Rightarrow> bool"
where
  Step_Axiom:"(nth SG i) = ([], [get_axiom a]) \<Longrightarrow> step_ok (SG,C) i (Axiom a)"
| Step_Lrule:"lrule_ok R i j L \<Longrightarrow> step_ok R i (Lrule L j)"
| Step_Rrule:"rrule_ok R i j L \<Longrightarrow> step_ok R i (Rrule L j)"
| Step_Cut:"fsafe \<phi> \<Longrightarrow> i \<in> {0 .. length SG-1} \<Longrightarrow> step_ok (SG,C) i (Cut \<phi>)"
| Step_CloseId:"nth (fst (nth SG i)) j = nth (snd (nth SG i)) k \<Longrightarrow> step_ok (SG,C) i (CloseId j k) "
| Step_G:"\<And>a p. nth SG i = ([], [([[a]]p)]) \<Longrightarrow> step_ok (SG,C) i G"
  
inductive deriv_ok :: "('sf, 'sc, 'sz) rule \<Rightarrow> ('sf, 'sc, 'sz) derivation \<Rightarrow> bool"
where 
  Deriv_Nil:"deriv_ok R Nil"
| Deriv_Cons:"step_ok R i S \<Longrightarrow> deriv_ok (step_result R (i,S)) SS \<Longrightarrow> deriv_ok R ((i,S) # SS)"
  
inductive proof_ok :: "('sf, 'sc, 'sz) pf \<Rightarrow> bool"
where
  Proof_ok:"deriv_ok (start_proof D) S \<Longrightarrow> proof_ok (D,S)"

(* DI Example *)  
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
  
definition DIAnd :: "('sf,'sc,'sz) rule" 
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

(*definition DIAndCut12Intro :: "('sf,'sc,'sz) formula"
where "DIAndCut12Intro = (([[Pvar vid1]](Pc pid2  \<rightarrow> (Pc pid1 && Pc pid2)))
  \<rightarrow> (([[Pvar vid1]](Pc pid2)) \<rightarrow> ([[Pvar vid1]](Pc pid1 && Pc pid2))))" 
*)
definition DIAndProof :: "('sf, 'sc, 'sz) pf"
where "DIAndProof =
  (DIAndConcl, [
   (0, Rrule ImplyR 0)
  ,(0, Lrule AndL 0)
  ,(0, Rrule ImplyR 0)
  ,(0, Cut DIAndCutP1)
  ,(1, Cut DIAndSG1)
  ,(0, Rrule CohideR 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc (Suc (Suc 0)), CloseId 1 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc (Suc 0), Cut DIAndCut34Elim1)
  ,(0, Lrule ImplyL 0)
  ,(Suc (Suc (Suc 0)), Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc 0, Rrule CohideRR 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), G)  
  ,(0, Rrule ImplyR 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), Lrule AndL 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), CloseId 0 0)
  ,(Suc (Suc (Suc 0)), VSubst Kaxiom DIAndSubst341)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc 0, CloseId 0 0)
  ,(0, Cut DIAndCut12Intro)
  ,(Suc 0, VSubst Kaxiom DIAndSubst12)
  ,(0, Lrule ImplyL 0)
  ,(1, Lrule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc 0, Cut DIAndCutP12)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc (Suc (Suc (Suc 0))), VSubst Kaxiom DIAndCurry12)
  ,(Suc (Suc (Suc 0)), Rrule CohideRR 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc (Suc 0), G)  
  ,(0, Rrule ImplyR 0)  
  ,(Suc (Suc (Suc (Suc 0))), Rrule ImplyR 0)  
  ,(Suc (Suc (Suc (Suc 0))), Rrule AndR 0)  
  ,(Suc (Suc (Suc (Suc 0))), CloseId 1 0)  
  ,(Suc (Suc (Suc (Suc 0))), CloseId 0 0)  
  ,(Suc (Suc (Suc 0)), CloseId 1 0)  
  ,(Suc (Suc 0), CloseId 1 0)  
  ,(Suc 0, Cut DIAndCut34Elim2)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc (Suc (Suc 0)), VSubst Kaxiom DIAndSubst342)
  ,(Suc (Suc 0), Rrule CohideRR 0)
  ,(Suc (Suc 0), G)
  ,(0, Rrule ImplyR 0)
  ,(Suc (Suc 0), Lrule AndL 0)
  ,(Suc (Suc 0), CloseId 1 0)
  ,(Suc 0, Lrule ImplyL 0)
  ,(Suc (Suc 0), CloseId 1 0)
  ,(1, Cut DIAndSG2)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc (Suc 0), CloseId 4 0)
  ,(1, Lrule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ])
  "

lemma print_example_result:"rule_to_string(proof_result (DIAndProof)) = undefined"
  unfolding DIAndProof_def DIAndConcl_def Implies_def Or_def 
  proof_result.simps deriv_result.simps start_proof.simps DIAndCutP12_def  DIAndSG1_def DIAndSG2_def DIAndCutP1_def Box_def DIAndCut34Elim1_def DIAndCut12Intro_def DIAndCut34Elim2_def DIAnd_def
  using pne12 pne13 pne14 pne23 pne24 pne34 apply (auto)
  sorry
  
lemma example_result_correct:"proof_result DIAndProof = DIAnd"
  unfolding DIAndProof_def DIAndConcl_def Implies_def Or_def 
   DIAndCutP12_def  DIAndSG1_def DIAndSG2_def DIAndCutP1_def Box_def DIAndCut34Elim1_def DIAndCut12Intro_def DIAndCut34Elim2_def DIAnd_def
  by (auto)

end end