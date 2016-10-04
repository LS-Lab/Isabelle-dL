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
where "sound R \<longleftrightarrow> (\<forall>I. is_interp I \<longrightarrow> (\<forall>i. i \<ge> 0 \<longrightarrow> i < length (fst R) \<longrightarrow> seq_sem I (nth (fst R) i) = UNIV) \<longrightarrow> seq_sem I (snd R) = UNIV)"

lemma soundI:"(\<And>I. is_interp I \<Longrightarrow> (\<And>i. i \<ge> 0 \<Longrightarrow> i < length SG \<Longrightarrow> seq_sem I (nth SG i) = UNIV) \<Longrightarrow> seq_sem I G = UNIV) \<Longrightarrow> sound (SG,G)"
  unfolding sound_def by auto

fun start_proof::"('sf,'sc,'sz) sequent \<Rightarrow> ('sf,'sc,'sz) rule"
where "start_proof S = ([S], S)"
  
lemma start_proof_sound:"sound (start_proof S)"
  unfolding sound_def by auto
  
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
  
  lemma axiom_valid:"valid (get_axiom a)"
proof (cases a)
  case AloopIter
  then show ?thesis by (simp add: loop_valid) 
next
  case AI
  then show ?thesis by (simp add: I_valid)
next
  case Atest
  then show ?thesis by (simp add: test_valid)
next
  case Abox
  then show ?thesis by (simp add: box_valid)
next
  case Achoice
  then show ?thesis by (simp add: choice_valid)
next
  case AK
  then show ?thesis by (simp add: K_valid)
next
  case AV
  then show ?thesis by (simp add: V_valid)
next
  case Aassign
  then show ?thesis by (simp add: assign_valid)
next
  case AdConst
  then show ?thesis by (simp add: diff_const_axiom_valid)
next
  case AdPlus
  then show ?thesis by (simp add: diff_plus_axiom_valid)
next
  case AdMult
  then show ?thesis by (simp add: diff_times_axiom_valid)
next
  case ADW
  then show ?thesis by (simp add: DW_valid)
next
  case ADE
  then show ?thesis by (simp add: DE_valid)
next
  case ADC
  then show ?thesis by (simp add: DC_valid)
next
  case ADS
  then show ?thesis by (simp add: DS_valid)
next
  case ADIGeq
  then show ?thesis by (simp add: DIGeq_valid)
next
  case ADIGr
  then show ?thesis by (simp add: DIGr_valid)
next
  case ADG
  then show ?thesis by (simp add: DG_valid)
qed

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

fun close :: "'a list \<Rightarrow> 'a \<Rightarrow>'a list"
where "close L x = filter (\<lambda>y. y \<noteq> x) L"

fun closeI ::"'a list \<Rightarrow> nat \<Rightarrow>'a list"
where "closeI L i = close L (nth L i)"
  
fun Lrule_result :: "lrule \<Rightarrow> nat \<Rightarrow> ('sf, 'sc, 'sz) sequent \<Rightarrow> ('sf, 'sc, 'sz) sequent list"
where "Lrule_result AndL j (A,S) = (case (nth A j) of And p q \<Rightarrow> [(close ([p, q] @ A) (nth A j), S)])"
  | "Lrule_result ImplyL j (A,S) = (case (nth A j) of Not (And (Not q) (Not (Not p))) \<Rightarrow> 
     [(close (q # A) (nth A j), S), (close (p # S) (nth A j), S)])"
  
(* Note: Some of the pattern-matching here is... interesting. The reason for this is that we can only
   match on things in the base grammar, when we would quite like to check things in the derived grammar.
   So all the pattern-matches have the definitions expanded, sometimes in a silly way. *)
fun Rrule_result :: "rrule \<Rightarrow> nat \<Rightarrow> ('sf, 'sc, 'sz) sequent \<Rightarrow> ('sf, 'sc, 'sz) sequent list"
where 
  "Rrule_result ImplyR j (A,S) = (case (nth S j) of Not (And (Not q) (Not (Not p))) \<Rightarrow> [(p # A, q # (closeI S j ))] | _ \<Rightarrow> undefined)"
| "Rrule_result AndR j (A,S) = (case (nth S j) of (And p q) \<Rightarrow> [(A, p # (closeI S j )), (A, q # (closeI S j))])"
| "Rrule_result CohideR j (A,S) = [(A, [nth S 0])]"
| "Rrule_result CohideRR j (A,S) = [([], [nth S 0])]"

fun step_result :: "('sf, 'sc, 'sz) rule \<Rightarrow> (nat * ('sf, 'sc, 'sz) step) \<Rightarrow>  ('sf, 'sc, 'sz) rule"
where
  "step_result (SG,C) (i,Axiom a)   = (closeI SG i, C)"
| "step_result (SG,C) (i,Lrule L j) = (close (append SG (Lrule_result L j (nth SG i))) (nth SG i), C)"
| "step_result (SG,C) (i,Rrule L j) = (append (closeI SG i) (Rrule_result L j (nth SG i)), C)" 
| "step_result (SG,C) (i,Cut \<phi>) = (let (A,S) = nth SG i in ((\<phi> # A, S) # ((A, \<phi> # S) # (closeI SG i)), C))"
| "step_result (SG,C) (i,VSubst \<phi> \<sigma>) = (closeI SG i, C)"
| "step_result (SG,C) (i,CloseId j k) = (closeI SG i, C)"
| "step_result (SG,C) (i,G) = (case nth SG i of (_, (Not (Diamond q (Not p))) # Nil) \<Rightarrow> (([], [p]) # closeI SG i, C))"
| "step_result R (i,S) = R"
  
fun deriv_result :: "('sf, 'sc, 'sz) rule \<Rightarrow> ('sf, 'sc, 'sz) derivation \<Rightarrow> ('sf, 'sc, 'sz) rule"
where 
  "deriv_result R [] = R"
| "deriv_result R (s # ss) = deriv_result (step_result R s) (ss)" 
  
fun proof_result :: "('sf, 'sc, 'sz) pf \<Rightarrow> ('sf, 'sc, 'sz) rule"
where "proof_result (D,S) = deriv_result (start_proof D) S"
  
inductive lrule_ok ::"('sf,'sc,'sz) sequent list \<Rightarrow> ('sf,'sc,'sz) sequent \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> lrule \<Rightarrow> bool"
where
  Lrule_And:"\<And>p q. nth (fst (nth SG i)) j = (p && q) \<Longrightarrow> lrule_ok SG C i j AndL"
| Lrule_Imply:"\<And>p q. nth (fst (nth SG i)) j = (p \<rightarrow> q) \<Longrightarrow> lrule_ok SG C i j AndL"

inductive rrule_ok ::"('sf,'sc,'sz) rule \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rrule \<Rightarrow> bool"
where
  Rrule_And:"\<And>p q. nth (snd (nth SG i)) j = (p && q) \<Longrightarrow> rrule_ok (SG,C) i j AndR"
| Rrule_Imply:"\<And>p q. nth (snd (nth SG i)) j = (p \<rightarrow> q) \<Longrightarrow> rrule_ok (SG,C) i j AndR"
| Rrule_Cohide:"length (snd (nth SG i)) > j  \<Longrightarrow> rrule_ok (SG,C) i j CohideR"
| Rrule_CohideRR:"length (snd (nth SG i)) > j  \<Longrightarrow> rrule_ok (SG,C) i j CohideRR"
  
inductive step_ok  :: "('sf, 'sc, 'sz) rule \<Rightarrow> nat \<Rightarrow> ('sf, 'sc, 'sz) step \<Rightarrow> bool"
where
  Step_Axiom:"(nth SG i) = ([], [get_axiom a]) \<Longrightarrow> step_ok (SG,C) i (Axiom a)"
| Step_Lrule:"lrule_ok SG C i j L \<Longrightarrow> step_ok (SG,C) i (Lrule L j)"
| Step_Rrule:"rrule_ok R i j L \<Longrightarrow> step_ok R i (Rrule L j)"
| Step_Cut:"fsafe \<phi> \<Longrightarrow> i \<in> {0 .. length SG-1} \<Longrightarrow> step_ok (SG,C) i (Cut \<phi>)"
| Step_CloseId:"nth (fst (nth SG i)) j = nth (snd (nth SG i)) k \<Longrightarrow> step_ok (SG,C) i (CloseId j k) "
| Step_G:"\<And>a p. nth SG i = ([], [([[a]]p)]) \<Longrightarrow> step_ok (SG,C) i G"
  
inductive deriv_ok :: "('sf, 'sc, 'sz) rule \<Rightarrow> ('sf, 'sc, 'sz) derivation \<Rightarrow> bool"
where 
  Deriv_Nil:"deriv_ok R Nil"
| Deriv_Cons:"step_ok R i S \<Longrightarrow> i \<ge> 0 \<Longrightarrow> i < length (fst R) \<Longrightarrow> deriv_ok (step_result R (i,S)) SS \<Longrightarrow> deriv_ok R ((i,S) # SS)"
  
inductive proof_ok :: "('sf, 'sc, 'sz) pf \<Rightarrow> bool"
where
  Proof_ok:"deriv_ok (start_proof D) S \<Longrightarrow> proof_ok (D,S)"

lemma nonempty_induct:"\<And>P. (\<And>j. P [] j) \<Longrightarrow> (\<And>x L. P (x # L) 0) \<Longrightarrow> (\<And>x xs j. (P xs j \<Longrightarrow> P (x # xs) (Suc j))) \<Longrightarrow> (\<And>L j. P L j)"
  sorry
  (*by(metis list_nonempty_induct)*) 

lemma close_length:"\<And>L j. length L > 0 \<longrightarrow> i \<ge> 0 \<longrightarrow> i < length L \<longrightarrow> length (close L i) = length L - 1"
  (*subgoal for L
    by(induction rule: nonempty_induct[of "(\<lambda> L j. (length L > 0 \<longrightarrow> j \<ge> 0 \<longrightarrow> j < length L \<longrightarrow> length (close L j) = length L - 1))"], auto)
  done*)
  sorry
  (*using nonempty_induct[of "(\<lambda> L j. (length L > 0 \<longrightarrow> j \<ge> 0 \<longrightarrow> j < length L \<longrightarrow> length (close L i) = length L - 1))"]*)
  (*using nonempty_induct[of "(\<lambda> L j. j = length SG \<longrightarrow> (\<forall>i. (seq_valid (nth SG i) \<longrightarrow> sound (SG,C) \<longrightarrow> i \<ge> 0 \<longrightarrow> i < j \<longrightarrow> sound(close SG i, C))))"]*)

definition sublist::"'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where "sublist A B \<equiv> (\<forall>x. List.member A x \<longrightarrow> List.member B x)"

lemma sublistI:"(\<And>x. List.member A x \<Longrightarrow> List.member B x) \<Longrightarrow> sublist A B"
  unfolding sublist_def by auto
  
lemma sound_weaken_gen:"\<And>A B C. sublist A B \<Longrightarrow> sound (A, C) \<Longrightarrow> sound (B,C)"
  sorry

lemma sound_weaken:"\<And>SG SGS C. sound (SGS, C) \<Longrightarrow> sound (SG # SGS, C)"
  subgoal for SG SGS C
    apply(induction SGS)
    subgoal unfolding sound_def by auto
    subgoal for SG2 SGS
      unfolding sound_def 
      by (metis fst_conv le0 length_Cons not_less_eq nth_Cons_Suc snd_conv)
    done
  done

lemma sound_weaken_app:"\<And>SG SGS C. sound (SG, C) \<Longrightarrow> sound (SG @ SGS, C)"
  sorry

lemma fml_seq_valid:"valid \<phi> \<Longrightarrow> seq_valid ([], [\<phi>])"
  unfolding seq_valid_def valid_def by auto

lemma close_provable_sound:"sound (SG, C) \<Longrightarrow> sound (close SG \<phi>, \<phi>) \<Longrightarrow> sound (close SG \<phi>, C)"
  sorry

lemma closeI_provable_sound:"\<And>i. sound (SG, C) \<Longrightarrow> sound (closeI SG i, (nth SG i)) \<Longrightarrow> sound (closeI SG i, C)"
  sorry

lemma closeI_valid_sound:"\<And>i. sound (SG, C) \<Longrightarrow> seq_valid (nth SG i) \<Longrightarrow> sound (closeI SG i, C)"
  sorry

(*lemma close_nonmember:"(\<not>(List.member B a) \<Longrightarrow> seq_valid (B, [a]) \<Longrightarrow> sound ([(A,SI)], (close (B @ A) a,SI)))"
  sorry*)

lemma close_nonmember:"(\<not>(List.member B a) \<Longrightarrow> seq_valid (B, [a]) \<Longrightarrow> sound ([(close (B @ A) a,SI)], (A,SI)))"
  sorry

lemma mem_sing:"\<And>x. List.member [x] x" sorry
lemma mem_appR:"\<And>A B x. List.member B x \<Longrightarrow> List.member (A @ B) x" sorry
lemma mem_filter:"\<And>A P x. P x \<Longrightarrow> List.member A x \<Longrightarrow> List.member (filter P A) x"
    sorry
lemma close_app_neq:"List.member A x \<Longrightarrow> x \<noteq> a \<Longrightarrow> close (A @ B) a \<noteq> B"
  sorry

lemma fst_neq:"A \<noteq> B \<Longrightarrow> (A,C) \<noteq> (B,D)"
  by auto

lemma lrule_sound: "lrule_ok SG C i j L \<Longrightarrow> i < length SG \<Longrightarrow> sound (SG,C) \<Longrightarrow> sound (close (append SG (Lrule_result L j (nth SG i))) (nth SG i), C)"
proof(induction rule: lrule_ok.induct)
  case (Lrule_And SG i j C p q)
    assume eq:"fst (SG ! i) ! j = (p && q)"
    assume "i < length SG"
    assume sound:"sound (SG, C)"
    obtain AI and SI where SG_dec:"(AI,SI) = (SG ! i)"
      by (metis seq2fml.cases)
    have AIjeq:"AI ! j = (p && q)" using SG_dec eq
      by (metis fst_conv)
    have obvious:"p \<noteq> (Syntax.And p q)" sorry
    have not_mem:" \<not> List.member [p, q] (And p q)" apply (auto simp add: member_rec) sorry
    have true:"sound ([(close ([p, q] @ AI) (p && q),SI)], (AI,SI))"
      apply(rule close_nonmember)
      subgoal by (rule not_mem)
      unfolding seq_valid_def by auto
    have member_singD:"\<And>x P. P x \<Longrightarrow> (\<And>y. List.member [x] y \<Longrightarrow> P y)"
      by (metis member_rec(1) member_rec(2))
    have mems:"\<And>x. List.member [(close ([p, q] @ AI) (p && q),SI)] x \<Longrightarrow> List.member ([y\<leftarrow>SG . y \<noteq> (AI, SI)] @ [y\<leftarrow> [(close ([p, q] @ AI) (p && q), SI)] . y \<noteq> (AI, SI)]) x"
      apply(rule member_singD [of "\<lambda>y. List.member ([y\<leftarrow>SG . y \<noteq> (AI, SI)] @ [y\<leftarrow> [(close ([p, q] @ AI) (p && q), SI)] . y \<noteq> (AI, SI)]) y" "(close ([p, q] @ AI) (p && q),SI)"])
      prefer 2
      subgoal by assumption
      apply(rule mem_appR)
      apply(rule mem_filter)
      defer
      apply(rule mem_sing)
      apply(rule fst_neq)
      apply(rule close_app_neq[of "[p, q]" p "p && q" AI])
      subgoal by(auto simp add: member_rec)
      using obvious by blast  
     have sub:"sublist [(close ([p, q] @ AI) (p && q),SI)] ([y\<leftarrow>SG . y \<noteq> (AI, SI)] @ [y\<leftarrow> [(close (p # q # AI) (p && q), SI)] . y \<noteq> (AI, SI)])"
      apply (rule sublistI)
      using mems by auto
    have cool:"sound ([y\<leftarrow>SG . y \<noteq> (AI, SI)] @ [y\<leftarrow> [(close (p # q # AI) (p && q), SI)] . y \<noteq> (AI, SI)], AI, SI)"
      apply(rule sound_weaken_gen[OF sub] )
      by(rule true)
    have res_sound:"sound ([y\<leftarrow>SG . y \<noteq> (AI,SI)] @ [y\<leftarrow>Lrule_result AndL j (AI,SI) . y \<noteq> (AI,SI)],(AI,SI))"
      apply (simp)
      using cool AIjeq by auto
   show "?case"
    apply(rule close_provable_sound)
    apply(rule sound_weaken_app)
    apply(rule sound)
    using SG_dec apply(auto simp add: eq SG_dec)
    using res_sound SG_dec eq by auto
   
next
  case (Lrule_Imply SG i j C p q)
  then show ?case sorry
qed
  sorry

lemma step_sound:"step_ok R i S \<Longrightarrow> i \<ge> 0 \<Longrightarrow> i < length (fst R) \<Longrightarrow> sound R \<Longrightarrow> sound (step_result R (i,S))"
proof(induction rule: step_ok.induct)
  case (Step_Axiom SG i a C)
    assume is_axiom:"SG ! i = ([], [get_axiom a])"
    assume sound:"sound (SG, C)"
    assume i0:"0 \<le> i"
    assume "i < length (fst (SG, C))"
    then have iL:"i < length (SG)" 
      by auto
    have "seq_valid ([], [get_axiom a])"
      apply(rule fml_seq_valid)
      by(rule axiom_valid)
    then have seq_valid:"seq_valid (SG ! i)"
      using is_axiom by auto
    (*  i0 iL *)
  then show ?case 
    using closeI_valid_sound[OF sound seq_valid] by simp
next
  case (Step_Lrule R i j L)
  then show ?case
    using lrule_sound
    by (metis step_result.simps(2) surj_pair)
    
next
  case (Step_Rrule R i j L)
  then show ?case sorry
next
  case (Step_Cut \<phi> i SG C)
  then show ?case sorry
next
  case (Step_CloseId SG i j k C)
  then show ?case sorry
next
  case (Step_G SG i C a p)
  then show ?case sorry
qed
  
lemma deriv_sound:"deriv_ok R D \<Longrightarrow> sound R \<Longrightarrow> sound (deriv_result R D)"
  apply(induction rule: deriv_ok.induct)
  using step_sound by auto
  
lemma proof_sound:"proof_ok Pf \<Longrightarrow> sound (proof_result Pf)"
  apply(induct rule: proof_ok.induct)
  unfolding proof_result.simps  apply(rule deriv_sound)
  apply assumption
  by(rule start_proof_sound)
  
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

(* TODO: Think this is just the wrong approach *)
(*lemma close_valid_sound':"\<And>SG i. (seq_valid (nth SG i) \<longrightarrow> sound (SG,C) \<longrightarrow> i \<ge> 0 \<longrightarrow> i < length SG \<longrightarrow> sound(closeI SG i, C))"
  subgoal for SG i
    sorry*)
  (*  apply(induction rule: nonempty_induct[of "(\<lambda> SG j. (seq_valid (nth SG j) \<longrightarrow> sound (SG,C) \<longrightarrow> j \<ge> 0 \<longrightarrow> j < length SG \<longrightarrow> sound(close SG j, C)))"])*)
    (*using nonempty_induct[of "(\<lambda> SG j. (seq_valid (nth SG j) \<longrightarrow> sound (SG,C) \<longrightarrow> j \<ge> 0 \<longrightarrow> j < length SG \<longrightarrow> sound(close SG j, C)))"]
    apply(induction rule: nonempty_induct)*)
    (*subgoal for j by (auto simp add: seq_valid_def sound_def)*)
    
    (*subgoal for x L apply (auto simp add: seq_valid_def sound_def) by (simp add: nth_Cons')*)
    
    (*subgoal for x xs j
      apply(simp add: seq_valid_def)
      apply(standard)
      apply(rule impI | rule allI)+
      proof -
        assume IH: "(\<forall>I. is_interp I \<longrightarrow> fml_sem I (seq2fml (xs ! j)) = UNIV) \<longrightarrow> sound (xs, C) \<longrightarrow> j < length xs \<longrightarrow> sound (close xs j, C)"
        assume fact:"\<forall>I. is_interp I \<longrightarrow> fml_sem I (seq2fml (xs ! j)) = UNIV"
        from IH fact have 
          IH2:"sound (xs, C) \<Longrightarrow> j < length xs \<Longrightarrow> sound (close xs j, C)"
          by blast
        
        assume "sound (x # xs, C)"
        assume "j < length xs"          
        have soundXs:"sound (close xs j, C)"
          sorry
        show "sound (x # close xs j, C)"
          by(rule sound_weaken[OF soundXs])
      qed
      done
    done*)
      (*apply(rule soundI)
      subgoal for I
        apply(erule allE[where x=I])+
        unfolding sound_def
        apply(erule allE[where x=I])+
        apply simp
       
        sledgehammer
      apply(rule allI)
      
      (*apply (auto simp add: seq_valid_def sound_def)*)
      using seq_valid_def sound_def close_length nth_Cons'
      sledgehammer
    (*subgoal by (auto simp add: seq_valid_def sound_def)
    subgoal for x by (auto simp add: seq_valid_def sound_def)
    subgoal for x xs apply (auto simp add: seq_valid_def sound_def)
      sledgehammer
    apply(cases "SG")
    subgoal by auto
    subgoal for S SGG
      apply(induction "SGG")
      subgoal apply (auto simp add: seq_valid_def sound_def) 
        done
      subgoal for S2 SGS
        apply (auto simp add: seq_valid_def sound_def)
        using seq_valid_def sound_def 
        
        sledgehammer
        
      done*)
    done
  done*)
        
      

(*lemma close_valid_sound:"\<And>SG i. seq_valid (nth SG i) \<Longrightarrow> sound (SG,C) \<Longrightarrow> i \<ge> 0 \<Longrightarrow> i < length SG \<Longrightarrow> sound(close SG i, C)"
  using close_valid_sound' by blast*)