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
  "seq2fml (ante,succ) = Implies (foldr And ante TT) (foldr Or succ FF)"
  
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

lemma soundI':"(\<And>I \<nu>. is_interp I \<Longrightarrow> (\<And>i . i \<ge> 0 \<Longrightarrow> i < length SG \<Longrightarrow> \<nu> \<in> seq_sem I (nth SG i)) \<Longrightarrow> \<nu> \<in> seq_sem I G) \<Longrightarrow> sound (SG,G)"
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
     [(close (q # A) (nth A j), S), (close A (nth A j), p # S)])"
  
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
| Lrule_Imply:"\<And>p q. nth (fst (nth SG i)) j = (p \<rightarrow> q) \<Longrightarrow> lrule_ok SG C i j ImplyL"

inductive rrule_ok ::"('sf,'sc,'sz) rule \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rrule \<Rightarrow> bool"
where
  Rrule_And:"\<And>p q. nth (snd (nth SG i)) j = (p && q) \<Longrightarrow> rrule_ok (SG,C) i j AndR"
| Rrule_Imply:"\<And>p q. nth (snd (nth SG i)) j = (p \<rightarrow> q) \<Longrightarrow> rrule_ok (SG,C) i j AndR"
| Rrule_Cohide:"length (snd (nth SG i)) > j  \<Longrightarrow> rrule_ok (SG,C) i j CohideR"
| Rrule_CohideRR:"length (snd (nth SG i)) > j  \<Longrightarrow> rrule_ok (SG,C) i j CohideRR"
  
inductive step_ok  :: "('sf, 'sc, 'sz) rule \<Rightarrow> nat \<Rightarrow> ('sf, 'sc, 'sz) step \<Rightarrow> bool"
where
  Step_Axiom:"(nth SG i) = ([], [get_axiom a]) \<Longrightarrow> step_ok (SG,C) i (Axiom a)"
| Step_Lrule:"lrule_ok SG C i j L \<Longrightarrow> j < length (fst (nth SG i)) \<Longrightarrow>  step_ok (SG,C) i (Lrule L j)"
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

definition sublist::"'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where "sublist A B \<equiv> (\<forall>x. List.member A x \<longrightarrow> List.member B x)"

lemma sublistI:"(\<And>x. List.member A x \<Longrightarrow> List.member B x) \<Longrightarrow> sublist A B"
  unfolding sublist_def by auto

lemma soundI_mem:"(\<And>I. is_interp I \<Longrightarrow> (\<And>\<phi>. List.member SG \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV) \<Longrightarrow> seq_sem I C = UNIV) \<Longrightarrow> sound (SG,C)"
  apply (auto simp add: sound_def)
  by (metis in_set_conv_nth in_set_member iso_tuple_UNIV_I seq2fml.simps)

lemma soundD_mem:"sound (SG,C) \<Longrightarrow> (\<And>I. is_interp I \<Longrightarrow> (\<And>\<phi>. List.member SG \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV) \<Longrightarrow> seq_sem I C = UNIV)"
  apply (auto simp add: sound_def)
  using in_set_conv_nth in_set_member iso_tuple_UNIV_I seq2fml.simps
  by (metis seq2fml.elims)

lemma close_provable_sound:"sound (SG, C) \<Longrightarrow> sound (close SG \<phi>, \<phi>) \<Longrightarrow> sound (close SG \<phi>, C)"
  proof (rule soundI_mem)
    fix I::"('sf,'sc,'sz) interp"
    assume S1:"sound (SG, C)"
    assume S2:"sound (close SG \<phi>, \<phi>)"
    assume good:"is_interp I"
    assume SGCs:"(\<And>\<phi>'. List.member (close SG \<phi>) \<phi>' \<Longrightarrow> seq_sem I \<phi>' = UNIV)"
    have S\<phi>:"seq_sem I \<phi> = UNIV"
      using S2 apply simp
      apply(drule soundD_mem)
      using good apply auto
      using SGCs UNIV_I by fastforce
    have mem_close:"\<And>P. List.member SG P \<Longrightarrow> P \<noteq> \<phi> \<Longrightarrow> List.member (close SG \<phi>) P"
      by(induction SG, auto simp add: member_rec)
    have SGs:"\<And>P. List.member SG P \<Longrightarrow> seq_sem I P = UNIV"
      subgoal for P
        apply(cases "P = \<phi>")
        subgoal using S\<phi> by auto
        subgoal using mem_close[of P] SGCs by auto
        done
      done
    show "seq_sem I C = UNIV"
      using S1 apply simp
      apply(drule soundD_mem)
      using good apply auto
      using SGs apply auto
      using impl_sem by blast
    qed
    
lemma sound_weaken_gen:"\<And>A B C. sublist A B \<Longrightarrow> sound (A, C) \<Longrightarrow> sound (B,C)"
  proof (rule soundI_mem)
    fix A B::"('sf,'sc,'sz) sequent list" 
      and C::"('sf,'sc,'sz) sequent" 
      and I::"('sf,'sc,'sz) interp"
    assume sub:"sublist A B"
    assume good:"is_interp I"
    assume "sound (A, C)"
    then have soundC:"(\<And>\<phi>. List.member A \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV) \<Longrightarrow> seq_sem I C = UNIV"
      apply simp
      apply(drule soundD_mem)
      by (auto simp add: good)
    assume SG:"(\<And>\<phi>. List.member B \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)"
    show "seq_sem I C = UNIV"
      using soundC SG sub unfolding sublist_def by auto
  qed
  
lemma sound_weaken:"\<And>SG SGS C. sound (SGS, C) \<Longrightarrow> sound (SG # SGS, C)"
  subgoal for SG SGS C
    apply(induction SGS)
    subgoal unfolding sound_def by auto
    subgoal for SG2 SGS
      unfolding sound_def 
      by (metis fst_conv le0 length_Cons not_less_eq nth_Cons_Suc snd_conv)
    done
  done

lemma member_filter:"\<And>P. List.member (filter P L) x \<Longrightarrow> List.member L x"
  apply(induction L, auto)
  by(metis (full_types) member_rec(1))

lemma close_sub:"sublist (close \<Gamma> \<phi>) \<Gamma>"
  apply (auto simp add: sublist_def)
  using member_filter by fastforce

lemma close_app_comm:"close (A @ B) x  = close A x @ close B x"
  by auto

lemma nth_member:"n < List.length L \<Longrightarrow> List.member L (List.nth L n)"
  apply(induction L, auto simp add: member_rec)
  by (metis in_set_member length_Cons nth_mem set_ConsD)

lemma seq_semI':"(\<nu> \<in> fml_sem I (foldr And \<Gamma> TT) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr Or \<Delta> FF)) \<Longrightarrow> \<nu> \<in> seq_sem I (\<Gamma>,\<Delta>)"
  by auto 

lemma mem_appL:"List.member A x \<Longrightarrow> List.member (A @ B) x"
  by(induction A, auto simp add: member_rec)

lemma sound_weaken_appR:"\<And>SG SGS C. sound (SG, C) \<Longrightarrow> sound (SG @ SGS, C)"
  subgoal for SG SGS C
    apply(rule sound_weaken_gen)
    apply(auto)
    unfolding sublist_def apply(rule allI)
    subgoal for x
      using mem_appL[of SG x SGS] by auto 
    done
  done

named_theorems member_intros "Prove that stuff is in lists"

lemma mem_sing[member_intros]:"\<And>x. List.member [x] x"
  by(auto simp add: member_rec)
lemma mem_appR[member_intros]:"\<And>A B x. List.member B x \<Longrightarrow> List.member (A @ B) x"
  subgoal for A by(induction A, auto simp add: member_rec) done
lemma mem_filter[member_intros]:"\<And>A P x. P x \<Longrightarrow> List.member A x \<Longrightarrow> List.member (filter P A) x"
  subgoal for A
    by(induction A, auto simp add: member_rec)
  done

lemma sound_weaken_appL:"\<And>SG SGS C. sound (SGS, C) \<Longrightarrow> sound (SG @ SGS, C)"
  subgoal for SG SGS C
    apply(rule sound_weaken_gen)
    apply(auto)
    unfolding sublist_def apply(rule allI)
    subgoal for x
      using mem_appR[of SGS x SG] by auto
    done
  done

lemma fml_seq_valid:"valid \<phi> \<Longrightarrow> seq_valid ([], [\<phi>])"
  unfolding seq_valid_def valid_def by auto

lemma closeI_provable_sound:"\<And>i. sound (SG, C) \<Longrightarrow> sound (closeI SG i, (nth SG i)) \<Longrightarrow> sound (closeI SG i, C)"
  using close_provable_sound by auto

lemma valid_to_sound:"seq_valid A \<Longrightarrow> sound (B, A)"
  unfolding seq_valid_def sound_def by auto

lemma closeI_valid_sound:"\<And>i. sound (SG, C) \<Longrightarrow> seq_valid (nth SG i) \<Longrightarrow> sound (closeI SG i, C)"
  using valid_to_sound closeI_provable_sound by auto
  
lemma close_nonmember_eq:"\<not>(List.member A a) \<Longrightarrow> close A a = A"
  by (induction A, auto simp add: member_rec)

lemma close_noneq_nonempty:"List.member A x \<Longrightarrow> x \<noteq> a \<Longrightarrow> close A a \<noteq> []"
  by(induction A, auto simp add: member_rec)

lemma close_app_neq:"List.member A x \<Longrightarrow> x \<noteq> a \<Longrightarrow> close (A @ B) a \<noteq> B" 
  using append_self_conv2[of "close A a" "close B a"] append_self_conv2[of "close A a" "B"] close_app_comm[of A B a] close_noneq_nonempty[of A x a]
  apply(cases "close B a = B")
  apply (auto)
  by (metis (no_types, lifting) filter_True filter_append mem_Collect_eq set_filter)
  
lemma member_singD:"\<And>x P. P x \<Longrightarrow> (\<And>y. List.member [x] y \<Longrightarrow> P y)"
  by (metis member_rec(1) member_rec(2))

lemma fst_neq:"A \<noteq> B \<Longrightarrow> (A,C) \<noteq> (B,D)"
  by auto

lemma and_foldl_sem:"\<nu> \<in> fml_sem I (foldr And \<Gamma> TT) \<Longrightarrow> (\<And>\<phi>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>)"
  by(induction \<Gamma>, auto simp add: member_rec)

lemma and_foldl_sem_conv:"(\<And>\<phi>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma> TT)"
  by(induction \<Gamma>, auto simp add: member_rec)

lemma or_foldl_sem:"List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I (foldr Or \<Gamma> FF)"
  by(induction \<Gamma>, auto simp add: member_rec)

lemma \<Gamma>_sub_sem:"sublist \<Gamma>1 \<Gamma>2 \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma>2 TT) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma>1 TT)"
  unfolding sublist_def 
  by (smt and_foldl_sem and_foldl_sem_conv)

lemma seq_semI:"List.member \<Delta> \<psi> \<Longrightarrow>((\<And>\<phi>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>) \<Longrightarrow> \<nu> \<in> fml_sem I \<psi>) \<Longrightarrow> \<nu> \<in> seq_sem I (\<Gamma>,\<Delta>)"
  apply(rule seq_semI')
  using and_foldl_sem[of \<nu> I \<Gamma>] or_foldl_sem by blast
  
lemma seq_MP:"\<nu> \<in> seq_sem I (\<Gamma>,\<Delta>) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma> TT) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr Or \<Delta> FF)"
  by(induction \<Delta>, auto)
  
lemma lrule_sound: "lrule_ok SG C i j L \<Longrightarrow> i < length SG \<Longrightarrow> j < length (fst (SG ! i)) \<Longrightarrow> sound (SG,C) \<Longrightarrow> sound (close (append SG (Lrule_result L j (nth SG i))) (nth SG i), C)"
proof(induction rule: lrule_ok.induct)
  case (Lrule_And SG i j C p q)
    assume eq:"fst (SG ! i) ! j = (p && q)"
    assume sound:"sound (SG, C)"
    obtain AI and SI where SG_dec:"(AI,SI) = (SG ! i)"
      by (metis seq2fml.cases)
    have AIjeq:"AI ! j = (p && q)" using SG_dec eq
      by (metis fst_conv)
    have sub:"sublist [(close ([p, q] @ AI) (p && q),SI)] ([y\<leftarrow>SG . y \<noteq> (AI, SI)] @ [y\<leftarrow> [(close (p # q # AI) (p && q), SI)] . y \<noteq> (AI, SI)])"
      apply (rule sublistI)
      using member_singD [of "\<lambda>y. List.member ([y\<leftarrow>SG . y \<noteq> (AI, SI)] @ [y\<leftarrow> [(close ([p, q] @ AI) (p && q), SI)] . y \<noteq> (AI, SI)]) y" "(close ([p, q] @ AI) (p && q),SI)"]
      using close_app_neq[of "[p, q]" p "p && q" AI] 
      by(auto intro: member_intros fst_neq simp add: member_rec expr_diseq)
    have cool:"sound ([y\<leftarrow>SG . y \<noteq> (AI, SI)] @ [y\<leftarrow> [(close (p # q # AI) (p && q), SI)] . y \<noteq> (AI, SI)], AI, SI)"
      apply(rule sound_weaken_gen[OF sub] )
      apply(auto simp add: member_rec expr_diseq)
      unfolding seq_valid_def
      proof (rule soundI_mem)
        fix I::"('sf,'sc,'sz) interp"
        assume good:"is_interp I"
        assume sgs:"(\<And>\<phi>. List.member [(p # q # [y\<leftarrow>AI . y \<noteq> (p && q)], SI)] \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)"
        have theSg:"seq_sem I (p # q # [y\<leftarrow>AI . y \<noteq> (p && q)], SI) = UNIV"
          apply(rule sgs)
          by(auto intro: member_intros)
        then have sgIn:"\<And>\<nu>. \<nu> \<in> seq_sem I ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)], SI)"
          by auto
        { fix \<nu>
          assume sem:"\<nu> \<in> seq_sem I ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)], SI)"
          have mem_eq:"\<And>x. List.member ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)]) x = List.member AI x"
            by (metis (mono_tags, lifting) Lrule_And.prems(2) SG_dec eq fst_conv local.member_filter mem_filter member_rec(1) nth_member)
          have myeq:"\<nu> \<in> seq_sem I ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)], SI) \<Longrightarrow>  \<nu> \<in> seq_sem I (AI, SI)"
            using and_foldl_sem and_foldl_sem_conv seq_semI Lrule_And.prems(2) SG_dec eq  seq_MP seq_semI' mem_eq
            by (metis (no_types, lifting))
          
          have "\<nu> \<in> seq_sem I ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)], SI)"
            using sem by auto
          then have "\<nu> \<in> seq_sem I ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)], SI)"
            by blast
          then have "\<nu> \<in> seq_sem I (AI, SI)"
            using myeq by auto}
          then show "seq_sem I (AI, SI) = UNIV"
            using sgIn by blast
          qed
    have res_sound:"sound ([y\<leftarrow>SG . y \<noteq> (AI,SI)] @ [y\<leftarrow>Lrule_result AndL j (AI,SI) . y \<noteq> (AI,SI)],(AI,SI))"
      apply (simp)
      using cool AIjeq by auto
   show "?case"
    apply(rule close_provable_sound)
    apply(rule sound_weaken_appR)
    apply(rule sound)
    using res_sound SG_dec by auto
next
  case (Lrule_Imply SG i j C p q)
    have implyL_simp:"\<And>AI SI SS p q. 
      (nth AI  j) = (Not (And (Not q) (Not (Not p)))) \<Longrightarrow> 
      (AI,SI) = SS \<Longrightarrow> 
      Lrule_result ImplyL j SS = [(close (q # AI) (nth AI j), SI), (close AI (nth AI j), p # SI)]"
      subgoal for AI SI SS p q apply(cases SS) by auto done
    assume eq:"fst (SG ! i) ! j = (p \<rightarrow> q)"
    assume iL:"i < length SG"
    assume jL:"j < length (fst (SG ! i))"
    assume sound:"sound (SG, C)"
    obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
      by (metis seq2fml.cases)
    have res_eq:"Lrule_result ImplyL j (SG ! i) = 
      [(close (q # \<Gamma>) (nth \<Gamma> j), \<Delta>), 
       (close \<Gamma> (nth \<Gamma> j), p # \<Delta>)]"
      apply(rule implyL_simp)
      using SG_dec eq Implies_def Or_def 
      by (metis fstI)+
    have AIjeq:"\<Gamma> ! j = (p \<rightarrow> q)" 
      using SG_dec eq unfolding Implies_def Or_def
      by (metis fst_conv)
    have big_sound:"sound ([(close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>), (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)], (\<Gamma>,\<Delta>))"
      apply(rule soundI')
      apply(rule seq_semI')
      proof -
        fix I::"('sf,'sc,'sz) interp" and \<nu>::"'sz state"
        assume good:"is_interp I"
        assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow>
                 i < length [(close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>), (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)] \<Longrightarrow>
                 \<nu> \<in> seq_sem I ([(close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>), (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)] ! i))"
        have sg1:"\<nu> \<in> seq_sem I (close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>)" using sgs[of 0] by auto
        have sg2:"\<nu> \<in> seq_sem I (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)" using sgs[of "Suc 0"] by auto
        assume \<Gamma>:"\<nu> \<in> fml_sem I (foldr And \<Gamma> TT)"
        have \<Gamma>_proj:"\<And>\<phi> \<Gamma>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma> TT) \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>"
          apply(induction \<Gamma>, auto simp add: member_rec)
          using and_foldl_sem by blast
        have imp:"\<nu> \<in> fml_sem I (p \<rightarrow> q)" 
          apply(rule \<Gamma>_proj[of \<Gamma>])
          using AIjeq  jL SG_dec nth_member
          apply (metis fst_conv)
          by (rule \<Gamma>)
        have sub:"sublist (close \<Gamma> (p \<rightarrow> q)) \<Gamma>"
          by (rule close_sub)
        have \<Gamma>C:"\<nu> \<in> fml_sem I (foldr And (close \<Gamma> (p \<rightarrow> q)) TT)"
          by (rule \<Gamma>_sub_sem[OF sub \<Gamma>])
        have "\<nu> \<in> fml_sem I (foldr op || (p # \<Delta>) FF)"
          by(rule seq_MP[OF sg2 \<Gamma>C])
        then have disj:"\<nu> \<in> fml_sem I p \<or> \<nu> \<in> fml_sem I (foldr op || \<Delta> FF)"
          by auto 
        { assume p:"\<nu> \<in> fml_sem I p"
          have q:"\<nu> \<in> fml_sem I q" using p imp by simp
          have res: "\<nu> \<in> fml_sem I (foldr op || \<Delta> FF)" 
            using disj \<Gamma> seq_semI
            proof -
              have "\<nu> \<in> fml_sem I (foldr op && (q # \<Gamma>) TT)"
                using \<Gamma> q by auto
              then show ?thesis
                by (meson \<Gamma>_sub_sem close_sub seq_MP sg1)
            qed
          have conj:"\<nu> \<in> fml_sem I (foldr op && (q # \<Gamma>) TT)"
            using q \<Gamma> by auto
          have conj:"\<nu> \<in> fml_sem I (foldr op && (close (q # \<Gamma>) (p \<rightarrow> q)) TT)"
            apply(rule \<Gamma>_sub_sem)
            defer
            apply(rule conj)
            by(rule close_sub)
          have \<Delta>1:"\<nu> \<in> fml_sem I (foldr op || \<Delta> FF)"
            by(rule seq_MP[OF sg1 conj])
          }
        then show "\<nu> \<in> fml_sem I (foldr op || \<Delta> FF)"
          using disj by auto
      qed
      have neq1:"close ([q] @ \<Gamma>) (p \<rightarrow> q) \<noteq> \<Gamma>"
        apply(rule close_app_neq)
        apply(rule mem_sing)
        by (auto simp add: expr_diseq)
      have neq2:"p # \<Delta> \<noteq> \<Delta>"
        by(induction p, auto)
      have close_eq:"close [(close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>), (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)] (\<Gamma>,\<Delta>) = [(close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>), (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)]"
        apply(rule close_nonmember_eq)
        apply auto
        using neq1 neq2  
        apply (simp add: member_rec)
      proof -
        assume a1: "q = (p \<rightarrow> q)"
        assume "List.member [([y\<leftarrow>\<Gamma> . y \<noteq> q], \<Delta>), ([y\<leftarrow>\<Gamma> . y \<noteq> q], p # \<Delta>)] (\<Gamma>, \<Delta>)"
          then have "[f\<leftarrow>\<Gamma> . f \<noteq> q] = \<Gamma>"
        by (simp add: member_rec)
        then show False
          using a1 neq1 by fastforce
      qed       
  show ?case 
    apply(rule close_provable_sound)
    apply(rule sound_weaken_appR)
    apply(rule sound)
    apply(unfold res_eq)
    apply(unfold AIjeq)
    unfolding close_app_comm
    apply (rule sound_weaken_appL)
    using close_eq big_sound SG_dec   
    by simp
qed

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
    using step_result.simps(2) surj_pair
    by simp
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
  proof_result.simps deriv_result.simps start_proof.simps DIAndCutP12_def  DIAndSG1_def DIAndSG2_def DIAndCutP1_def Box_def DIAndCut34Elim1_def DIAndCut12Intro_def DIAndCut34Elim2_def DIAnd_def
  using pne12 pne13 pne14 pne23 pne24 pne34 by (auto)

end end
