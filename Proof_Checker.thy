theory "Proof_Checker" 
imports
  Ordinary_Differential_Equations.ODE_Analysis
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
  
begin 
section \<open>Proof Checker\<close>
text \<open>This proof checker defines a datatype for proof terms in dL and a function for checking proof
 terms, with a soundness proof that any proof accepted by the checker is a proof of a sound rule or
 valid formula.

 A simple concrete hybrid system and a differential invariant rule for conjunctions are provided
 as example proofs.
\<close>
  
lemma sound_weaken_gen:"\<And>A B C. sublist A B \<Longrightarrow> sound (A, C) \<Longrightarrow> sound (B,C)"
proof (rule soundI_mem)
  fix A B::"sequent list" 
    and C::"sequent" 
    and I::"interp"
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

lemma mem_appL:"List.member A x \<Longrightarrow> List.member (A @ B) x"
  by(induction A, auto simp add: member_rec)

lemma mem_appR:"List.member B x \<Longrightarrow> List.member (A @ B) x"
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

fun start_proof::"sequent \<Rightarrow> rule"
where "start_proof S = ([S], S)"
  
lemma start_proof_sound:"sound (start_proof S)"
  unfolding sound_def by auto
  
section \<open>Proof Checker Implementation\<close>

datatype rrule = ImplyR | AndR |CohideRR | TrueR | EquivR | Skolem | NotR
  | HideR | CutRight "formula" | EquivifyR | CommuteEquivR | BRenameR  ident ident
  | ExchangeR nat | OrR

(*  CohideR | *)
  
datatype lrule = ImplyL | AndL | HideL | FalseL
  | NotL | CutLeft "formula" | EquivL | BRenameL ident ident
  | OrL
(*  EquivForwardL | EquivBackwardL |  *)
datatype  axRule =
(*  CT
|*) CQ (* "('a, 'c) trm" "('a, 'c) trm" "('a, 'b, 'c) subst" "('a, 'b, 'c) pt" (*"('c \<Rightarrow> trm )" "('c \<Rightarrow> trm )" *)"'c"*)
| CE (* "('a, 'b, 'c) formula" "('a, 'b, 'c) formula" "('a, 'b, 'c) subst" "('a, 'b, 'c) derivation"*)
| G
| monb


datatype axiom =
  AloopIter | AI | Atest | Abox | Achoice | AK | AV | Aassign | Adassign
| Advar | AdConst | AdPlus | AdMult
| ADW | ADE | ADC | ADS 
|(* ADIGr | ADG |*) AEquivReflexive | ADiffEffectSys
| AAllElim | ADiffLinear | ABoxSplit | AImpSelf | Acompose | AconstFcong | AdMinus | AassignEq | AallInst
| AassignAny | AequalCommute

| ATrueImply | Adiamond | AdiamondModusPonens | AequalRefl | AlessEqualRefl
| Aassignd | Atestd | Achoiced | Acomposed | Arandomd

datatype ruleApp =
  URename ident ident
(*| BRename 'c 'c*)
| RightRule "rrule" nat
| LeftRule "lrule" nat
| CloseId nat nat
| Cohide2 nat nat
| Cut "formula"
| DIGeqSchema "ODE" "trm" "trm"
| DIGrSchema "ODE" "trm" "trm"
| DIEqSchema "ODE" "trm" "trm"

(*| ARApp "('a,'b,'c) axRule"*)

datatype pt =
  FOLRConstant "formula"
| RuleApplication "pt" "ruleApp" nat
| AxiomaticRule " axRule"
| PrUSubst " pt" "subst"
| Ax axiom
| FNC "pt" "sequent" "ruleApp"
| Pro "pt" "pt"
| Start "sequent"
| Sub "pt" "pt" nat

type_synonym pf = "sequent * pt"
  
fun get_axiom:: "axiom \<Rightarrow> formula"
where 
  "get_axiom AloopIter = loop_iterate_axiom"
| "get_axiom AI = Iaxiom"
| "get_axiom Atest = test_axiom"
| "get_axiom Abox = box_axiom"
| "get_axiom Achoice = choice_axiom"
| "get_axiom AK = Kaxiom"
| "get_axiom AV = Vaxiom"
| "get_axiom Aassign = assign_axiom"
| "get_axiom Adassign = diff_assign_axiom" 
| "get_axiom AdConst = diff_const_axiom"
| "get_axiom AdPlus = diff_plus_axiom"
| "get_axiom AdMult = diff_times_axiom"
| "get_axiom Advar = diff_var_axiom"
| "get_axiom ADW = DWaxiom"
| "get_axiom ADE = DEaxiom"
| "get_axiom ADC = DCaxiom"
| "get_axiom ADS = DSaxiom"
(*| "get_axiom ADIGeq = DIGeqaxiom"
| "get_axiom ADIGr = DIGraxiom"*)
(*| "get_axiom ADG = DGaxiom"*)
| "get_axiom AEquivReflexive = EquivReflexiveAxiom"
| "get_axiom ADiffEffectSys = DiffEffectSysAxiom"
| "get_axiom AAllElim = AllElimAxiom"
| "get_axiom ADiffLinear = DiffLinearAxiom"
| "get_axiom ABoxSplit = BoxSplitAxiom"
| "get_axiom AImpSelf = ImpSelfAxiom"
| "get_axiom Acompose = compose_axiom"
| "get_axiom AconstFcong = constFcongAxiom"
| "get_axiom AdMinus = dMinusAxiom"
| "get_axiom AassignEq = assignEqAxiom"
| "get_axiom AallInst = allInstAxiom"
| "get_axiom AassignAny = assignAnyAxiom"
| "get_axiom AequalCommute = equalCommuteAxiom"
| "get_axiom ATrueImply = TrueImplyAxiom"
| "get_axiom Adiamond = diamondAxiom"
| "get_axiom AdiamondModusPonens = diamondModusPonensAxiom"
| "get_axiom AequalRefl = equalReflAxiom"
| "get_axiom AlessEqualRefl = lessEqualReflAxiom"
| "get_axiom Aassignd = assigndAxiom"
| "get_axiom Atestd = testdAxiom"
| "get_axiom Achoiced = choicedAxiom"
| "get_axiom Acomposed = composedAxiom"
| "get_axiom Arandomd = randomdAxiom"

fun get_axrule::"axRule \<Rightarrow> rule"
  where  
    (*"get_axrule CT = CTaxrule"
  |*) "get_axrule CQ = CQaxrule"
  | "get_axrule CE = CEaxrule"
  | "get_axrule G = Gaxrule"
  | "get_axrule monb = monbrule"

lemma axrule_sound:"sound (get_axrule ar)"
proof (cases ar)
  case CE
  then show ?thesis using sound_CEaxrule by auto
next
  case CQ
  then show ?thesis using sound_CQaxrule by auto
next
  case G
  then show ?thesis using sound_Gaxrule by auto
next
  case monb
  then show ?thesis using sound_monbrule by auto
qed

lemma invX:"Rep_ident (Abs_ident ''$x'') = ''$x''"
    apply(rule Abs_ident_inverse)
    by(auto simp add: max_str)
lemma invY:"Rep_ident (Abs_ident ''$y'') = ''$y''"
    apply(rule Abs_ident_inverse)
    by(auto simp add: max_str)
lemma invZ:"Rep_ident (Abs_ident ''$z'') = ''$z''"
    apply(rule Abs_ident_inverse)
    by(auto simp add: max_str)
lemma axiom_safe:"fsafe (get_axiom a)"
  by(cases a, auto simp add: axiom_defs Box_def Or_def Equiv_def Implies_def empty_def Equals_def 
   f1_def p1_def P_def f0_def expand_singleton Forall_def Greater_def id_simps DFunl_def Minus_def 
  TT_def Leq_def invX invY invZ ident_expose_def Ix_def Iy_def Iz_def SSENT_def FSENT_def SSENTINEL_def FSENTINEL_def max_str ilength_def) 

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
  case Adassign
  then show ?thesis by (simp add: diff_assign_valid)
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
(*next
  case ADIGeq
  then show ?thesis by (simp add: DIGeq_valid)
next
  case ADIGr
  then show ?thesis by (simp add: DIGr_valid)*)
(*next
  case ADG
  then show ?thesis by (simp add: DG_valid)*)
next
  case Advar
  then show ?thesis by (simp add: diff_var_axiom_valid)
next
  case AEquivReflexive
  then show ?thesis by (auto simp add: EquivReflexiveAxiom_def valid_def)
next
  case ADiffEffectSys
  then show ?thesis by (simp add: DiffEffectSys_valid)
next
  case AAllElim
  then show ?thesis by (simp add: AllElimAxiom_valid)
next
  case ADiffLinear
  then show ?thesis by (simp add: DiffLinear_valid)
next
  case ABoxSplit
  then show ?thesis by(auto simp add: BoxSplitAxiom_def valid_def)
next
  case  AImpSelf
  then show ?thesis by(auto simp add: ImpSelfAxiom_def TT_def valid_def)
next
  case Acompose
  then show ?thesis by(simp add: compose_valid)
next
  case AconstFcong
  then show ?thesis by (simp add: constFcong_valid)
next
  case AdMinus
  then show ?thesis by (simp add: dMinusAxiom_valid)
next
  case AassignEq
  then show ?thesis by (simp add: assignEq_valid)
next
  case AallInst
  then show ?thesis by (simp add: allInst_valid)
next
  case AassignAny
  then show ?thesis by (simp add: assignAny_valid)
next
  case AequalCommute
  then show ?thesis by (simp add: equalCommute_valid)
next
  case ATrueImply
  then show ?thesis by (simp add: TrueImply_valid)
next
  case Adiamond
  then show ?thesis by (simp add: diamond_valid)
next
  case AdiamondModusPonens
  then show ?thesis by (simp add: diamondModusPonens_valid)
next
  case AequalRefl
  then show ?thesis by (simp add: equalRefl_valid)
next
  case AlessEqualRefl
  then show ?thesis by (simp add: lessEqualRefl_valid)
next
  case Aassignd
  then show ?thesis by (simp add: assignd_valid)
next
  case Atestd
  then show ?thesis by (simp add: testd_valid)
next
  case Achoiced
  then show ?thesis by (simp add: choiced_valid)
next
  case Acomposed
  then show ?thesis by (simp add: composed_valid)
next
  case Arandomd
  then show ?thesis by (simp add: randomd_valid)
qed

fun seq_to_string :: "sequent \<Rightarrow> char list"
where "seq_to_string (A,S) = join '', '' (map fml_to_string A) @ '' |- '' @ join '', '' (map fml_to_string S)"
  
fun rule_to_string :: "rule \<Rightarrow> char list"
where "rule_to_string (SG, C) = (join '';;   '' (map seq_to_string SG)) @ ''            '' @  \<^cancel>\<open>[char_of_nat 10] @ \<close>seq_to_string C"

fun close :: "'a list \<Rightarrow> 'a \<Rightarrow>'a list"
where "close L x = filter (\<lambda>y. y \<noteq> x) L"

(* this way proof is harder but actually has right behavior *)
fun closeI ::"'a list \<Rightarrow> nat \<Rightarrow>'a list"
  where "closeI (x # xs) 0 = xs"
  | "closeI (x # xs) (Suc n) = x # (closeI xs n)"
  | "closeI Nil _ = undefined"

fun replaceI :: "'a list \<Rightarrow> nat \<Rightarrow> 'a  \<Rightarrow> 'a list"
  where "replaceI (x # xs) 0 y = (y # xs)"
  |  "replaceI (x # xs) (Suc n) y = x # (replaceI xs n y)"
  |  "replaceI Nil _ _ = undefined"
  

lemma close_sub:"sublist (close \<Gamma> \<phi>) \<Gamma>"
  apply (auto simp add: sublist_def)
  using member_filter by fastforce

lemma closeI_sub:"j < length \<Gamma> \<Longrightarrow> sublist (closeI \<Gamma> j) \<Gamma>"
proof -
  assume j:"j < length \<Gamma>"
  have imp:"j < length \<Gamma> \<Longrightarrow> sublist (closeI \<Gamma> j) \<Gamma>"
      apply(rule index_list_induct[of "(\<lambda> \<Gamma> j. sublist (closeI \<Gamma> j) \<Gamma>)"])
    subgoal for L by (auto simp add: sublist_def, cases L, auto simp add: member_rec)
    using j by(auto simp add: sublist_def member_rec j)
  then show ?thesis using j by auto
qed

lemma close_app_comm:"close (A @ B) x  = close A x @ close B x"
  by auto

lemma close_provable_sound:"sound (SG, C) \<Longrightarrow> sound (close SG \<phi>, \<phi>) \<Longrightarrow> sound (close SG \<phi>, C)"
proof (rule soundI_mem)
  fix I::"interp"
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


datatype rule_ret =
  Rok  "sequent list"
| Rerr "sequent list"

datatype step_ret =
  Sok  "rule"
| Serr "rule list"


fun LeftRule_result :: "lrule \<Rightarrow> nat \<Rightarrow> sequent \<Rightarrow> sequent list option"
  where "LeftRule_result AndL j (A,S) = (case (nth A j) of And p q \<Rightarrow> 
Some [((closeI A j) @ [p, q], S)] 
| _ \<Rightarrow> None)"
| "LeftRule_result ImplyL j (A,S) = (case (nth A j) of Not (And (Not q) (Not (Not p))) \<Rightarrow> 
   Some [(closeI A j, S @ [p]), 
         (replaceI A j q, S)] | _ \<Rightarrow> None)"
(*| "LeftRule_result EquivForwardL j (A,S) = (case (nth A j) of Not(And (Not (And p q)) (Not (And (Not p') (Not q')))) \<Rightarrow>
   (if (p = p' & q = q') then Some [(closeI A j @ [q], S), (closeI A j,  S @ [p])] else None) | _ \<Rightarrow> None)"
| "LeftRule_result EquivBackwardL j (A,S) = (case (nth A j) of Not(And (Not (And p q)) (Not (And (Not p') (Not q')))) \<Rightarrow>
   (if (p = p' & q = q') then Some [(closeI A j @ [p], S), (closeI A j , S @ [q])] else None) | _ \<Rightarrow> None)"*)
| "LeftRule_result HideL j (A,S) = 
   Some [(closeI A j, S)]"
| "LeftRule_result (CutLeft f) j (A,S) = Some [((replaceI A j f),S), ((closeI A j), S @[Implies (nth A j) f])]"
| "LeftRule_result EquivL j (A,S) = (case (nth A j) of Not(And (Not (And p q)) (Not (And (Not p') (Not q')))) \<Rightarrow>
   (if (p = p' & q = q') then Some [(replaceI A j (And p q), S), (replaceI A j (And (Not p) (Not q)) , S)] else None) | _ \<Rightarrow> None)"
| "LeftRule_result (BRenameL x y) j (A,S)      = (if x = y then None else
  (case (nth A j) of
   Not(Diamond (Assign xvar \<theta>) (Not \<phi>)) \<Rightarrow>
    (if
      (x = xvar \<and>
     (TRadmit \<theta> \<and>  FRadmit([[Assign xvar \<theta>]]\<phi>) \<and> FRadmit \<phi> \<and> fsafe ([[Assign xvar \<theta>]]\<phi>) \<and>
     {Inl y, Inr y, Inr x} \<inter> FVF ([[Assign xvar \<theta>]]\<phi>) = {})  \<and>
        FRadmit ([[y := \<theta>]]FUrename xvar  y \<phi>) \<and>
      FRadmit (FUrename xvar y \<phi>) \<and>
    fsafe ([[y := \<theta>]]FUrename xvar y \<phi>) \<and>
  {Inl xvar, Inr xvar, Inr y} \<inter> FVF ([[y := \<theta>]]FUrename xvar y \<phi>) = {})
  
    then
        Some [(replaceI A j (FBrename x y (nth A j)),S)]
    else None)
   | Not(Exists xvar (Not \<phi>)) \<Rightarrow> 
    (if
      x = xvar \<and>
     (FRadmit(Forall xvar \<phi>) \<and>
      FRadmit \<phi> \<and> 
     fsafe (Forall xvar \<phi>) \<and>
     {Inl y, Inr y, Inr x} \<inter> FVF (Forall xvar \<phi>) = {}) \<and>
      FRadmit (Forall  y (FUrename xvar  y \<phi>)) \<and>
      FRadmit (FUrename xvar y \<phi>) \<and>
     fsafe (Forall y (FUrename xvar y \<phi>)) \<and>
     {Inl xvar, Inr xvar, Inr y} \<inter> FVF (Forall y (FUrename xvar y \<phi>)) = {}
    then
        Some [(replaceI A j (FBrename x y (nth A j)),S)]
    else None)

   | _ \<Rightarrow> None))"
| Lstep_Not:"LeftRule_result NotL j (A,S) = (case (nth A j) of (Not p) \<Rightarrow> Some [(closeI A j , S @ [p])] | _ \<Rightarrow> None)" 
| Lstep_FalseR:"LeftRule_result FalseL j (A,S) = (if (nth A j) = FF then (Some []) else None)"
| Lstep_OrL:"LeftRule_result OrL j (A,S) =
(case (nth A j) of
  Not (And (Not p) (Not q)) \<Rightarrow>
  Some [(replaceI A j p, S),
        (replaceI A j q, S)] 
| _ \<Rightarrow> None
)"

(* Note: Some of the pattern-matching here is... interesting. The reason for this is that we can only
   match on things in the base grammar, when we would quite like to check things in the derived grammar.
   So all the pattern-matches have the definitions expanded, sometimes in a silly way. *)
fun RightRule_result :: "rrule \<Rightarrow> nat \<Rightarrow> sequent \<Rightarrow> sequent list option"
  where 
  Rstep_Not:"RightRule_result NotR j (A,S) = (case (nth S j) of (Not p) \<Rightarrow> Some [(A @ [p], closeI S j)] | _ \<Rightarrow> None)"
| Rstep_And:"RightRule_result AndR j (A,S) = (case (nth S j) of (And p q) \<Rightarrow> Some [(A, replaceI S j p), (A, replaceI S j q)] | _ \<Rightarrow> None)"
| Rstep_Imply:"RightRule_result ImplyR j (A,S) = (case (nth S j) of Not (And (Not q) (Not (Not p))) \<Rightarrow> 
    Some [(A @ [p], (closeI S j) @ [q])] | _ \<Rightarrow> None)"
| Rstep_EquivR:"RightRule_result EquivR j (A,S) =
   (case (nth S j) of Not(And (Not (And p q)) (Not (And (Not p') (Not q')))) \<Rightarrow> 
                (if (p = p' \<and> q = q') then (Some [(A @ [p], (closeI S j) @ [q]), ( A @ [q], (closeI S j) @ [p])])
                else (None)) | _ \<Rightarrow> None)"
(*| Rstep_CohideR:"RightRule_result CohideR j (A,S) = Some [(A, [nth S j])]"*)
| Rstep_CohideRR:"RightRule_result CohideRR j (A,S) = Some [([], [nth S j])]"
| Rstep_TrueR:"RightRule_result TrueR j (A,S) = (case (nth S j) of (Geq (Const x) (Const y)) \<Rightarrow>
    (if (x = y & (sint (Rep_bword x) = 0)) then(Some []) else None) | _ \<Rightarrow> None)"
| Step_Skolem:"RightRule_result Skolem j (A,S) = (case (nth S j) of (Not (Exists x (Not p)))  \<Rightarrow> 
(if ((Inl x) \<notin> FVSeq (A,S)) \<and> 
    fsafe (foldr (&&) A TT) \<and> 
    fsafe (foldr (||) (closeI S j) FF)
then
  Some [(A, replaceI S j p)]
else None)
| _ \<Rightarrow> None)"
| RStep_BR:"RightRule_result (BRenameR x y) j (A,S)      = (if x = y then None else
  (case (nth S j) of
   Not(Diamond (Assign xvar \<theta>) (Not \<phi>)) \<Rightarrow>
    (if
      x = xvar \<and>
     (TRadmit \<theta> \<and>  FRadmit([[Assign xvar \<theta>]]\<phi>) \<and> FRadmit \<phi> \<and> fsafe ([[Assign xvar \<theta>]]\<phi>) \<and>
     {Inl y, Inr y, Inr x} \<inter> FVF ([[Assign xvar \<theta>]]\<phi>) = {})  \<and>
        FRadmit ([[y := \<theta>]]FUrename xvar  y \<phi>) \<and>
      FRadmit (FUrename xvar y \<phi>) \<and>
    fsafe ([[y := \<theta>]]FUrename xvar y \<phi>) \<and>
  {Inl xvar, Inr xvar, Inr y} \<inter> FVF ([[y := \<theta>]]FUrename xvar y \<phi>) = {}
  
    then
        Some [(A, replaceI S j (FBrename x y (nth S j)))]
    else None)
   | Not(Exists xvar (Not \<phi>)) \<Rightarrow> 
    (if
      x = xvar \<and>
     (FRadmit(Forall xvar \<phi>) \<and>
      FRadmit \<phi> \<and> 
     fsafe (Forall xvar \<phi>) \<and>
     {Inl y, Inr y, Inr x} \<inter> FVF (Forall xvar \<phi>) = {}) \<and>
      FRadmit (Forall  y (FUrename xvar  y \<phi>)) \<and>
      FRadmit (FUrename xvar y \<phi>) \<and>
     fsafe (Forall y (FUrename xvar y \<phi>)) \<and>
     {Inl xvar, Inr xvar, Inr y} \<inter> FVF (Forall y (FUrename xvar y \<phi>)) = {}
    then
        Some [(A, replaceI S j (FBrename x y (nth S j)))]
    else None)
   | _ \<Rightarrow> None))"
| RStep_ExchangeR:"RightRule_result (ExchangeR k) j (A,S) =
  (if j \<noteq> k \<and> k < length S then
    Some [(A, replaceI (replaceI S j (nth S k)) k (nth S j))]
  else None)"
| Rstep_OrR:"RightRule_result (OrR) j (A,S) =
(case (nth S j) of
  Not (And (Not p) (Not q)) \<Rightarrow>
  Some [(A, ((closeI S j) @ [p, q]))] 
| _ \<Rightarrow> None
)

"

(* TODO: Is this derivable *)


(*  (if ((case (SG ! i) of ([],[Not(Diamond(Assign x t) (Not p))]) \<Rightarrow> True | _ \<Rightarrow> False)) then
     Some (merge_seqs SG [SBrename x y (nth SG i)] i,C)
   else None)*)

| Rstep_HideR:"RightRule_result HideR j (A,S) = Some [(A, closeI S j)]"
(** G |- c, D    G |- c->p, D
  * ------------------------- (Cut right)
  *        G |- p, D*)
| Rstep_CutRight:"RightRule_result (CutRight v) j (A,S) = Some [(A, replaceI S j v), (A,replaceI S j (Implies v (nth S j)))]"
(* G |- a<->b, D
 * -------------
 * G |- a->b,  D*)
| Rstep_EquivifyR:"RightRule_result EquivifyR j (A,S) = (case (nth S j) of Not (And (Not q) (Not (Not p))) \<Rightarrow> 
Some [(A, replaceI S j (Equiv p q))] | _ \<Rightarrow> None)"
  (* G |- q<->p, D
  * ------------- (<->cR)
  * G |- p<->q, D*)
| Rstep_CommuteEquivR:"RightRule_result CommuteEquivR j (A,S) = (case nth S j of 
Not(And (Not (And p q)) (Not (And (Not p') (Not q')))) \<Rightarrow> 
                (if (p = p' \<and> q = q') then (Some[(A, replaceI S j (Equiv q p))])
                else None)| _ \<Rightarrow> None)"




lemma fml_seq_valid:"valid \<phi> \<Longrightarrow> seq_valid ([], [\<phi>])"
  unfolding seq_valid_def valid_def by auto

lemma closeI_provable_sound:"\<And>i. sound (SG, C) \<Longrightarrow> sound (closeI SG i, (nth SG i)) \<Longrightarrow> i < length SG \<Longrightarrow> sound (closeI SG i, C)"
proof (rule soundI_mem)
  fix i and I::"interp"
  assume S1:"sound (SG, C)"
  assume S2:"sound (closeI SG i, SG ! i)"
  assume good:"is_interp I"
  assume SGCs:"(\<And>\<phi>. List.member (closeI SG i) \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)"
  assume i:"i < length SG"
  have S\<phi>:"seq_sem I (SG ! i) = UNIV"
    using S2 apply simp
    apply(drule soundD_mem)
      using good apply auto
      using SGCs UNIV_I by fastforce
  have mem_close_ind:"(\<forall>P. List.member SG P \<longrightarrow> P \<noteq> (SG ! i) \<longrightarrow> List.member (closeI SG i) P)" 
    apply(rule index_list_induct[of "(\<lambda> SG i. (\<forall>P. List.member SG P \<longrightarrow> P \<noteq> (SG ! i) \<longrightarrow> List.member (closeI SG i) P))"])
    subgoal for L by(induction L,auto simp add: member_rec)
    by(auto simp add: member_rec i)
  then  have mem_close:"\<And>P. List.member SG P \<Longrightarrow> P \<noteq> (SG ! i) \<Longrightarrow> List.member (closeI SG i) P" 
    by auto
  have SGs:"\<And>P. List.member SG P \<Longrightarrow> seq_sem I P = UNIV"
    subgoal for P
      apply(cases "P = (SG ! i)")
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

lemma valid_to_sound:"seq_valid A \<Longrightarrow> sound (B, A)"
  unfolding seq_valid_def sound_def by auto

lemma sound_to_valid:"sound ([], A) \<Longrightarrow> seq_valid A"
  unfolding seq_valid_def sound_def by auto

lemma closeI_valid_sound:"\<And>i. i < length SG \<Longrightarrow> sound (SG, C) \<Longrightarrow> seq_valid (nth SG i) \<Longrightarrow> sound (closeI SG i, C)"
  using valid_to_sound closeI_provable_sound by auto
  
fun merge_rules :: "rule \<Rightarrow> rule \<Rightarrow> nat \<Rightarrow> rule option"
  where 
    "merge_rules (P1,C1) (Nil,C2) i  = 
    (if (i < length P1 \<and> nth P1 i = C2) then
      Some (closeI P1 i, C1)
    else 
      (None))"
  | "merge_rules (P1,C1) (S # SS, C2) i = 
    (if (i < length P1 \<and> nth P1 i = C2) then
      Some ((replaceI P1 i S) @ SS, C1)
    else None)"

lemma soundE_mem:"sound (SG,C) \<Longrightarrow> (\<And>I. is_interp I \<Longrightarrow> (\<And>\<phi>. List.member SG \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV) \<Longrightarrow> seq_sem I C = UNIV)"
proof -
  assume snd:"sound (SG,C)"
  have sound:"\<And>I. is_interp I \<Longrightarrow> 
      (\<And>i. i\<ge>0 \<Longrightarrow> i < length (fst (SG, C)) \<Longrightarrow> seq_sem I (fst (SG, C) ! i) = UNIV) \<Longrightarrow> seq_sem I C = UNIV"
    using snd[unfolded sound_def] by(auto)  
  fix I::"interp"
  assume good_interp:"is_interp I"
  assume pres:"(\<And>\<phi>. List.member SG \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)"
  show "seq_sem I C = UNIV" 
    apply(rule sound)
     apply(rule good_interp)
    apply(simp)
    subgoal for i
    using pres[of "SG ! i"] nth_member[of i SG]
    by auto
  done
qed

lemma permute_sound:
  assumes sound:"sound (SG1,C)"
  assumes permute:"set SG1 = set SG2"
  shows "sound (SG2,C)"
proof -
  have in_mem:"\<And>i L. (List.member L i) = (i \<in> set L)" 
    subgoal for i L
      apply(induction L)
      by(auto simp add: List.member_rec) 
    done
  have mem:"\<And>i. List.member SG1 i \<Longrightarrow> List.member SG2 i"
    subgoal for i
     using permute in_mem[of SG1 i] in_mem[of SG2 i] by auto done
  show ?thesis
    apply(rule soundI_mem)
    using soundE_mem[OF sound] permute mem by(auto)
qed


lemma closeI_perm: "i < length L \<Longrightarrow> set ((List.nth L i) # closeI L i) = set L"
proof -
  assume i:"i < length L"
  have imp:"i < length L \<longrightarrow> set ((List.nth L i) # closeI L i) = set L"
    apply(rule index_list_induct)
    subgoal for L by(cases L,auto)
    by(auto simp add: i)
  then show ?thesis using i by(auto)
qed

lemma merge_front_sound:
  assumes S1:"sound (C2 # SG1,C)"
  assumes S2:"sound (SG2,C2)"
  shows "sound (SG2 @ SG1,C)"
proof (rule soundI_mem)
  fix I::"interp"
  assume good_interp:"is_interp I"
  assume pres:"(\<And>\<phi>. List.member (SG2 @ SG1) \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)"
  have presL:"(\<And>\<phi>. List.member SG2 \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)" 
    subgoal for \<phi>
      using pres mem_appL[of "SG2" \<phi> "SG1"] by auto done
  have presR:"(\<And>\<phi>. List.member SG1 \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)" 
    subgoal for \<phi>
      using pres[of \<phi>] mem_appR[of SG1 \<phi> SG2] by auto done
  have cSem:"seq_sem I C2 = UNIV" 
    using soundE_mem[OF S2 good_interp presL] by auto
  have pres1:"(\<And>\<phi>. List.member (C2 # SG1) \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)"
    using cSem presR by(auto simp add: List.member_rec)
  show "seq_sem I C = UNIV"
     using soundE_mem[OF S1 good_interp pres1]
       soundE_mem[OF S2 good_interp presL] 
     by(auto)
 qed

lemma set_eq_left:
  assumes eq:"set A1 = set A2"
  shows "set (A1 @ L) = set (A2 @ L)"
  by(induction L,auto simp add: eq)

lemma closeI_set_perm:"i < length SG1 \<Longrightarrow> set (S # closeI SG1 i) = set (replaceI SG1 i S)"
proof -
  assume i:"i < length SG1"
  have imp:"i < length SG1 \<Longrightarrow> set (S # closeI SG1 i) = set (replaceI SG1 i S)"
    apply(rule index_list_induct[of "(\<lambda> SG1 i. set (S # closeI SG1 i) = set (replaceI SG1 i S))"])
    subgoal for L using i by(cases L,auto simp add: i)
    by(auto)
  then show ?thesis using i by auto
qed


lemma merge_rules_some_match:
  assumes merge:"merge_rules (SG1,C1) (SG2,C2) i = Some R"
  shows"nth SG1 i = C2"
  using merge  apply(cases SG2,simp) apply(cases " i < length SG1 \<and> SG1 ! i = C2",auto) apply(cases " i < length SG1 \<and> SG1 ! i = C2",auto)
  done

lemma  merge_rules_sound:
  assumes S1:"sound (SG1,C1)"
  assumes S2:"sound (SG2,C2)"
  assumes i:"i < length SG1"
  assumes merge:"merge_rules (SG1,C1) (SG2,C2) i = Some R"
  shows "sound R"
proof (cases SG2, auto)
  case Nil then have Result:"SG2 = []" by auto
  have at:"nth SG1 i = C2" using merge merge_rules_some_match by auto
  from Result have valid:"seq_valid C2" 
    using sound_to_valid S2 by auto
  then have valid:"seq_valid (nth SG1 i)" using at by auto 
  then show "sound R" 
    using closeI_valid_sound[OF i S1 valid] merge Result i at by auto 
next
  case (Cons S SS) then have Result:"SG2 = S # SS" by auto
  have at:"nth SG1 i = C2" using merge merge_rules_some_match by auto
  have sound1:"sound ([C2] @ closeI SG1 i, C1)"
    apply(rule permute_sound[OF S1])
    using closeI_perm[OF i] at by auto
  have sound2:"sound (SG2 @ closeI SG1 i, C1)"
    apply(rule merge_front_sound) 
    using sound1 S2 by auto
  have sound3:"sound ((S # closeI SG1 i) @ SS, C1)"
    apply(rule permute_sound[OF sound2])
    using Result by auto
  have sound:"sound (replaceI SG1 i S @ SS, C1)"
    apply(rule permute_sound[OF sound3])
    apply(rule set_eq_left) 
    apply(rule closeI_set_perm)
    by(rule i)
    then show "sound R" using merge at i Result by(auto)
    qed


fun rule_result :: "rule \<Rightarrow> (nat * ruleApp) \<Rightarrow>  rule option"
  where
  Step_LeftRule:"rule_result (SG,C) (i,LeftRule L j) =  
   (if j \<ge> length (fst (nth SG i)) then None else
   (case (LeftRule_result L j (nth SG i)) of
     Some a \<Rightarrow> merge_rules (SG,C) (a, nth SG i) i
   | None \<Rightarrow> None))"
| Step_RightRule:"rule_result (SG,C) (i,RightRule R j) =
   (if j \<ge> length (snd (nth SG i)) then None else
   (case (RightRule_result R j (nth SG i)) of
     Some a \<Rightarrow> merge_rules (SG,C) (a, nth SG i) i
   | None \<Rightarrow> None\<^cancel>\<open>[(SG,C)]\<close>))" 
| Step_Cut:"rule_result (SG,C) (i,Cut \<phi>) = 
  (if(fsafe \<phi>) then
    (let (A,S)= nth SG i in  (merge_rules (SG,C) ([(A @ [\<phi>], S), (A,  S @ [\<phi>])], (A,S)) i))
  else None)"
| Step_CloseId:"rule_result (SG,C) (i,CloseId j k)   = 
  (if (j < length (fst (nth SG i))) \<and> (k < length (snd (nth SG i))) \<and> nth (fst (nth SG i)) j = nth (snd (nth SG i)) k then
    Some (closeI SG i, C)
   else None)"
| Step_UR:"rule_result (SG, C) (i, URename x y)      = 
    (if(FRadmit (seq2fml (SG ! i)) \<and> FRadmit (seq2fml (SUrename x y (SG ! i))) \<and> fsafe (seq2fml (SUrename x y (SG ! i)))) then
      merge_rules (SG,C) ([SUrename x y (nth SG i)],nth SG i) i
    else None)"
| Step_Cohide2:"rule_result (SG, C) (i, Cohide2 j k) = 
(if ((j \<ge> length (fst (nth SG i))) \<or> (k \<ge> length (snd (nth SG i)))) then None 
 else
  (merge_rules (SG,C) ([([nth (fst(nth SG i)) j],[nth (snd(nth SG i)) k])], (nth SG i)) i))"
| Step_DIGeq:"rule_result (SG,C) (i, DIGeqSchema ODE \<theta>1 \<theta>2) =
(  let proved = 
    ([],[Implies 
      (Implies (DPredl vid1) (And (Geq \<theta>1 \<theta>2) ([[EvolveODE ODE (DPredl vid1)]](Geq (Differential \<theta>1) (Differential \<theta>2)))))
      ([[EvolveODE ODE (DPredl vid1)]](Geq \<theta>1 \<theta>2))])
   in 
   let wanted = nth SG i in
   if (proved = wanted \<and>
  osafe ODE \<and>
  dfree \<theta>1 \<and>
  dfree \<theta>2 \<and>
  FVT \<theta>1 \<subseteq> Inl ` ODE_dom ODE \<and>
  FVT \<theta>2 \<subseteq> Inl ` ODE_dom ODE) then
      Some (closeI SG i,C)
   else None)"
| Step_DIGr:"rule_result (SG,C) (i, DIGrSchema ODE \<theta>1 \<theta>2) =
(  let proved = 
    ([],[Implies 
      (Implies (DPredl vid1) (And (Greater \<theta>1 \<theta>2) ([[EvolveODE ODE (DPredl vid1)]](Geq (Differential \<theta>1) (Differential \<theta>2)))))
      ([[EvolveODE ODE (DPredl vid1)]](Greater \<theta>1 \<theta>2))])
   in 
   let wanted = nth SG i in
   if (proved = wanted \<and>
  osafe ODE \<and>
  dfree \<theta>1 \<and>
  dfree \<theta>2 \<and>
  FVT \<theta>1 \<subseteq> Inl ` ODE_dom ODE \<and>
  FVT \<theta>2 \<subseteq> Inl ` ODE_dom ODE) then
      Some (closeI SG i,C)
   else None)"
| Step_DIEq:"rule_result (SG,C) (i, DIEqSchema ODE \<theta>1 \<theta>2) =
(  let proved = 
    ([],[Implies 
      (Implies (DPredl vid1) (And (Equals \<theta>1 \<theta>2) ([[EvolveODE ODE (DPredl vid1)]](Equals (Differential \<theta>1) (Differential \<theta>2)))))
      ([[EvolveODE ODE (DPredl vid1)]](Equals \<theta>1 \<theta>2))])
   in 
   let wanted = nth SG i in
   if (proved = wanted \<and>
  osafe ODE \<and>
  dfree \<theta>1 \<and>
  dfree \<theta>2 \<and>
  FVT \<theta>1 \<subseteq> Inl ` ODE_dom ODE \<and>
  FVT \<theta>2 \<subseteq> Inl ` ODE_dom ODE) then
      Some (closeI SG i,C)
   else None)
"



fun fnc :: "rule \<Rightarrow> sequent \<Rightarrow> ruleApp \<Rightarrow> rule option"
  where "fnc r seq ra = 
  (case (rule_result (start_proof seq) (0,ra))   of
    Some rule \<Rightarrow> merge_rules rule r 0
  | None  \<Rightarrow> None)"

fun pro :: "rule \<Rightarrow> rule \<Rightarrow> rule option"
  where "pro r1 r2 = merge_rules r2 r1 0"

fun pt_result :: "pt \<Rightarrow> rule option"
where
  "pt_result (FOLRConstant f) = Some ([], ([],[f]))"  
| "pt_result (RuleApplication pt ra i) = (case (pt_result pt) of Some res \<Rightarrow> (if i \<ge> length (fst res) then None else rule_result res (i,ra)) | None \<Rightarrow> None)"
| "pt_result (AxiomaticRule ar) = Some(get_axrule ar)"
| "pt_result (PrUSubst pt sub) = (case (pt_result pt) of Some res \<Rightarrow> 
(if ssafe sub \<and> Radmit sub res \<and> Rsafe res \<and> (FVS sub = {} \<or> (fst res = []) \<or> res = CQaxrule) then
  Some (Rsubst res sub)
else None) | None \<Rightarrow> None)"
| "pt_result (Ax a) = Some([], ([],[get_axiom a]))"
| "pt_result (FNC pt seq ra) = 
(case (pt_result pt) of 
   Some res \<Rightarrow> fnc res seq ra
 | None \<Rightarrow> None)"
| "pt_result (Pro pt1 pt2) = 
  (case pt_result pt2 of
     Some res2 \<Rightarrow> 
     (if (1 \<noteq> length (fst (res2))) then None else
     (case pt_result pt1 of
       Some res1 \<Rightarrow> pro res1 res2
      | None \<Rightarrow> None))
   | None \<Rightarrow> None)"
| "pt_result (Start f) = Some(start_proof f)"
| "pt_result (Sub pt1 pt2 i) =
  (case pt_result pt1 of
     Some res1 \<Rightarrow> 
     (if (i \<ge> length (fst (res1))) then None else
       (case pt_result pt2 of
          Some res2 \<Rightarrow> merge_rules res1 res2 i
        | None \<Rightarrow> None))
   | None \<Rightarrow> None)"

thm Or_def
thm Implies_def  
inductive lrule_ok ::" sequent list \<Rightarrow> sequent \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> lrule \<Rightarrow> bool"
where
  LeftRule_And:"(case (nth (fst (nth SG i)) j) of  (p && q) \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> lrule_ok SG C i j AndL"
| LeftRule_EquivForward:"(case (nth (fst (nth SG i)) j) of (!(!(PPPP && Q) && !(! PP && ! QQ))) \<Rightarrow> (PPPP = PP) \<and> (Q = QQ)| _ \<Rightarrow> False) \<Longrightarrow> lrule_ok SG C i j EquivForwardL"
| LeftRule_Imply:"(case (nth (fst (nth SG i)) j) of ( !(!Q && !(!PP)))  \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> lrule_ok SG C i j ImplyL"
| LeftRule_EquivBackward:"(case (nth (fst (nth SG i)) j) of (!(!(PPPP && Q) && !(! PP && ! QQ))) \<Rightarrow> (PPPP = PP) \<and> (Q = QQ) | _ \<Rightarrow> False) \<Longrightarrow> lrule_ok SG C i j EquivBackwardL"
| LeftRule_False:"nth (fst (nth SG i)) j = Geq \<^bold>0 (One) \<Longrightarrow> lrule_ok SG C i j FalseL"
named_theorems prover "Simplification rules for checking validity of proof certificates" 
lemmas [prover] = axiom_defs Box_def Or_def Implies_def filter_append ssafe_def SDom_def FUadmit_def PFUadmit_def id_simps

inductive_simps 
    LeftRule_And[prover]: "lrule_ok SG C i j AndL"
and LeftRule_Imply[prover]: "lrule_ok SG C i j ImplyL"
and LeftRule_Forward[prover]: "lrule_ok SG C i j EquivForwardL"
and LeftRule_EquivBackward[prover]: "lrule_ok SG C i j EquivBackwardL"

inductive rrule_ok ::"sequent list \<Rightarrow> sequent \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rrule \<Rightarrow> bool"
where
  RightRule_And:"(case (nth (snd (nth SG i)) j) of (p && q) \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> rrule_ok SG C i j AndR"
| RightRule_Imply:"(case (nth (snd (nth SG i)) j) of ( !(!Q && !(!PP))) \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> rrule_ok SG C i j ImplyR"
| RightRule_Equiv:"(case (nth (snd (nth SG i)) j) of  (!(!(PPPP && Q) && !(! PP && ! QQ))) \<Rightarrow> (PPPP = PP) \<and> (Q = QQ) | _ \<Rightarrow> False) \<Longrightarrow> rrule_ok SG C i j EquivR"
(* Note: Used to ban no-op cohides because close function breaks if sequent unchanged by rule, but we should just get the close function right instead *)
| RightRule_Cohide:"length (snd (nth SG i)) > j \<Longrightarrow> \<^cancel>\<open>(length (snd (nth SG i)) \<noteq> 1) \<Longrightarrow>\<close> rrule_ok SG C i j CohideR"
| RightRule_CohideRR:"length (snd (nth SG i)) > j  \<Longrightarrow> \<^cancel>\<open> fst (nth SG i) \<noteq>  [] \<Longrightarrow>  length (snd (nth SG i)) \<noteq> 1 \<Longrightarrow>\<close> rrule_ok SG C i j CohideRR"
| RightRule_True:"nth (snd (nth SG i)) j = Geq \<^bold>0 \<^bold>0 \<Longrightarrow> rrule_ok SG C i j TrueR"

(* | RightRule_Cohide:"length (snd (nth SG i)) > j \<Longrightarrow> (\<And>\<Gamma> q. (nth SG i) \<noteq> (\<Gamma>, [q])) \<Longrightarrow> rrule_ok SG C i j CohideR"
*)  
inductive_simps 
    RightRule_And_simps[prover]: "rrule_ok SG C i j AndR"
and RightRule_Imply_simps[prover]: "rrule_ok SG C i j ImplyR"
and RightRule_Equiv_simps[prover]: "rrule_ok SG C i j EquivR"
and RightRule_CohideR_simps[prover]: "rrule_ok SG C i j CohideR"
and RightRule_CohideRR_simps[prover]: "rrule_ok SG C i j CohideRR"
and RightRule_TrueR_simps[prover]: "rrule_ok SG C i j TrueR"

inductive sing_at::"(ident \<Rightarrow> trm) \<Rightarrow> trm \<Rightarrow> ident \<Rightarrow> bool"
  where sing_at_zero: "is_vid1 i \<Longrightarrow> f i = \<theta> \<Longrightarrow> sing_at f \<theta> i "
 |  sing_not_zero: "\<not>(is_vid1 i) \<Longrightarrow> f i = \<^bold>0 \<Longrightarrow> sing_at f \<theta> i"

inductive is_singleton :: "(ident \<Rightarrow> trm) \<Rightarrow> trm \<Rightarrow> bool"
  where Is_singleton: "(\<forall>i. sing_at (\<lambda>i. if is_vid1 i then \<theta> else \<^bold>0) \<theta> i) \<Longrightarrow> is_singleton (\<lambda>i. if is_vid1 i then \<theta> else \<^bold>0) \<theta> "

subsection \<open>Soundness\<close>

named_theorems member_intros "Prove that stuff is in lists"

lemma mem_sing[member_intros]:"\<And>x. List.member [x] x"
  by(auto simp add: member_rec)

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

lemma equiv_case_lem:"\<And>X. (case X of ! ((! (And PPPP Q)) && (! (And (! PP) (! QQ)))) \<Rightarrow>( PPPP = PP \<and> Q = QQ )
                          | ! (! (And PPPP Q) && (! (And (! PP) _))) \<Rightarrow> False
                          | ! (! (And PPPP Q) && (! (And _  formula2))) \<Rightarrow> False 
                          | ! (! (And PPPP Q) && (! _)) \<Rightarrow> False 
                          | ! (! (And PPPP Q) && _) \<Rightarrow> False
                          | ! (And (! _) formula2) \<Rightarrow> False 
                          | ! (And _ formula2) \<Rightarrow> False 
                          | ! _ \<Rightarrow> False 
                          | _ \<Rightarrow> False) \<Longrightarrow> (\<exists> Q P. (X = (Q \<leftrightarrow> P)))"
  subgoal for X
    apply(cases "\<exists> PPPP PP Q QQ. X = (! (! (PPPP && Q) && ! (! PP && ! QQ)))")
    subgoal apply auto subgoal for PP  QQ by (simp add: Equiv_def Or_def) done
proof -
  assume a0:"
    case X of Not (Not (PPPP && Q) && Not (Not PP && Not QQ)) \<Rightarrow> PPPP = PP \<and> Q = QQ | ! (! (PPPP && Q) && ! (Not PP && _)) \<Rightarrow> False
    | ! (Not (And PPPP Q) && Not (And _ xb)) \<Rightarrow> False 
    | ! (Not (And PPPP Q) && Not _) \<Rightarrow> False 
    | ! (Not (And PPPP Q) && _) \<Rightarrow> False 
    | ! (And (Not _)  xb) \<Rightarrow> False
    | ! (And _ xb) \<Rightarrow> False 
    | ! _ \<Rightarrow> False 
    | _ \<Rightarrow> False"
  assume a1:"\<nexists>PPPP PP Q QQ. X = ! (! (PPPP && Q) && ! (! PP && ! QQ))"
  show "\<exists>Q P. X = (Q \<leftrightarrow> P)"
    apply(cases "\<exists> PPPP Q PP QQ. X = ! (! (PPPP && Q) && ! (! PP && QQ))")
    subgoal using a0 a1 apply (auto simp add: Equiv_def Or_def) subgoal for PPPP Q PP QQ by(cases QQ, auto) done
      proof -
        assume a2:"\<nexists>PPPP Q PP QQ. X = ! (! (PPPP && Q) && ! (! PP && QQ))"
        show "\<exists>Q P. X = (Q \<leftrightarrow> P)"
    subgoal apply (auto simp add: Equiv_def Or_def)
      apply(cases "\<exists> PPPP Q x xb. X = (! (! (PPPP && Q) && ! (x && xb)))")
      subgoal using a0 a1 a2 apply (auto simp add: Equiv_def Or_def) subgoal for PPPP Q PP QQ by(cases PP, auto)
      done

    proof -
        assume a3:"\<nexists>PPPP Q x xb. X = ! (! (PPPP && Q) && ! (x && xb))"
        show "\<exists>Q P. X = ! (! (Q && P) && ! (! Q && ! P))"
          apply(cases "\<exists> PPPP Q QQ. X = ! (! (PPPP && Q) && ! QQ)")
          subgoal using a0 a1 a2 apply (auto simp add: Equiv_def Or_def) subgoal for PPPP Q PP  apply(cases PP, auto) subgoal for x41 x42 by (cases x41, auto) done done
        proof -
          assume a4:"\<nexists>PPPP Q QQ. X = ! (! (PPPP && Q) && ! QQ)"
          show "\<exists>Q P. X = ! (! (Q && P) && ! (! Q && ! P))"
            apply(cases "\<exists> PPPP Q QQ. (X =! (! (PPPP && Q) && QQ))") subgoal using a0 a1 a2 apply (auto simp add: Equiv_def Or_def) subgoal for PPPP Q QQ  apply(cases QQ, auto) subgoal for x41 apply (cases x41, auto)  subgoal for x41 by (cases x41, auto)done done done
          proof -
            assume a5:"\<nexists>PPPP Q QQ. X = ! (! (PPPP && Q) && QQ)"
            show "\<exists>Q P. X = ! (! (Q && P) && ! (! Q && ! P))"
              apply(cases "\<exists> PP QQ. X = (! (! PP && QQ))") subgoal using a0 a1 a2 a3 a4 a5 apply(auto simp add: Equiv_def Or_def) subgoal for PP QQ by(cases PP, auto) done
            proof -
              assume a6:"\<nexists>PP QQ. X = ! (! PP && QQ)"
              show "\<exists>Q P. X = ! (! (Q && P) && ! (! Q && ! P))"
                apply(cases "\<exists> PP QQ. X = (! ( PP && QQ))") subgoal using a0 a1 a2 a3 a4 a5 apply(auto simp add: Equiv_def Or_def) subgoal for PP QQ apply(cases PP, auto) subgoal for x3 by(cases x3, auto) done done
              proof -
                assume a7: "\<nexists>PP QQ. X = ! (PP && QQ)" 
                show "\<exists>Q P. X = ! (! (Q && P) && ! (! Q && ! P))"
                  apply(cases "\<exists> PP. X = (! PP)") subgoal using a0 a1 a2 a3 a4 a5 a6 a7 apply(auto simp add: Equiv_def Or_def) subgoal for PP by(cases PP, auto) done
                  using a0 a1 a2 a3 a4 a5 a6 a7 by(auto simp add: Equiv_def Or_def, cases X, auto)
              qed
            qed
          qed
        qed
      qed
      done
  qed
qed
  done
                
lemma imp_case_lem:"\<And>X. (case X of ! (! Q && ! (! PP)) \<Rightarrow> True | ! (! Q && ! _) \<Rightarrow> False | ! (! Q && _) \<Rightarrow> False | ! (_ && formula2) \<Rightarrow> False
    | ! _ \<Rightarrow> False | _ \<Rightarrow> False) \<Longrightarrow>
    (\<exists> Q P. X = (Q \<rightarrow> P))"
    subgoal for X
      apply (cases "\<exists>P. \<exists>Q. X = ! (! Q && ! (! P))", auto simp add: Implies_def Or_def expr_diseq)
    proof -
      assume a0:"case X of ! (! Q && ! (! PP)) \<Rightarrow> True | ! (! Q && ! _) \<Rightarrow> False | ! (! Q && _) \<Rightarrow> False | ! (_ && xb) \<Rightarrow> False | ! _ \<Rightarrow> False | _ \<Rightarrow> False"
      assume a1:"\<forall>P Q. X \<noteq> ! (! Q && ! (! P))"
      show False
        apply (cases "\<exists>P. \<exists>Q. X = ! (! Q && ! P)", auto simp add: Implies_def Or_def expr_diseq a0 a1)
        subgoal for P Q using a0 a1 by (auto, cases P, auto)
        proof -
          assume a2:"\<forall> P Q. X \<noteq> ! (! Q && ! P)"
          show False
            apply (cases "\<exists>P. \<exists>Q. X = ! (! Q &&  P)")
            subgoal using a0 a1 a2 apply (auto) subgoal for P Q by(cases P,auto) done
        proof -
          assume a3:"\<nexists>P Q. X = ! (! Q && P)"
          show False
            apply (cases "\<exists>P. \<exists>Q. X = ! ( Q &&  P)", auto simp add: Implies_def Or_def expr_diseq)
            subgoal for P Q using a0 a1 a2 a3 by (auto, cases Q, auto)
          proof -
            assume a4:"\<forall>P Q. X \<noteq> ! (Q && P)"
            show False
              apply (cases "\<exists>Q. X = ! Q")
                subgoal
                  apply(auto simp add: Implies_def Or_def expr_diseq a0 a1 a2 a3 a4) 
                  subgoal for Q using a0 a1 a2 a3 a4 by(cases "Q", auto simp add: a0 a1 a2 a3 a4)
                  done
                using a0 a1 a2 a3 a4 by (auto, cases X, auto)
            qed
          qed
        qed
      qed
    done


lemma foldr_fml_sem:"\<And>I L. fml_sem I (foldr (||) L FF) = (\<Union>\<phi>\<in> set L. fml_sem I \<phi>) "
  subgoal for I L
    by(induction L,auto)
  done

lemma disjunct_set:
  assumes perm:"set L1 = set L2"
  shows "fml_sem I (foldr (||) L1 FF) = fml_sem I (foldr (||) L2 FF)"
  using foldr_fml_sem[of I L1] foldr_fml_sem[of I L2] perm by auto


lemma  replaceI_closeI_set:"j < length \<Delta> \<Longrightarrow> set (replaceI \<Delta> j \<phi> ) = set (\<phi> # closeI \<Delta> j)"
proof -
  assume le:"j < length \<Delta>"
  have imp:"j < length \<Delta> \<longrightarrow> set (replaceI \<Delta> j \<phi> ) = set (\<phi> # closeI \<Delta> j)"
    apply(induction rule: index_list_induct[where P = "(\<lambda> \<Delta> j. j < length \<Delta> \<longrightarrow> set (replaceI \<Delta> j \<phi> ) = set (\<phi> # closeI \<Delta> j))"]) 
    subgoal for L by(cases L, auto)
    by(auto  simp add: le)
  then show ?thesis
    using le by auto
qed

lemma replaceI_assoc_disj:
"j < length \<Delta> \<Longrightarrow> fml_sem I (foldr (||) (replaceI \<Delta> j \<phi> ) FF) = fml_sem I (foldr (||) (\<phi> # closeI \<Delta> j) FF)"
proof -
  assume le:"j < length \<Delta>"
  have imp:"j < length \<Delta> \<longrightarrow> fml_sem I (foldr (||) (replaceI \<Delta> j \<phi> ) FF) = fml_sem I (foldr (||) (\<phi> # closeI \<Delta> j) FF)"
    apply(induction rule: index_list_induct[where P = "(\<lambda> \<Delta> j. j < length \<Delta> \<longrightarrow> fml_sem I (foldr (||) (replaceI \<Delta> j \<phi> ) FF) = fml_sem I (foldr (||) (\<phi> # closeI \<Delta> j) FF))"]) 
    subgoal for L by(cases L, auto)
    by(auto  simp add: le)
  then show ?thesis
    using le by auto
qed

lemma replaceI_assoc_conj:
"j < length \<Delta> \<Longrightarrow> fml_sem I (foldr (&&) (replaceI \<Delta> j \<phi> ) TT) = fml_sem I (foldr (&&) (\<phi> # closeI \<Delta> j) TT)"
proof -
  assume le:"j < length \<Delta>"
  have imp:"j < length \<Delta> \<longrightarrow> fml_sem I (foldr (&&) (replaceI \<Delta> j \<phi> ) TT) = fml_sem I (foldr (&&) (\<phi> # closeI \<Delta> j) TT)"
    apply(induction rule: index_list_induct[where P = "(\<lambda> \<Delta> j. j < length \<Delta> \<longrightarrow> fml_sem I (foldr (&&) (replaceI \<Delta> j \<phi> ) TT) = fml_sem I (foldr (&&) (\<phi> # closeI \<Delta> j) TT))"]) 
    subgoal for L by(cases L, auto)
    by(auto  simp add: le)
  then show ?thesis
    using le by auto
qed


lemma snoc_assoc_disj:
"fml_sem I (foldr (||) (\<Delta> @ [\<phi>]) FF) = fml_sem I (foldr (||) (\<phi> # \<Delta>) FF)"
  apply(induction \<Delta>)
  by(auto) 

lemma snoc_assoc_conj:
"fml_sem I (foldr (&&) (\<Delta> @ [\<phi>]) TT) = fml_sem I (foldr (&&) (\<phi> # \<Delta>) TT)"
  apply(induction \<Delta>)
  by(auto)

lemma snoc_assoc_sequent:
"seq_sem I (p # \<Gamma>,q # \<Delta>) = seq_sem I (\<Gamma> @ [p], \<Delta> @ [q])"
  using snoc_assoc_conj[of I \<Gamma> p] snoc_assoc_disj[of I \<Delta> q] by(auto)
  
lemma closeI_ident_disj:
  fixes j::nat
  assumes  j:"j < length \<Delta>"
  assumes  eq:"nth \<Delta> j = \<phi> "
  shows "fml_sem I (foldr (||) (\<phi> # (closeI \<Delta> j)) FF) = fml_sem I (foldr (||) \<Delta> FF) "
proof -
  have imp:"nth \<Delta> j = \<phi> \<longrightarrow> fml_sem I (foldr (||) (\<phi> # (closeI \<Delta> j)) FF) = fml_sem I (foldr (||) \<Delta> FF)"
    apply(induction rule: index_list_induct[where P = "(\<lambda>L n. nth L n = \<phi> \<longrightarrow> fml_sem I (foldr (||) (\<phi> # (closeI L n)) FF) = fml_sem I (foldr (||) L FF))"]) 
    subgoal for L by(cases L,auto)
    by(auto simp add: j)
  then show ?thesis
    by (auto simp add: eq)
qed

lemma closeI_ident_conj:
  fixes j::nat
  assumes  j:"j < length \<Gamma>"
  assumes  eq:"nth \<Gamma> j = \<phi> "
  shows "fml_sem I (foldr (&&) (\<phi> # (closeI \<Gamma> j)) TT) = fml_sem I (foldr (&&) \<Gamma> TT) "
proof -
  have imp:"nth \<Gamma> j = \<phi> \<longrightarrow> fml_sem I (foldr (&&) (\<phi> # (closeI \<Gamma> j)) TT) = fml_sem I (foldr (&&) \<Gamma> TT)"
    apply(induction rule: index_list_induct[where P = "(\<lambda>L n. nth L n = \<phi> \<longrightarrow> fml_sem I (foldr (&&) (\<phi> # (closeI L n)) TT) = fml_sem I (foldr (&&) L TT))"]) 
    subgoal for L by(cases L,auto)
    by(auto simp add: j)
  then show ?thesis
    by (auto simp add: eq)
qed

lemma replaceI_ident:
  fixes j::nat
  assumes  j:"j < length \<Delta>"
  assumes  eq:"nth \<Delta> j = \<phi> "
  shows "replaceI \<Delta> j \<phi> = \<Delta>"
proof -
  have imp:"nth \<Delta> j = \<phi> \<longrightarrow> replaceI \<Delta> j \<phi> = \<Delta>"
    apply(rule index_list_induct[where P = "(\<lambda>L n. nth L n = \<phi> \<longrightarrow> replaceI L n \<phi> = L)"])
    subgoal for L by (cases L,auto)
    by (auto simp add: j)
  then show ?thesis using eq by auto
qed

  
lemma replaceI_closeI_conj:
  fixes i::nat
  assumes rep:"\<nu> \<in> fml_sem I (foldr (&&)  (replaceI \<Gamma> i \<phi>) TT)"
  assumes i:"i < length \<Gamma>"
  shows "\<nu> \<in> fml_sem I (foldr (&&)  (\<phi> # closeI \<Gamma> i) TT)" 
proof -
  have imp:"i < length \<Gamma> \<longrightarrow> \<nu> \<in> fml_sem I (foldr (&&)  (replaceI \<Gamma> i \<phi>) TT) \<longrightarrow> (\<nu> \<in> fml_sem I (foldr (&&) (\<phi> # closeI \<Gamma> i) TT))"
    apply(rule index_list_induct[where P = "(\<lambda>\<Gamma> i. i < length \<Gamma> \<longrightarrow> \<nu> \<in> fml_sem I (foldr (&&)  (replaceI \<Gamma> i \<phi>) TT) \<longrightarrow> (\<nu> \<in> fml_sem I (foldr (&&)  (\<phi> # closeI \<Gamma> i) TT)))"])
    subgoal for L by(cases L,auto)
    by(auto simp add: i)
  then show ?thesis using i rep by auto
qed

lemma replaceI_closeI_conj_conv:
  fixes i::nat
  assumes rep:"\<nu> \<in> fml_sem I (foldr (&&)  (\<phi> # closeI \<Gamma> i) TT)" 
  assumes i:"i < length \<Gamma>"
  shows "\<nu> \<in> fml_sem I (foldr (&&)  (replaceI \<Gamma> i \<phi>) TT)"
proof -
  have imp:"i < length \<Gamma> \<longrightarrow> \<nu> \<in> fml_sem I (foldr (&&) (\<phi> # closeI \<Gamma> i) TT) \<longrightarrow> (\<nu> \<in> fml_sem I (foldr (&&) (replaceI \<Gamma> i \<phi>) TT))"
    apply(rule index_list_induct[where P = "(\<lambda>\<Gamma> i. i < length \<Gamma> \<longrightarrow> \<nu> \<in> fml_sem I (foldr (&&) (\<phi> # closeI \<Gamma> i) TT) \<longrightarrow> (\<nu> \<in> fml_sem I (foldr (&&)  (replaceI \<Gamma> i \<phi>) TT)))"])
    subgoal for L by(cases L,auto)
    by(auto simp add: i)
  then show ?thesis using i rep by auto
qed

lemma replaceI_closeI_disj:
  fixes i::nat
  assumes rep:"\<nu> \<in> fml_sem I (foldr (||)  (replaceI \<Delta> i \<phi>) FF)"
  assumes i:"i < length \<Delta>"
  shows "\<nu> \<in> fml_sem I (foldr (||)  (\<phi> # closeI \<Delta> i) FF)" 
proof -
  have imp:"i < length \<Delta> \<longrightarrow> \<nu> \<in> fml_sem I (foldr (||)  (replaceI \<Delta> i \<phi>) FF) \<longrightarrow> (\<nu> \<in> fml_sem I (foldr (||)  (\<phi> # closeI \<Delta> i) FF))"
    apply(rule index_list_induct[where P = "(\<lambda>\<Delta> i. i < length \<Delta> \<longrightarrow> \<nu> \<in> fml_sem I (foldr (||) (replaceI \<Delta> i \<phi>) FF) \<longrightarrow> (\<nu> \<in> fml_sem I (foldr (||)  (\<phi> # closeI \<Delta> i) FF)))"])
    subgoal for L by(cases L,auto)
    by(auto simp add: i)
  then show ?thesis using i rep by auto
qed
lemma TUrename_cancel:"TRadmit \<theta> \<Longrightarrow> \<theta> = (TUrename what repl  (TUrename what repl \<theta>)) "
proof (induction \<theta>)
qed (auto)

lemma TUrename_cancel_sym:"TRadmit \<theta> \<Longrightarrow> \<theta> = (TUrename repl what   (TUrename what repl \<theta>)) "
proof (induction \<theta>)
qed (auto)


lemma TUrename_scancel:"TRadmit \<theta> \<Longrightarrow> sterm_sem I \<theta> \<nu> = sterm_sem I (TUrename what repl  (TUrename what repl \<theta>)) \<nu> "
  using TUrename_cancel by auto

lemma TUrename_dcancel:"TRadmit \<theta> \<Longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I (TUrename what repl  (TUrename what repl \<theta>)) \<nu> "
  using TUrename_cancel by auto

lemma OUrename_cancel:"ORadmit ode \<Longrightarrow> \<^cancel>\<open>ODE_sem I \<close>ode\<^cancel>\<open> \<nu>\<close> = \<^cancel>\<open>ODE_sem I \<close>(OUrename what repl  (OUrename what repl ode)) \<^cancel>\<open>\<nu> \<close>"
proof (induction ode)
  case (OVar x)
  then show ?case by(auto)
next
  case (OSing x1a x2)
  then show ?case 
    by(auto simp add: TUrename_cancel)
next
  case (OProd ode1 ode2)
  then show ?case     
    by(auto)
qed

lemma OUrename_cancel_sym:"ORadmit ode \<Longrightarrow> ode = (OUrename repl what (OUrename what repl ode))"
proof (induction ode)
qed(auto simp add: TUrename_cancel_sym)

lemma FUrename_cancel_sym:"FRadmit \<phi> \<Longrightarrow> \<phi> = (FUrename repl what (FUrename what repl \<phi>)) "
and PUrename_cancel_sym:"PRadmit \<alpha> \<Longrightarrow> \<alpha> = (PUrename repl what (PUrename what repl \<alpha>)) "
proof (induction \<phi> and \<alpha>)
qed (auto simp add: TUrename_cancel_sym OUrename_cancel_sym)


lemma FUrename_cancel:"FRadmit \<phi> \<Longrightarrow> \<phi> = (FUrename what repl  (FUrename what repl \<phi>)) "
and PUrename_cancel:"PRadmit \<alpha> \<Longrightarrow> \<alpha> = (PUrename what repl  (PUrename what repl \<alpha>)) "
proof (induction \<phi> and \<alpha>)
case (Pvar x)
  then show ?case by(simp)
next
  case (Assign x1 x2)
  then show ?case by(auto simp add: TUrename_cancel)
next
  case (AssignAny x1)
  then show ?case by(auto)
next
  case (DiffAssign x1 x2)
  then show ?case by(auto simp add: TUrename_cancel)
next
  case (Test x)
  then show ?case by(auto)
next
  case (EvolveODE x1 x2)
  then show ?case by(auto simp add: OUrename_cancel)
next
  case (Choice x1 x2)
  then show ?case by auto
next
  case (Sequence x1 x2)
  then show ?case by auto
next
  case (Loop x)
then show ?case by auto
next
  case (Geq x1 x2)
  then show ?case by(auto simp add: TUrename_cancel)
next
  case (Prop x1 x2)
  then show ?case by(auto simp add: TUrename_cancel)
next
  case (Not x)
  then show ?case by auto
next
  case (And x1 x2)
  then show ?case by auto
next
  case (Exists x1 x2)
  then show ?case by auto
next
  case (Diamond x1 x2)
  then show ?case by auto
next
  case (InContext x1 x2)
  then show ?case by auto
qed

lemma TUrename_Zero[simp]: "TUrename what repl \<^bold>0 = \<^bold>0"
  by (auto simp: Zero_def)

lemma TUrename_One[simp]: "TUrename what repl \<^bold>1 = \<^bold>1"
  by (auto simp: One_def)

lemma FUrename_TT[simp]: "FUrename what repl TT = TT"
  by (auto simp: TT_def)

lemma FUrename_FF[simp]: "FUrename what repl FF = FF"
  by (auto simp: FF_def)

lemma foldr_FUrename_disj:"FUrename what repl (foldr (&&) a TT) = foldr (&&) (map (FUrename what repl) a) TT"
  by(induction a) (auto simp add: )

lemma foldr_FUrename_conj:"FUrename what repl (foldr (||) a FF) = foldr (||) (map (FUrename what repl) a) FF"
  by(induction a,auto simp add: FF_def Or_def)

lemma SUrename_FUrename:"seq2fml (SUrename what repl \<phi>)  = FUrename what repl (seq2fml \<phi>)"
  by(cases \<phi>, auto simp add: foldr_FUrename_disj foldr_FUrename_conj Implies_def Or_def)

lemma brename_dfree:"dfree \<theta> \<Longrightarrow> TRadmit \<theta> \<Longrightarrow> dfree (TUrename what repl \<theta>)"
proof (induction  rule: dfree.induct)
qed(auto)

lemma brename_dsafe:"dsafe \<theta> \<Longrightarrow> TRadmit \<theta> \<Longrightarrow> dsafe (TUrename what repl \<theta>)"
proof (induction rule: dsafe.induct )
qed(auto simp add:  brename_dfree)


lemma brename_tadmit:"TRadmit \<theta>  \<Longrightarrow> TRadmit (TUrename what repl \<theta>)"
proof (induction \<theta>)
  case (Var x)
then show ?case by auto
next
case (Const x)
  then show ?case by auto
next
case (Function x1a x2a)
  then show ?case by auto
next
  case (Functional x)
  then show ?case by auto
next
case (Plus \<theta>1 \<theta>2)
then show ?case by auto
next
  case (Times \<theta>1 \<theta>2)
  then show ?case by auto
next
  case (Max \<theta>1 \<theta>2)
  then show ?case by auto
next
  case (DiffVar x)
  then show ?case by auto
next
  case (Differential \<theta>)  
  then show ?case using brename_dfree by(auto simp add: brename_dfree)
qed (auto)

lemma brename_oadmit:"ORadmit ODE  \<Longrightarrow> ORadmit (OUrename what repl ODE)"
proof(induction ODE)
  case (OVar x)
  then show ?case by(auto)
next
  case (OSing x1a x2)
  then show ?case by(auto simp add: brename_tadmit brename_dfree)
next
  case (OProd ODE1 ODE2)
  then show ?case by(auto)
qed

lemma brename_fadmit:"FRadmit \<phi>  \<Longrightarrow> FRadmit (FUrename what repl \<phi>)"
 and  brename_padmit:"PRadmit \<alpha>  \<Longrightarrow> PRadmit (PUrename what repl \<alpha>)"
proof(induction \<phi> and \<alpha>)
  case (Pvar x)
  then show ?case by(auto)
next
  case (Assign x1 x2)
  then show ?case by(auto simp add: brename_tadmit brename_dfree)
next
  case (AssignAny x1)
  then show ?case by(auto simp add: brename_tadmit brename_dfree)
next
case (DiffAssign x1 x2)
  then show ?case by(auto simp add: brename_tadmit brename_dfree)
next
  case (Test x)
  then show ?case by(auto)
next
  case (EvolveODE x1 x2)
  then show ?case by(auto simp add: brename_tadmit brename_dfree brename_oadmit)
next
  case (Choice x1 x2)
  then show ?case by(auto)
next
  case (Sequence x1 x2)
  then show ?case by(auto)
next
  case (Loop x)
  then show ?case by(auto)
next
  case (Geq x1 x2)
  then show ?case  by(auto simp add: brename_tadmit brename_dfree)
next
  case (Prop x1 x2)
  then show ?case  by(auto simp add: brename_tadmit brename_dfree)
next
  case (Not x)
  then show ?case by auto
next
  case (And x1 x2)
  then show ?case by auto
next
  case (Exists x1 x2)
  then show ?case by auto
next
  case (Diamond x1 x2)
  then show ?case by auto
next
  case (InContext x1 x2)
  then show ?case by auto
qed

lemma brenameR_fadmitwhat_lem:"FRadmit ([[what := t]]p)  \<Longrightarrow> FRadmit ([[repl := t]]FUrename what repl p)"
  using brename_fadmit by (auto simp add: Box_def)
lemma brenameR_fadmitP_lem:  "FRadmit p \<Longrightarrow> FRadmit (FUrename what repl p)" using brename_fadmit by auto

lemma brenameR_all_admitwhat_lem:"  FRadmit (Forall what p) ==> FRadmit (Forall repl (FUrename what repl p))"
  using brename_fadmit by (auto simp add: Forall_def)

lemma lrule_sound:       
  assumes some:"(LeftRule_result L j (nth SG i)) = Some rres"
  assumes i:"i < length SG"
  assumes j:"j < length (fst (nth SG  i))"
  assumes sound:"sound (SG,C)"
  shows "sound (rres, nth SG i)"
proof(cases L)
  case ImplyL then have L:"L = ImplyL" by auto
  obtain p q where eq:"(fst (SG ! i) ! j) = (p \<rightarrow> q)" 
    using some L apply(cases "SG ! i",auto) subgoal for a b 
      apply(cases "a ! j", auto) subgoal for x3 apply(cases "x3", auto) 
        subgoal for x41 x42 apply (cases "x41", auto)
          apply (cases "x42", auto)
          subgoal for x3a x3aa by(cases x3aa,auto simp add: Implies_def Or_def)  done done done done
  have implyL_simp:"\<And>AI SI SS p q.
   (nth AI j) = Implies p q \<Longrightarrow>
   (AI,SI) = SS \<Longrightarrow>
   LeftRule_result ImplyL j SS = Some [(closeI AI j, SI @ [p]), (replaceI AI j q, SI)]" 
    subgoal for AI SI SS p q by(cases SS, auto simp add: Implies_def Or_def) done
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)" by (metis seq2fml.cases)
  have res_eq:"  LeftRule_result ImplyL j (SG ! i) = Some [(closeI \<Gamma> j, \<Delta> @ [p]), (replaceI \<Gamma> j q, \<Delta>)]" 
    apply(rule implyL_simp)
    using SG_dec eq Implies_def Or_def by (metis fstI)+
  have rres:"rres = [(closeI \<Gamma> j, \<Delta> @ [p]), (replaceI \<Gamma> j q, \<Delta>)]" using some res_eq L by auto
  have AIjeq:"\<Gamma> ! j = (p \<rightarrow> q)" using SG_dec eq unfolding Implies_def Or_def by (metis fst_conv)
  have jG:"j < length \<Gamma>" using j SG_dec by(cases "SG ! i", auto)
  have big_sound:"sound  ([(closeI \<Gamma> j, \<Delta> @ [p]), (replaceI \<Gamma> j q, \<Delta>)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(closeI \<Gamma> j, \<Delta> @ [p]), (replaceI \<Gamma> j q, \<Delta>)] \<Longrightarrow> \<nu> \<in> seq_sem I ([(closeI \<Gamma> j, \<Delta> @ [p]), (replaceI \<Gamma> j q, \<Delta>)] ! i))"
    assume ante:"\<nu> \<in> fml_sem I (foldr And \<Gamma> TT)"
    have jD:"j < length \<Gamma>" using j SG_dec by(cases "SG ! i",auto)
   have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
   have ante1:"\<nu> \<in> fml_sem I (foldr And (nth \<Gamma> j # closeI \<Gamma> j) TT)" 
     using duh[OF ante, of "fml_sem I (foldr (&&) (\<Gamma> ! j # closeI \<Gamma> j) TT)"] 
     closeI_ident_conj[OF jG , of "\<Gamma> ! j", of I, OF refl ] by auto
    have ante2:"\<nu> \<in> fml_sem I (foldr And (closeI \<Gamma> j) TT)" using ante1 by auto
    have ante3:"\<nu> \<in> fml_sem I (foldr And ((p \<rightarrow> q) # closeI \<Gamma> j) TT)" 
      using ante1 AIjeq by auto
    have sg1:"\<nu> \<in> seq_sem I (closeI \<Gamma> j, \<Delta> @ [p])" using sgs[of 0] by auto
    have succ1:"\<nu> \<in> fml_sem I (foldr Or (\<Delta> @ [p]) FF)" using ante2 sg1 seq_MP by auto
    have succ2:"\<nu> \<in> fml_sem I (foldr Or (p # \<Delta>) FF)" 
      using duh[OF succ1, of "fml_sem I (foldr Or (\<Delta> @ [p]) FF)"]
      using snoc_assoc_disj[of I \<Delta> p]  by auto
    have succOr:"\<nu> \<in> fml_sem I p \<or> \<nu> \<in> fml_sem I  (foldr Or (p # \<Delta>) FF)" using succ2 by auto 
    have sg2:"\<nu> \<in> seq_sem I (replaceI \<Gamma> j q, \<Delta>)" using sgs[of 1] by auto
    then have sg3:"\<nu> \<in> seq_sem I (q # closeI \<Gamma> j, \<Delta>)" 
      using replaceI_closeI_conj_conv[of \<nu> I q \<Gamma> j] jD by auto
    have sg4:"\<nu> \<in> fml_sem I q \<Longrightarrow> \<nu> \<in> fml_sem I  (foldr And (q # \<Gamma>) TT)" using ante sg3 by auto 
    have sg5:"\<nu> \<in> fml_sem I q \<Longrightarrow> \<nu> \<in> fml_sem I  (foldr Or (\<Delta>) FF)"
      apply(rule seq_MP[OF sg3]) using ante2 by auto
    show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using succOr apply simp
      apply(erule disjE) 
      subgoal using ante3 sg5 by auto.
  qed
  then show ?thesis using some SG_dec rres by auto
next
  case AndL  then have L:"L = AndL" by auto
  obtain p q where eq:"(fst (SG ! i) ! j) = (p && q)" 
    using some L apply(cases "SG ! i",auto) subgoal for a b 
      apply(cases "a ! j", auto) done done
  have andL_simp:"\<And>AI SI SS p q.
   (nth AI j) = And p q \<Longrightarrow>
   (AI,SI) = SS \<Longrightarrow>
   LeftRule_result AndL j SS = Some [((closeI AI j) @ [p, q], SI)]" 
    subgoal for AI SI SS p q by(cases SS, auto simp add: Implies_def Or_def) done
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)" by (metis seq2fml.cases)
  have res_eq:"  LeftRule_result AndL j (SG ! i) = Some [((closeI \<Gamma> j) @ [p, q], \<Delta>)]" 
    apply(rule andL_simp)
    using SG_dec eq by (metis fstI)+
  have rres:"rres = [((closeI \<Gamma> j) @ [p, q], \<Delta>)]" using some res_eq L by auto
  have AIjeq:"\<Gamma> ! j = (p && q)" using SG_dec eq unfolding Implies_def Or_def by (metis fst_conv)
  have jG:"j < length \<Gamma>" using j SG_dec by(cases "SG ! i", auto)
  have big_sound:"sound  ([((closeI \<Gamma> j) @ [p, q], \<Delta>)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [((closeI \<Gamma> j) @ [p, q], \<Delta>)] \<Longrightarrow> \<nu> \<in> seq_sem I ([((closeI \<Gamma> j) @ [p, q], \<Delta>)] ! i))"
    assume ante:"\<nu> \<in> fml_sem I (foldr And \<Gamma> TT)"
   have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
   have ante1:"\<nu> \<in> fml_sem I (foldr And (nth \<Gamma> j # closeI \<Gamma> j) TT)" 
     using duh[OF ante, of "fml_sem I (foldr (&&) (\<Gamma> ! j # closeI \<Gamma> j) TT)"] 
     closeI_ident_conj[OF jG , of "\<Gamma> ! j", of I, OF refl ] by auto
   then have ante2:"\<nu> \<in> fml_sem I (foldr And ((p && q) # (closeI \<Gamma> j)) TT)" 
     using closeI_ident_conj[OF jG , of "\<Gamma> ! j", of I, OF refl ] AIjeq by auto
   then have ante3:"\<nu> \<in> fml_sem I (foldr And (p # q # (closeI \<Gamma> j)) TT)" 
     by auto
   then have ante4:"\<nu> \<in> fml_sem I (foldr And (q # p # (closeI \<Gamma> j)) TT)" 
     by auto
   then have ante5:"\<nu> \<in> fml_sem I (foldr And ((q # (closeI \<Gamma> j))@[p]) TT)" 
      using snoc_assoc_conj[of I "(q # (closeI \<Gamma> j))" p]  by auto
   then have ante6:"\<nu> \<in> fml_sem I (foldr And (q # ((closeI \<Gamma> j)@[p])) TT)"  by auto
   then have ante7:"\<nu> \<in> fml_sem I (foldr And  (((closeI \<Gamma> j)@[p])@[q]) TT)" 
      using snoc_assoc_conj[of I "(closeI \<Gamma> j)@[p]" q]  by auto
   then have ante8:"\<nu> \<in> fml_sem I (foldr And  ((closeI \<Gamma> j)@[p,q]) TT)" by auto
    have sg1:"\<nu> \<in> seq_sem I ((closeI \<Gamma> j) @ [p, q], \<Delta>)" using sgs[of 0] by auto
    show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" using ante8 sg1 ante by auto
  qed
  then show ?thesis using some SG_dec rres by auto
next
  case HideL then have L:"L = HideL" by auto
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have hideL_simp:"\<And>\<Gamma> \<Delta> SS. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    LeftRule_result HideL j SS = Some [(closeI \<Gamma> j, \<Delta>)]"
    subgoal for AI SI SS apply(cases SS) apply (auto) done done
  have res_eq:"LeftRule_result HideL j (SG ! i) = 
    Some [(closeI \<Gamma> j, \<Delta>)] "
    apply(rule hideL_simp)
    subgoal using  SG_dec by (metis snd_conv) done
  have rres:"rres = [(closeI \<Gamma> j, \<Delta>)]" 
    using res_eq SG_dec hideL_simp some  i j L by auto
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  then have jD:"j < length \<Gamma>" using SG_dec j by auto
  have big_sound:"sound ([(closeI \<Gamma> j, \<Delta>)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume ante:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(closeI \<Gamma> j, \<Delta>)] \<Longrightarrow> \<nu> \<in> seq_sem I ([(closeI \<Gamma> j, \<Delta>)] ! i))"
     have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
    have sq1:"\<nu> \<in> seq_sem I (closeI \<Gamma> j, \<Delta>)" using sgs[of 0] by auto
    from ante have "\<nu> \<in> fml_sem I (foldr (&&) (nth \<Gamma> j # (closeI \<Gamma> j)) TT)"  
      using closeI_ident_conj[OF jD , of "\<Gamma> ! j", of I, OF refl] by auto
    then have ante2:"\<nu> \<in> fml_sem I (foldr (&&) (closeI \<Gamma> j) TT)"   by auto
    then show " \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using seq_MP sq1 by auto
     qed
  then show ?thesis using some SG_dec rres by auto
next
  case NotL then have L:"L = NotL" by auto
  obtain x p where eq:"(fst (SG ! i) ! j) = (Not p)"      
    using some i L apply(auto simp add: some i L) apply(cases "SG ! i",auto simp add: L Forall_def)
    subgoal for a b by(cases "a ! j", auto) done 
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have notL_simp:"\<And>\<Gamma> \<Delta> SS p. 
    (nth \<Gamma> j) = Not p \<Longrightarrow> 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    LeftRule_result NotL j SS = Some [(closeI \<Gamma> j, \<Delta> @ [p])]"
    subgoal for AI SI SS p apply(cases SS) apply (auto simp add: Forall_def Implies_def Or_def) done done
  have res_eq:"LeftRule_result NotL j (SG ! i) = 
    Some [(closeI \<Gamma> j, \<Delta> @ [p])]"
    apply(rule notL_simp)
    subgoal using eq SG_dec eq apply auto by(cases "SG ! i",auto)
    by (rule SG_dec) 
  have rres:"rres = [(closeI \<Gamma> j, \<Delta> @ [p])]" 
    using res_eq SG_dec notL_simp eq some  i j L by auto
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  have AIjeq:"\<Gamma> ! j = (Not  p)" using \<Gamma> eq by auto
  then have jD:"j < length \<Gamma>" using SG_dec j \<Gamma> by auto
  have big_sound:"sound ([(closeI \<Gamma> j, \<Delta> @ [p])], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(closeI \<Gamma> j, \<Delta> @ [p])] \<Longrightarrow> \<nu> \<in> seq_sem I ([(closeI \<Gamma> j, \<Delta> @ [p])] ! i))"
     have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
     have "\<nu> \<in> seq_sem I (closeI \<Gamma> j, \<Delta> @ [p])" using sgs[of 0] by auto
     have s1:"\<nu> \<in> seq_sem I (closeI \<Gamma> j, p # \<Delta>)" using sgs[of 0] snoc_assoc_disj by auto
     then have s2:"\<nu> \<in> seq_sem I (Not p # closeI \<Gamma> j,  \<Delta>)" using sgs[of 0] snoc_assoc_disj by auto
     then have s3:"\<nu> \<in> seq_sem I (nth \<Gamma> j #  closeI \<Gamma> j,  \<Delta>)" using sgs[of 0]AIjeq by (auto simp add: \<Delta> AIjeq)
     then have s4:"\<nu> \<in> seq_sem I ( \<Gamma> , \<Delta>)" using sgs[of 0]  AIjeq 
       closeI_ident_conj[OF jD , of "\<Gamma> ! j", of I, OF refl] by auto
     then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" 
       using closeI_ident_conj[OF jD AIjeq, of I] ante seq_MP[OF s4 ante] by auto
     qed
  then show ?thesis using some SG_dec rres by auto
next
  case (CutLeft cutFml) then have L:"L = CutLeft cutFml" by auto
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have cutL_simp:"\<And>\<Gamma> \<Delta> SS. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    LeftRule_result (CutLeft cutFml) j SS = 
    Some [((replaceI \<Gamma> j cutFml), \<Delta>), ((closeI \<Gamma> j), \<Delta> @[Implies (nth \<Gamma> j) cutFml])]"
    subgoal for AI SI SS apply(cases SS) apply (auto) done done
  have res_eq:"LeftRule_result (CutLeft cutFml) j (SG ! i) = 
    Some [((replaceI \<Gamma> j cutFml), \<Delta>), ((closeI \<Gamma> j), \<Delta> @[Implies (nth \<Gamma> j) cutFml])]"
    apply(rule cutL_simp)
    subgoal using  SG_dec by (metis snd_conv) done
  have rres:"rres = [((replaceI \<Gamma> j cutFml), \<Delta>), ((closeI \<Gamma> j), \<Delta> @[Implies (nth \<Gamma> j) cutFml])]" 
    using res_eq SG_dec cutL_simp some  i j L by auto
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  have jD:"j < length \<Gamma>" using \<Gamma> SG_dec j by auto
  have big_sound:"sound ([((replaceI \<Gamma> j cutFml), \<Delta>), ((closeI \<Gamma> j), \<Delta> @[Implies (nth \<Gamma> j) cutFml])], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    then have ante1:" \<nu> \<in> fml_sem I (foldr (&&) (nth \<Gamma> j #(closeI \<Gamma> j)) TT)" 
      using closeI_ident_conj[OF j, of "nth \<Gamma> j" ] \<Gamma> i j  by auto 
    then have ante2:" \<nu> \<in> fml_sem I (foldr (&&) ((closeI \<Gamma> j)) TT)" 
      using closeI_ident_conj[OF j, of "nth \<Gamma> j" ] \<Gamma> i j  by auto 
    then have ante3:" \<nu> \<in> fml_sem I (nth \<Gamma> j)" 
      using ante1 by auto 
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [((replaceI \<Gamma> j cutFml), \<Delta>), ((closeI \<Gamma> j), \<Delta> @[Implies (nth \<Gamma> j) cutFml])] \<Longrightarrow> \<nu> \<in> seq_sem I ([((replaceI \<Gamma> j cutFml), \<Delta>), ((closeI \<Gamma> j), \<Delta> @[Implies (nth \<Gamma> j) cutFml])] ! i))"
     have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
    have l1:"\<nu> \<in> seq_sem I ((replaceI \<Gamma> j cutFml), \<Delta>)" using sgs[of 0] by auto
    then have l2:"\<nu> \<in> seq_sem I (cutFml # closeI \<Gamma> j, \<Delta>)" 
      using replaceI_closeI_conj_conv[of \<nu> I cutFml \<Gamma> j] jD by auto
    have      r1:"\<nu> \<in> seq_sem I (closeI \<Gamma> j,  \<Delta> @[Implies (nth \<Gamma> j) cutFml])" using sgs[of 1] by auto
    then have f1:"\<nu> \<in> fml_sem I (foldr Or (\<Delta> @[Implies (nth \<Gamma> j) cutFml]) FF)"  using snoc_assoc_disj seq_MP ante2   by auto
    then have f2:"\<nu> \<in> fml_sem I (foldr Or (Implies (nth \<Gamma> j) cutFml # \<Delta>) FF)"
      using duh[OF f1, of "fml_sem I (foldr Or (Implies (nth \<Gamma> j) cutFml # \<Delta>) FF)"]
      using snoc_assoc_disj   by auto
    then have conj:"\<nu> \<in> fml_sem I (nth \<Gamma> j) \<and> (\<nu> \<in> fml_sem I (Implies (nth \<Gamma> j) cutFml) \<or> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF))"
       using ante3 by auto
    then show " \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      apply(simp)
      apply(erule conjE)
      apply(erule impE)
      subgoal.
      apply(erule disjE)
      subgoal using l2 ante2 by auto
      .
     qed
  then show ?thesis using some SG_dec rres by auto
next
  case EquivL then have L:"L = EquivL" by auto
  have exist:"\<exists> p q.(fst (SG ! i) ! j) =  Equiv p q"
    using some i L apply(auto simp add: some i L) apply(cases "SG ! i",auto simp add: L Equiv_def Implies_def Or_def)
    subgoal for a b
      apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto)
        subgoal for x41 x42 apply(cases x41,auto, cases x42, auto)
          subgoal for x3a x11 x12
            by(cases x3a,auto)
          subgoal for x3a x11 x12
            by(cases x3a,auto)
          subgoal for x3a x11 
            apply(cases x3a,auto,cases x11,auto)
            subgoal for x41a x42a x41aa x42aa
              apply(cases "x41aa",auto, cases x42aa,auto)
              subgoal for x3b x3aa
                by(cases "x41a = x3b \<and> x42a = x3aa",auto) done
            subgoal for x41a x42a x41aa x42aa
              apply(cases "x41aa",auto, cases x42aa,auto)
              subgoal for x3b x3aa
                by(cases "x41a = x3b \<and> x42a = x3aa",auto) done done
          subgoal for x3a x41a x42a
            by(cases x3a,auto)
          subgoal for x3a x51 x52
            by(cases x3a,auto)
          subgoal for x3a x61 x62
            by(cases x3a,auto)
          subgoal for x3a x71 x72
            by(cases x3a,auto) done done done done
  then obtain p q where eq:"(fst (SG ! i) ! j) = (p \<leftrightarrow> q)" by auto

  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have equivL_simp:"\<And>\<Gamma> \<Delta> p q SS. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    ((nth \<Gamma> j) = (p \<leftrightarrow> q)) \<Longrightarrow>
    LeftRule_result EquivL j SS =
    Some [(replaceI \<Gamma> j (And p q), \<Delta>), (replaceI \<Gamma> j (And (Not p) (Not q)) , \<Delta>)]"
    subgoal for AI SI p q SS apply(cases SS) by (auto simp add: Equiv_def Implies_def Or_def) done
  have res_eq:"LeftRule_result EquivL j (SG ! i) = 
    Some [(replaceI \<Gamma> j (And p q), \<Delta>), (replaceI \<Gamma> j (And (Not p) (Not q)) , \<Delta>)]"
    apply(rule equivL_simp)
    subgoal using  SG_dec by (metis snd_conv) 
    using eq SG_dec by(cases "SG ! i",auto)
  have rres:"rres = [(replaceI \<Gamma> j (And p q), \<Delta>), (replaceI \<Gamma> j (And (Not p) (Not q)) , \<Delta>)]" 
    using res_eq SG_dec equivL_simp some  i j L by auto
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  have jD:"j < length \<Gamma>" using \<Gamma> SG_dec j by auto
  have big_sound:"sound ([(replaceI \<Gamma> j (And p q), \<Delta>), (replaceI \<Gamma> j (And (Not p) (Not q)) , \<Delta>)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    then have ante1:" \<nu> \<in> fml_sem I (foldr (&&) (nth \<Gamma> j #(closeI \<Gamma> j)) TT)" 
      using closeI_ident_conj[OF j, of "nth \<Gamma> j" ] \<Gamma> i j  by auto 
    then have ante2:" \<nu> \<in> fml_sem I (foldr (&&) ((closeI \<Gamma> j)) TT)" 
      using closeI_ident_conj[OF j, of "nth \<Gamma> j" ] \<Gamma> i j  by auto 
    then have ante3:" \<nu> \<in> fml_sem I (p \<leftrightarrow> q)" 
      using ante1 eq \<Gamma> by auto 
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> 
    i < length [(replaceI \<Gamma> j (And p q), \<Delta>), (replaceI \<Gamma> j (And (Not p) (Not q)) , \<Delta>)] \<Longrightarrow> 
          \<nu> \<in> seq_sem I ([(replaceI \<Gamma> j (And p q), \<Delta>), (replaceI \<Gamma> j (And (Not p) (Not q)) , \<Delta>)] ! i))"
     have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
    have l1:"\<nu> \<in> seq_sem I (replaceI \<Gamma> j (And p q), \<Delta>)" using sgs[of 0] by auto
    then have l2:"\<nu> \<in> seq_sem I ((And p q) # closeI \<Gamma> j, \<Delta>)" 
      using replaceI_closeI_conj_conv[of \<nu> I "p && q" \<Gamma> j] jD by(auto)
    then have l3:"\<nu> \<in> seq_sem I (p # q # closeI \<Gamma> j, \<Delta>)" by auto
    have      r1:"\<nu> \<in> seq_sem I (replaceI \<Gamma> j (And (Not p) (Not q)), \<Delta>)" using sgs[of 1] by auto
    have r2:"\<nu> \<in> seq_sem I ((And (Not p) (Not q)) # closeI \<Gamma> j , \<Delta>)" 
    proof (auto)
      assume nf1:"\<nu> \<notin> fml_sem I p"
      assume nf2:"\<nu> \<notin> fml_sem I q"
      assume f:"\<nu> \<in> fml_sem I (foldr (&&) (closeI \<Gamma> j) TT)"
      have f2:"\<nu> \<in> fml_sem I (foldr (&&) (replaceI \<Gamma> j (! p && ! q)) TT)"
        using nf1 nf2 f replaceI_closeI_conj_conv[of \<nu> I  "(And (Not p) (Not q))" \<Gamma> j] jD by auto
      show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
        by (rule seq_MP[OF r1 f2])
    qed
    then have r3:"\<nu> \<in> seq_sem I ((Not p) # (Not q) # closeI \<Gamma> j, \<Delta>)" by auto
    then show " \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using l3 r3 ante3 ante2 by(auto)
  qed
  then show ?thesis using some SG_dec rres by auto
next
  case (BRenameL what repl) then have L:"L = BRenameL what repl" by auto
  have exist:"(\<exists> t p.(fst (SG ! i) ! j) =  ([[what := t]]p)) \<or> (\<exists> p. (fst (SG ! i) ! j) = Forall what p)"
    using some i L apply(auto simp add: some i L) apply(cases "SG ! i",auto simp add: L Equiv_def Implies_def Or_def)
    apply(cases "what = repl",auto)
    subgoal for a b
      apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto)
        subgoal for x61 x62
          apply(cases x62,auto) subgoal for x3a
              apply(cases "what = x61 \<and> FRadmit (Forall x61 x3a) \<and>
        FRadmit x3a \<and>
        fsafe (Forall x61 x3a) \<and>
        Inl repl \<notin> FVF (Forall x61 x3a) \<and>
        Inr repl \<notin> FVF (Forall x61 x3a) \<and>
        Inr x61 \<notin> FVF (Forall x61 x3a) \<and>
        FRadmit (Forall repl (FUrename x61 repl x3a)) \<and>
        FRadmit (FUrename x61 repl x3a) \<and>
        fsafe (Forall repl (FUrename x61 repl x3a)) \<and>
        Inl x61 \<notin> FVF (Forall repl (FUrename x61 repl x3a)) \<and>
        Inr x61 \<notin> FVF (Forall repl (FUrename x61 repl x3a)) \<and> Inr repl \<notin> FVF (Forall repl (FUrename x61 repl x3a))")
               apply(auto simp add: Box_def)
             apply(cases "what = x61",auto simp add: Box_def, cases "repl = x61",simp add: Box_def Forall_def)
            apply(erule allE[where x="x3a"], unfold Forall_def) by auto done
        subgoal for x61 x62
          apply(cases x61,auto)
          subgoal for x21 x22
            apply(cases x62,auto)
            subgoal for x3a
        
        apply(cases "what = x21 \<and>
        TRadmit x22 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x21 := x22]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x21 := x22]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x21 := x22]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x21 := x22]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x21 := x22]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x21 := x22]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x21 := x22]]x3a) \<and>
        Inl repl \<notin> FVF ([[x21 := x22]]x3a) \<and> Inr repl \<notin> FVF ([[x21 := x22]]x3a) \<and> Inr what \<notin> FVF ([[x21 := x22]]x3a)",auto simp add: Box_def)

              by(cases "what = x21 \<and>
        TRadmit x22 \<and>
        FRadmit x3a \<and>
        dsafe x22 \<and>
        fsafe x3a \<and>
        Inl repl \<notin> FVT x22 \<and>
        (Inl repl \<in> FVF x3a \<longrightarrow> repl = x21) \<and>
        Inr repl \<notin> FVT x22 \<and>
        Inr repl \<notin> FVF x3a \<and>
        Inr what \<notin> FVT x22 \<and>
        Inr what \<notin> FVF x3a \<and>
        TRadmit x22 \<and>
        FRadmit (FUrename x21 repl x3a) \<and>
        dsafe x22 \<and>
        fsafe (FUrename x21 repl x3a) \<and>
        Inl x21 \<notin> FVT x22 \<and>
        (Inl x21 \<in> FVF (FUrename x21 repl x3a) \<longrightarrow> x21 = repl) \<and>
        Inr x21 \<notin> FVT x22 \<and> Inr x21 \<notin> FVF (FUrename x21 repl x3a) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF (FUrename x21 repl x3a)",auto)+

            done done done done done

  have all_case:"(\<exists>  p.(fst (SG ! i) ! j) =  (Forall what p)) \<Longrightarrow> ?thesis"
  proof -
    assume "(\<exists>  p.(fst (SG ! i) ! j) =  (Forall what p))"
    then obtain  p where eq:"(fst (SG ! i) ! j) = (Forall what p)" by(auto)
    have admits:
     " FRadmit (Forall what p) \<and> FRadmit p \<and> fsafe (Forall what  p) \<and>
           {Inl repl, Inr repl, Inr what} \<inter> FVF (Forall what p) = {} \<and>
          FRadmit (Forall repl (FUrename what  repl p)) \<and>
         FRadmit (FUrename what repl p) \<and>
         fsafe (Forall repl (FUrename what repl p)) \<and>
         {Inl what, Inr what, Inr repl} \<inter> FVF (Forall repl (FUrename what repl p)) = {}"

            using some i L  apply(cases "SG ! i", auto simp add: L Equiv_def Implies_def Or_def some i)apply(cases "what = repl",auto)
            subgoal for a b
              apply(cases "a ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62,auto)
                  subgoal for x3a using eq apply(cases "FRadmit p \<and> fsafe p \<and> Inl repl \<notin> FVF p \<and> Inr repl \<notin> FVF p \<and> Inr what \<notin> FVF p ",auto simp add: Box_def Forall_def eq) done done
                subgoal for x61 x62 apply(cases x61,auto,cases x62,auto) 
                  subgoal for x21 x22 x3a using eq
                  by(cases "what = x21 \<and>
           TRadmit x22 \<and>
           ((\<exists>\<theta>1 \<theta>2. ([[x21 := x22]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
            (\<exists>args. (\<exists>p. ([[x21 := x22]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
            (\<exists>\<phi>. ([[x21 := x22]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
            (\<exists>\<phi> \<psi>. ([[x21 := x22]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
            (\<exists>\<phi>. (\<exists>x. ([[x21 := x22]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x21 := x22]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
           FRadmit x3a \<and>
           fsafe ([[x21 := x22]]x3a) \<and>
           Inl repl \<notin> FVF ([[x21 := x22]]x3a) \<and> Inr repl \<notin> FVF ([[x21 := x22]]x3a) \<and> Inr what \<notin> FVF ([[x21 := x22]]x3a)",auto simp add: Forall_def)
                done done done
                subgoal for a b
                  apply(cases "what = repl",auto)
              apply(cases "a ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21  using eq apply(cases x62,auto) 
                    by(cases " what = x61 \<and>
        FRadmit (Forall x61 x21) \<and>
        FRadmit x21 \<and> fsafe (Forall x61 x21) \<and> Inl repl \<notin> FVF (Forall x61 x21) \<and> Inr repl \<notin> FVF (Forall x61 x21) \<and> Inr what \<notin> FVF (Forall x61 x21)
",auto simp add: Forall_def)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  done
                subgoal for a b
                 apply(cases "what = repl",auto)
              apply(cases "a",auto) apply(cases "b",auto simp add: Box_def)
                  subgoal for x21 x22 x3
                    apply(cases "what = x21 \<and>
        TRadmit x22 \<and>
        FRadmit x3 \<and>
        dsafe x22 \<and>
        fsafe x3 \<and>
        Inl repl \<notin> FVT x22 \<and> (Inl repl \<in> FVF x3 \<longrightarrow> repl = x21) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF x3 \<and> Inr what \<notin> FVT x22 \<and> Inr what \<notin> FVF x3
")
                    subgoal  using eq by(auto simp add: Box_def Forall_def)
                    subgoal  using eq by(auto simp add: Box_def Forall_def) done done done done

                subgoal for a b
                  apply(cases "what = repl",auto, cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Forall_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Forall_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Forall_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Box_def Forall_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Forall_def)  
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def Forall_def) 
                      done done
                    done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Forall_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def Forall_def) 
                      done done
                    done done 
              subgoal for a b
              apply(cases "what = repl",auto, cases "a ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62,auto)
                  subgoal for x3a using eq
                    apply(cases "what = x61 \<and>
        FRadmit (Forall x61 x3a) \<and>
        FRadmit x3a \<and>
        fsafe (Forall x61 x3a) \<and>
        Inl repl \<notin> FVF (Forall x61 x3a) \<and>
        Inr repl \<notin> FVF (Forall x61 x3a) \<and>
        Inr what \<notin> FVF (Forall x61 x3a) \<and>
        FRadmit (Forall repl (FUrename x61 repl x3a)) \<and>
        FRadmit (FUrename x61 repl x3a) \<and>
        fsafe (Forall repl (FUrename x61 repl x3a)) \<and>
        Inl x61 \<notin> FVF (Forall repl (FUrename x61 repl x3a)) \<and>
        Inr x61 \<notin> FVF (Forall repl (FUrename x61 repl x3a)) \<and> Inr repl \<notin> FVF (Forall repl (FUrename x61 repl x3a))",auto simp add: Box_def Forall_def eq) done done
                subgoal for x61 x62 apply(cases x61,auto,cases x62,auto) 
                  subgoal for x21 x22 x3a using eq
                  by(cases "what = x21 \<and>
           TRadmit x22 \<and>
           ((\<exists>\<theta>1 \<theta>2. ([[x21 := x22]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
            (\<exists>args. (\<exists>p. ([[x21 := x22]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
            (\<exists>\<phi>. ([[x21 := x22]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
            (\<exists>\<phi> \<psi>. ([[x21 := x22]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
            (\<exists>\<phi>. (\<exists>x. ([[x21 := x22]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x21 := x22]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
           FRadmit x3a \<and>
           fsafe ([[x21 := x22]]x3a) \<and>
           Inl repl \<notin> FVF ([[x21 := x22]]x3a) \<and> Inr repl \<notin> FVF ([[x21 := x22]]x3a) \<and> Inr what \<notin> FVF ([[x21 := x22]]x3a)",auto simp add: Forall_def)
                done done done
                subgoal for a b
                  apply(cases "what = repl",auto)
              apply(cases "a ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21  using eq apply(cases x62,auto) 
                    by(cases "what = x61 \<and>
        FRadmit (Forall x61 x21) \<and>
        FRadmit x21 \<and>
        fsafe (Forall x61 x21) \<and>
        Inl repl \<notin> FVF (Forall x61 x21) \<and>
        Inr repl \<notin> FVF (Forall x61 x21) \<and>
        Inr what \<notin> FVF (Forall x61 x21) \<and>
        FRadmit (Forall repl (FUrename x61 repl x21)) \<and>
        FRadmit (FUrename x61 repl x21) \<and>
        fsafe (Forall repl (FUrename x61 repl x21)) \<and>
        Inl x61 \<notin> FVF (Forall repl (FUrename x61 repl x21)) \<and>
        Inr x61 \<notin> FVF (Forall repl (FUrename x61 repl x21)) \<and> Inr repl \<notin> FVF (Forall repl (FUrename x61 repl x21))",auto simp add: Forall_def)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  done
                subgoal for a b
                 apply(cases "what = repl",auto)
              apply(cases "a",auto) apply(cases "b",auto simp add: Box_def)
                  subgoal for x21 x22 x3
                    apply(cases "what = x21 \<and>
        TRadmit x22 \<and>
        FRadmit x3 \<and>
        dsafe x22 \<and>
        fsafe x3 \<and>
        Inl repl \<notin> FVT x22 \<and> (Inl repl \<in> FVF x3 \<longrightarrow> repl = x21) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF x3 \<and> Inr what \<notin> FVT x22 \<and> Inr what \<notin> FVF x3
")
                    subgoal  using eq by(auto simp add: Box_def Forall_def)
                    subgoal  using eq by(auto simp add: Box_def Forall_def) done done done done

                subgoal for a b
                  apply(cases "what = repl",auto, cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and>
        FRadmit (Forall x51 x3a) \<and>
        FRadmit x3a \<and>
        fsafe (Forall x51 x3a) \<and>
        Inl repl \<notin> FVF (Forall x51 x3a) \<and>
        Inr repl \<notin> FVF (Forall x51 x3a) \<and>
        Inr what \<notin> FVF (Forall x51 x3a) \<and>
        FRadmit (Forall repl (FUrename x51 repl x3a)) \<and>
        FRadmit (FUrename x51 repl x3a) \<and>
        fsafe (Forall repl (FUrename x51 repl x3a)) \<and>
        Inl x51 \<notin> FVF (Forall repl (FUrename x51 repl x3a)) \<and>
        Inr x51 \<notin> FVF (Forall repl (FUrename x51 repl x3a)) \<and> Inr repl \<notin> FVF (Forall repl (FUrename x51 repl x3a))
     ",auto simp add: Forall_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Forall_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Forall_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Box_def Forall_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Forall_def)  
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def Forall_def) 
                      done done
                    done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Forall_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def Forall_def) 
                      done done
                    done done 
                  done
then have FRAwhat:"FRadmit (Forall what p)" 
     and  FRAp:"FRadmit p" 
     and fsafewhat:"fsafe (Forall what p)"
     and  fvars:"{Inl repl, Inr repl, Inr what} \<inter> FVF (Forall what p) = {}"
  by auto
  have neq:"what \<noteq> repl"
    using some i L apply(auto simp add: some i L) by(cases "SG ! i",auto simp add: L Equiv_def Implies_def Or_def Forall_def)
  from FRAwhat   have FRArepl:"FRadmit (Forall repl (FUrename what  repl p))" using admits by auto 
  from  FRAp     have FRAprepl:"FRadmit (FUrename what repl p)" using brenameR_fadmitP_lem using admits by auto 
  from fsafewhat have fsaferepl:"fsafe (Forall repl (FUrename what repl p))" using admits by auto
  from fvars     have fvarsrepl:"{Inl what, Inr what, Inr repl} \<inter> FVF (Forall repl (FUrename what repl p)) = {}" 
    using admits by auto
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have brenameR_simp:"\<And>\<Gamma> \<Delta> p SS. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    \<Gamma> ! j = (Forall what p) \<Longrightarrow>
    what \<noteq> repl \<Longrightarrow>
  ( FRadmit((Forall what p)) \<and> FRadmit p \<and> fsafe (Forall what p) \<and>
     {Inl repl, Inr repl, Inr what} \<inter> FVF (Forall what p) = {})
\<and> FRadmit (Forall repl (FUrename what  repl p))
\<and> FRadmit (FUrename what repl p)
\<and> fsafe (Forall repl (FUrename what repl p))
\<and> {Inl what, Inr what, Inr repl} \<inter> FVF (Forall repl (FUrename what repl p)) = {} \<Longrightarrow>
    LeftRule_result (BRenameL what repl) j SS =
    Some [(replaceI \<Gamma> j (FBrename what repl (nth \<Gamma> j)),\<Delta>)]"
    subgoal for AI SI p  SS apply(cases SS) 
      by (auto simp add: Equiv_def Implies_def Or_def Box_def Forall_def)
    done
  have Gi:"\<Gamma> ! j = (Forall what p)" using SG_dec eq by (cases "SG ! i",auto)
  have res_eq:"LeftRule_result (BRenameL what repl) j (SG ! i) = 
    Some [(replaceI \<Gamma> j (FBrename what repl (nth \<Gamma> j)),\<Delta>)]"
    apply(rule brenameR_simp)
    subgoal using  SG_dec by (metis snd_conv) 
    using SG_dec  apply(cases "SG ! i",auto  simp add: FRAwhat FRAp fsafewhat fvars eq)
            apply(rule Gi)
    subgoal using neq by auto
          defer 
          apply(rule  FRAp)
         apply(rule fsafewhat)
    subgoal using fvars by auto
    subgoal using fvars by auto
    subgoal using fvars by auto
    using FRAwhat FRAp fsafewhat fvars FRArepl FRAprepl fsaferepl fvarsrepl by auto
  have rres:"rres = [(replaceI \<Gamma> j (FBrename what repl (nth \<Gamma> j)),\<Delta>)]"
    using res_eq SG_dec brenameR_simp some  i j L by auto
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  have jG:"j < length \<Gamma>" using \<Gamma> SG_dec j by auto
  have big_sound:"sound ([(replaceI \<Gamma> j (FBrename what repl (nth \<Gamma> j)),\<Delta>)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good_interp:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> 
    i < length [(replaceI \<Gamma> j (FBrename what repl (nth \<Gamma> j)),\<Delta>)] \<Longrightarrow> 
          \<nu> \<in> seq_sem I ([(replaceI \<Gamma> j (FBrename what repl (nth \<Gamma> j)),\<Delta>)] ! i))"
    have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
    from sgs have sg:"\<nu> \<in> seq_sem I (replaceI \<Gamma> j (FBrename what repl (nth \<Gamma> j)),\<Delta>)" by auto
    have sg1:"\<nu> \<in> seq_sem I ((FBrename what repl (nth \<Gamma> j)) # closeI \<Gamma> j, \<Delta>)"    
    proof(rule seq_semI')
      assume ante:"\<nu> \<in> fml_sem I (foldr (&&) ((FBrename what repl (nth \<Gamma> j)) # closeI \<Gamma> j) TT)"
      then have ante1:"\<nu> \<in> fml_sem I (foldr (&&) (replaceI \<Gamma> j (FBrename what repl (\<Gamma> ! j))) TT)" 
        using replaceI_closeI_conj_conv[of \<nu> I "(FBrename what repl (nth \<Gamma> j))" \<Gamma> j] jG
        by auto
      then have succ1:"\<nu> \<in> fml_sem I (foldr (||) ( \<Delta> ) FF)"
        using seq_MP[OF sg ante1]  by auto
      then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"  by auto
    qed
    have sgN:"\<nu> \<in> seq_sem I (\<Gamma>, \<Delta>)"    
    proof(rule seq_semI')
      assume ante:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
      then have con_sem:"\<nu> \<in> fml_sem I (foldr (&&) (nth \<Gamma> j # closeI  \<Gamma> j) TT)"
        using closeI_ident_conj[OF jG refl,of I] by auto
      then have canSem:"\<nu> \<in> fml_sem I (Forall what p)"
        using eq \<Gamma> SG_dec by auto
      have  moreEq:"(nth \<Gamma> j) = Forall what p"
        using eq SG_dec \<Gamma> by auto
      have renSem:"\<nu> \<in> fml_sem I (Forall repl (FUrename what repl p))"
        apply(rule BRename_forall_local_sound_neq[OF  FRAwhat  FRAp fsafewhat]) 
           apply(rule canSem) 
          apply(rule fvars) 
         apply(rule good_interp)
        by(rule neq)
      then have stuff:"\<nu> \<in> fml_sem I (FBrename what repl (Forall what p))"
        unfolding Forall_def by auto
      then have brenameSem:"\<nu> \<in> fml_sem I (FBrename what repl (nth \<Gamma> j))"
        using moreEq by auto
      then have ante1:"\<nu> \<in> fml_sem I (foldr (&&) (FBrename what repl (\<Gamma> ! j) # closeI \<Gamma> j) TT)"
        using  ante closeI_ident_conj[OF jG, of "\<Gamma> ! j", of I, OF refl]
        by auto
      then have succ1:"\<nu> \<in> fml_sem I (foldr (||) ( \<Delta> ) FF)"
        using seq_MP[OF sg1 ante1] by auto
      then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"  by auto
    qed
    show " \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      apply(rule seq_MP[OF sgN])
      using   ante eq \<Gamma>  by auto
  qed
    then show "sound (rres, SG ! i)"
      using some SG_dec rres by auto
  qed

  have box_case:"(\<exists> t p.(fst (SG ! i) ! j) =  ([[what := t]]p)) \<Longrightarrow> ?thesis"
  proof -
    assume "(\<exists> t p.(fst (SG ! i) ! j) =  ([[what := t]]p))"
    then obtain t p where eq:"(fst (SG ! i) ! j) = ([[what := t]]p)" by(auto)
          have admits:
             "TRadmit t \<and>  FRadmit ([[what := t]]p) \<and> FRadmit p \<and> fsafe ([[what := t]]p) \<and>
                 {Inl repl, Inr repl, Inr what} \<inter> FVF ([[what := t]]p) = {} \<and>
FRadmit ([[repl := t]]FUrename what  repl p) \<and>
FRadmit (FUrename what repl p) \<and>
fsafe ([[repl := t]]FUrename what repl p) \<and>
{Inl what, Inr what, Inr repl} \<inter> FVF ([[repl := t]]FUrename what repl p) = {}"
            using some i L  apply(cases "SG ! i", auto simp add: L Equiv_def Implies_def Or_def some i)apply(cases "what = repl",auto)
            subgoal for a b
              apply(cases "a ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62,auto) subgoal for x3a using eq by(auto simp add: Box_def eq) done 
                subgoal for x61 x62 apply(cases x62,auto) subgoal for x3a using eq by(auto simp add: Box_def eq)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x3a using eq apply(auto simp add: Box_def eq)by(cases "TRadmit t \<and>
        FRadmit p \<and>
        dsafe t \<and> fsafe p \<and> Inl repl \<notin> FVT t \<and> Inl repl \<notin> FVF p \<and> Inr repl \<notin> FVT t \<and> Inr repl \<notin> FVF p \<and> Inr what \<notin> FVT t \<and> Inr what \<notin> FVF p",auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              done done done

                subgoal for a b
                  apply(cases "what = repl",auto)
              apply(cases "a ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21  using eq apply(cases x62,auto) 
                    by(cases "what = x61 \<and>
        FRadmit (Forall x61 x21) \<and>
        FRadmit x21 \<and> fsafe (Forall x61 x21) \<and> Inl repl \<notin> FVF (Forall x61 x21) \<and> Inr repl \<notin> FVF (Forall x61 x21) \<and> Inr what \<notin> FVF (Forall x61 x21)",auto simp add: Box_def)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  done
                subgoal for a b
                 apply(cases "what = repl",auto)
              apply(cases "a",auto) apply(cases "b",auto simp add: Box_def)
                  subgoal for x21 x22 x3
                    apply(cases "what = x21 \<and> TRadmit x22 \<and> FRadmit x3 \<and> dsafe x22 \<and> fsafe x3 \<and> Inl repl \<notin> FVT x22 \<and> (Inl repl \<in> FVF x3 \<longrightarrow> repl = x21) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF x3 \<and> Inr what \<notin> FVT x22 \<and> Inr what \<notin> FVF x3")
                    subgoal  using eq by(auto simp add: Box_def)
                    subgoal  using eq by(auto simp add: Box_def) done

                  subgoal for x21 x22 x3
                    apply(cases "what = x21 \<and> TRadmit x22 \<and>  FRadmit x3 \<and> dsafe x22 \<and> fsafe x3 \<and> Inl repl \<notin> FVT x22 \<and> (Inl repl \<in> FVF x3 \<longrightarrow> repl = x21) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF x3 \<and> Inr what \<notin> FVT x22 \<and> Inr what \<notin> FVF x3")
                    subgoal  using eq by(auto simp add: Box_def)
                    subgoal  using eq by(auto simp add: Box_def) done
                  done done done
                subgoal for a b
                  apply(cases "what = repl",auto, cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Box_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Box_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Box_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Box_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done
                    done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done
                    done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done
                    done done 
                      apply(cases "what = repl",auto)
            subgoal for a b
              apply(cases "a ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62,auto) subgoal for x3a using eq by(auto simp add: Box_def eq) done 
                subgoal for x61 x62 apply(cases x62,auto) subgoal for x3a using eq by(auto simp add: Box_def eq)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x3a using eq by(auto simp add: Box_def eq)
              subgoal for x41 x42
                apply(cases x61,auto)
                done
              subgoal for x51 x52 by(cases x61,auto)
              subgoal for x61a x62a apply(cases x61a,auto) subgoal for x1 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x3a apply(cases x61,auto) done
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21  by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 by(cases x61,auto)

              done 

            subgoal for x71 x72 apply(cases x61,auto) done done done done
                subgoal for a b
                  apply(cases "what = repl",auto)
              apply(cases "a ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21  using eq apply(cases x62,auto) 
                    by(cases "what = x61 \<and>
        FRadmit (Forall x61 x21) \<and>
        FRadmit x21 \<and> fsafe (Forall x61 x21) \<and> Inl repl \<notin> FVF (Forall x61 x21) \<and> Inr repl \<notin> FVF (Forall x61 x21) \<and> Inr what \<notin> FVF (Forall x61 x21)",auto simp add: Box_def)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  done
                subgoal for a b
                 apply(cases "what = repl",auto)
              apply(cases "a",auto) apply(cases "b",auto simp add: Box_def)
                  subgoal for x21 x22 x3
                    apply(cases "what = x21 \<and>
        TRadmit x22 \<and>
        FRadmit x3 \<and>
        dsafe x22 \<and>
        fsafe x3 \<and>
        Inl repl \<notin> FVT x22 \<and>
        (Inl repl \<in> FVF x3 \<longrightarrow> repl = x21) \<and>
        Inr repl \<notin> FVT x22 \<and>
        Inr repl \<notin> FVF x3 \<and>
        Inr what \<notin> FVT x22 \<and>
        Inr what \<notin> FVF x3 \<and>
        TRadmit x22 \<and>
        FRadmit (FUrename x21 repl x3) \<and>
        dsafe x22 \<and>
        fsafe (FUrename x21 repl x3) \<and>
        Inl x21 \<notin> FVT x22 \<and>
        (Inl x21 \<in> FVF (FUrename x21 repl x3) \<longrightarrow> x21 = repl) \<and>
        Inr x21 \<notin> FVT x22 \<and> Inr x21 \<notin> FVF (FUrename x21 repl x3) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF (FUrename x21 repl x3)")
                    subgoal  using eq by(auto simp add: Box_def)
                    subgoal  using eq by(auto simp add: Box_def) done done done done
                subgoal for a b
                  apply(cases "what = repl",auto, cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Box_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or>
         (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and>
        Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and>
        Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and>
        Inr what \<notin> FVF ([[x51 := x52]]x3a) \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[repl := x52]]FUrename x51 repl x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[repl := x52]]FUrename x51 repl x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[repl := x52]]FUrename x51 repl x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[repl := x52]]FUrename x51 repl x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[repl := x52]]FUrename x51 repl x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or>
         (\<exists>\<alpha> \<phi>. ([[repl := x52]]FUrename x51 repl x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit (FUrename x51 repl x3a) \<and>
        fsafe ([[repl := x52]]FUrename x51 repl x3a) \<and>
        Inl x51 \<notin> FVF ([[repl := x52]]FUrename x51 repl x3a) \<and>
        Inr x51 \<notin> FVF ([[repl := x52]]FUrename x51 repl x3a) \<and> Inr repl \<notin> FVF ([[repl := x52]]FUrename x51 repl x3a)",auto simp add: Box_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Box_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Box_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done
                    done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "a ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done
                    done done done
then have TRA:"TRadmit t" 
     and  FRAwhat:"FRadmit ([[what := t]]p)" 
     and  FRAp:"FRadmit p" 
     and fsafewhat:"fsafe ([[what := t]]p)"
     and  fvars:"{Inl repl, Inr repl, Inr what} \<inter> FVF ([[what := t]]p) = {}"
  by auto
  have neq:"what \<noteq> repl"
    using some i L apply(auto simp add: some i L) by(cases "SG ! i",auto simp add: L Equiv_def Implies_def Or_def)
  from FRAwhat   have FRArepl:"FRadmit ([[repl := t]]FUrename what  repl p)"  using admits by auto
  from  FRAp     have FRAprepl:"FRadmit (FUrename what repl p)" using admits by auto
  from fsafewhat have fsaferepl:"fsafe ([[repl := t]]FUrename what repl p)" using admits by auto
  from fvars     have fvarsrepl:"{Inl what, Inr what, Inr repl} \<inter> FVF ([[repl := t]]FUrename what repl p) = {}" 
    using admits by auto
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have brenameR_simp:"\<And>\<Gamma> \<Delta> SS. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow>  \<^cancel>\<open> \<theta> p \<close>
    \<Gamma> ! j = ([[Assign what t]]p) \<Longrightarrow>
    what \<noteq> repl \<Longrightarrow>
  (TRadmit t \<and>  FRadmit([[Assign what t]]p) \<and> FRadmit p \<and> fsafe ([[Assign what t]]p) \<and>
     {Inl repl, Inr repl, Inr what} \<inter> FVF ([[Assign what t]]p) = {}
\<and> FRadmit ([[repl := t]]FUrename what  repl p)
\<and> FRadmit (FUrename what repl p)
\<and> fsafe ([[repl := t]]FUrename what repl p)
\<and> {Inl what, Inr what, Inr repl} \<inter> FVF ([[repl := t]]FUrename what repl p) = {}
) \<Longrightarrow>
    LeftRule_result (BRenameL what repl) j SS =
    Some [(replaceI \<Gamma> j (FBrename what repl (nth \<Gamma> j)),\<Delta>)]"
    subgoal for AI SI (*p q*) SS apply(cases SS) 
      by (auto simp add: Equiv_def Implies_def Or_def Box_def)
    done
  have Gi:"\<Gamma> ! j = ([[what := t]]p)" using SG_dec eq by (cases "SG ! i",auto)
  have res_eq:"LeftRule_result (BRenameL what repl) j (SG ! i) = 
    Some [(replaceI \<Gamma> j (FBrename what repl (nth \<Gamma> j)),\<Delta>)]"
    apply(rule brenameR_simp)
    subgoal using  SG_dec by (metis snd_conv) 
    using SG_dec  apply(cases "SG ! i",auto  simp add: TRA FRAwhat FRAp fsafewhat fvars eq)
            apply(rule Gi)
    subgoal using neq by auto
          defer defer
          apply(rule  FRAprepl)
         apply(rule fsaferepl)
    subgoal using fvarsrepl by auto
    subgoal using fvarsrepl by auto
    subgoal using fvarsrepl by auto
    apply(erule allE[where x=t])
    apply(erule allE[where x="Diamond (Assign what  t) (Not p)"])
    apply(erule allE)
    apply(erule allE[where x=p])
    apply(erule allE[where x="Assign what t"])
    apply(auto simp add: Box_def)
    using TRA FRAwhat FRAp fsafewhat fvars FRArepl FRAprepl fsaferepl fsaferepl
    by (auto simp add: TRA FRAwhat FRAp fsafewhat fvars FRArepl FRAprepl fsaferepl fvarsrepl)
  have rres:"rres = [( replaceI \<Gamma> j (FBrename what repl (nth \<Gamma> j)),\<Delta>)]" 
    using res_eq SG_dec brenameR_simp some  i j L by auto
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  have jD:"j < length \<Gamma>" using \<Gamma> SG_dec j by auto
  have big_sound:"sound ([(replaceI \<Gamma> j (FBrename what repl (nth \<Gamma> j)),\<Delta>)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good_interp:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> 
    i < length [(replaceI \<Gamma> j (FBrename what repl (\<Gamma> ! j)),\<Delta>)] \<Longrightarrow> 
          \<nu> \<in> seq_sem I ([(replaceI \<Gamma> j (FBrename what repl (\<Gamma> ! j)),\<Delta>)] ! i))"
    have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
    from sgs have sg:"\<nu> \<in> seq_sem I (replaceI \<Gamma> j (FBrename what repl (\<Gamma> ! j)),\<Delta>)" by auto
    then have sg1:"\<nu> \<in> seq_sem I ((FBrename what repl (nth \<Gamma> j)) # closeI \<Gamma> j ,\<Delta>)"
      using replaceI_closeI_conj_conv[of \<nu> I   "(FBrename what repl (nth \<Gamma> j))" \<Gamma> j] jD 
      by auto
    have sgN:"\<nu> \<in> seq_sem I (\<Gamma>, \<Delta>)"    
    proof(rule seq_semI')
      assume ante:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
      then have ante1:"\<nu> \<in> fml_sem I (foldr (&&) (nth \<Gamma> j # closeI  \<Gamma> j) TT)"
        using closeI_ident_conj[OF jD refl,of I] by auto
      then have fSem:"\<nu> \<in> fml_sem I (nth \<Gamma> j)" by auto
      have someEq:"(nth \<Gamma> j) = ([[what := t]]p)" using eq \<Delta> SG_dec by (auto,cases "SG ! i",auto)
      from fSem have fSem:"\<nu> \<in> fml_sem I ([[what := t]]p)" 
        using someEq by auto
      then have renSem:"\<nu> \<in> fml_sem I (FBrename what repl ([[what := t]]p))"
        using BRename_local_sound_neq[OF TRA FRAwhat  FRAp fsafewhat fSem fvars good_interp neq]  by (auto simp add: Box_def)
      then have rIsem:"\<nu> \<in> fml_sem I (FBrename what repl (nth \<Gamma> j))" using someEq by auto
      then have ante1:"\<nu> \<in> fml_sem I (foldr (&&) ((FBrename what repl (nth \<Gamma> j)) # closeI \<Gamma> j) TT)"
        using ante1   by auto
      then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" 
        using seq_MP[OF sg1]  by auto
    qed
    show " \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      apply(rule seq_MP[OF sgN])
      using   ante eq \<Gamma>  by auto
  qed
  then show ?thesis using some SG_dec rres by auto
qed
  show " sound (rres, SG ! i)" using box_case all_case exist some   by(auto) 
next 
  case OrL  then have L:"L = OrL" by auto
  obtain p q where eq:"fst (SG ! i) ! j = (p || q)"
    using some i L apply(auto simp add: some i L) apply(cases "SG ! i",auto simp add: L  Or_def)
    apply(cases "(SG ! i)",auto simp add: Or_def)
    subgoal for a b apply(cases "a ! j", auto) subgoal for x3 apply(cases x3,auto) subgoal for x41 x42 by(cases x41,auto,cases x42,auto)
    done done done
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  from \<Gamma> have jG:"j < length \<Gamma>" using SG_dec j by auto
  have AIjeq:"\<Gamma> ! j = (p || q)" 
    using SG_dec eq fst_conv
    by metis
  have rres:"rres = [(replaceI \<Gamma> j p, \<Delta>), (replaceI \<Gamma> j q, \<Delta>)]"
    using some L AIjeq apply(cases "SG ! i",auto)
    subgoal for a b
      using some L AIjeq  \<Gamma> \<Delta> 
      by(cases "a ! j",auto simp add: \<Gamma> \<Delta> Or_def) done
  have res_eq:"LeftRule_result OrL j (\<Gamma>,\<Delta>) = Some [(replaceI \<Gamma> j p, \<Delta>), (replaceI \<Gamma> j q, \<Delta>)]"
    using rres some AIjeq by (auto simp add: Or_def)
  have big_sound:"sound ([(replaceI \<Gamma> j p, \<Delta>), (replaceI \<Gamma> j q, \<Delta>)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I::"interp" and \<nu>
    assume good:"is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow>
             i < length [(replaceI \<Gamma> j p, \<Delta>), (replaceI \<Gamma> j q, \<Delta>)] \<Longrightarrow>
             \<nu> \<in> seq_sem I (nth [(replaceI \<Gamma> j p, \<Delta>), (replaceI \<Gamma> j q, \<Delta>)] i))"
    assume \<Gamma>_sem:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    have sg1:"\<nu> \<in> seq_sem I (replaceI \<Gamma> j p, \<Delta>)" using sgs[of 0] by auto
    have sg2:"\<nu> \<in> seq_sem I (replaceI \<Gamma> j q, \<Delta>)" using sgs[of 1] by auto
    from \<Gamma>_sem have ante1:"\<nu> \<in> fml_sem I (foldr (&&) ((nth \<Gamma> j) # (closeI \<Gamma> j)) TT)"
      using closeI_ident_conj[OF jG , of "\<Gamma> ! j", of I, OF refl ] by auto
    then have ante2:"\<nu> \<in> fml_sem I (foldr (&&) ((p || q) # (closeI \<Gamma> j)) TT)"
      using AIjeq by auto
    then have ante_disj:" (\<nu> \<in> fml_sem I (foldr (&&) (p # (closeI \<Gamma> j)) TT))
\<or> (\<nu> \<in> fml_sem I (foldr (&&) (q # (closeI \<Gamma> j)) TT))"
      by(auto)
    show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      apply(rule disjE[OF ante_disj])
       apply(rule seq_MP[OF sg1])
            subgoal using replaceI_closeI_conj_conv[of \<nu> I "p" \<Gamma> j] seq_MP[OF sg1] jG by auto
            subgoal using replaceI_closeI_conj_conv[of \<nu> I "q" \<Gamma> j] seq_MP[OF sg2] jG by auto
            done
  qed
  show "sound (rres, nth SG i)" 
    using rres SG_dec big_sound by(auto)
next
  case FalseL then have L:"L = FalseL" by auto
  have eq:"nth (fst (nth SG  i)) j = FF"
    using some L by(cases " \<^cancel>\<open>snd \<close>(SG ! i)\<^cancel>\<open> ! j\<close>")
      (auto simp add: L FF_def split: if_splits)
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  from \<Gamma> have jD:"j < length \<Gamma>" using SG_dec j by auto
  have AIjeq:"\<Gamma> ! j = (FF)"
    using SG_dec eq fst_conv
    by metis
  have rres:"rres = []"
    using some L AIjeq apply(cases "SG ! i",auto)
    subgoal for a b
      using some L AIjeq  \<Gamma> \<Delta> eq by(cases "a ! j",auto simp add: \<Gamma> \<Delta> eq) done
  have big_sound:"sound ([], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I::"interp" and \<nu>
    assume good:"is_interp I"
    assume ante:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    then have "\<nu> \<in> fml_sem I (foldr (&&) (FF # closeI \<Gamma> j) TT)"  
      using closeI_ident_conj[OF jD AIjeq, of I] 
       by auto
    then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta>  FF)"
      using closeI_ident_disj[OF jD AIjeq, of I] by auto
  qed
  then show ?thesis using rres SG_dec big_sound by(auto)    

qed

lemma rrule_sound: 
  assumes some:"(RightRule_result L j (nth SG i)) = Some rres"
  assumes i:"i < length SG"
  assumes j:"j < length (snd (nth SG  i))"
  assumes sound:"sound (SG,C)"
  shows "sound (rres, nth SG i)"
proof(cases L)
case ImplyR then have L:"L = ImplyR" by auto
  obtain p q where eq:"snd (SG ! i) ! j = (Implies p q)"
    using some L 
    apply(cases "(SG ! i)") apply(auto simp add: Implies_def Or_def)
    subgoal for a b
      apply(cases "b ! j", auto) subgoal for x3 apply(cases x3, auto)
        subgoal for x41 x42
        apply(cases "x41",auto) subgoal for x3a apply(cases x42,auto) subgoal for x4 by(cases x4,auto) done done done done done
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  then have jD:"j < length \<Delta>" using SG_dec j by auto
  have AIjeq:"\<Delta> ! j = (p \<rightarrow> q)" 
    using SG_dec eq snd_conv
    by metis
  have rres:"rres = [(\<Gamma> @ [p], (closeI \<Delta> j) @ [q])]"
    using some L AIjeq eq apply(cases "SG ! i",auto)
    subgoal for a b
      using some L AIjeq  \<Gamma> \<Delta> apply(cases "b ! j",auto simp add: \<Gamma> \<Delta>) by(auto simp add: Implies_def Or_def) done
  have res_eq:"RightRule_result ImplyR j (\<Gamma>,\<Delta>) = Some [(\<Gamma> @ [p], (closeI \<Delta> j) @ [q])]"
    using rres some AIjeq eq by (auto simp add: Implies_def Or_def)
  have big_sound:"sound ([(\<Gamma> @ [p], (closeI \<Delta> j) @ [q])], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume "is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(\<Gamma> @ [p], closeI \<Delta> j @ [q])] \<Longrightarrow> \<nu> \<in> seq_sem I ([(\<Gamma> @ [p], closeI \<Delta> j @ [q])] ! i))"
      have sg:"\<nu> \<in> seq_sem I (\<Gamma> @ [p], closeI \<Delta> j @ [q] )" using sgs[of 0] by auto
    assume \<Gamma>_sem:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    have assocced:"\<nu> \<in> seq_sem I (p # \<Gamma>, q # closeI \<Delta> j )"     
      using sg snoc_assoc_sequent[of I p \<Gamma> q "closeI \<Delta> j"] 
      by auto
    show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      apply(cases "\<nu> \<in> fml_sem I p")
      subgoal 
      proof -
        have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
        assume imp:"\<nu> \<in> fml_sem I p"
        then have ante:"\<nu> \<in> fml_sem I (foldr (&&) (p  # \<Gamma>) TT)" using \<Gamma>_sem by auto
        then have succ:"\<nu> \<in> fml_sem I (foldr (||) ((p \<rightarrow> q) # closeI \<Delta> j) FF)" 
          using imp seq_MP[OF assocced] AIjeq by auto
        then have almost:"\<nu> \<in> fml_sem I (foldr (||) ((p \<rightarrow> q) # closeI \<Delta> j) FF)" 
          using imp seq_MP[OF assocced] AIjeq by auto
        show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
          apply(rule duh[of \<nu> "fml_sem I (foldr (||) ((p \<rightarrow> q) # closeI \<Delta> j) FF)"])
          apply(rule almost)
          by(rule closeI_ident_disj[of j \<Delta> "p \<rightarrow> q" I, OF jD AIjeq])
      qed
      proof -
        have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
        assume imp:"\<nu> \<notin> fml_sem I p"
        then have ante:"\<nu> \<in> fml_sem I (p \<rightarrow> q)" using \<Gamma>_sem by auto
        then have succ:"\<nu> \<in> fml_sem I (foldr (||) ((p \<rightarrow> q) # closeI \<Delta> j) FF)" 
          using imp seq_MP[OF assocced] AIjeq by auto
        then have almost:"\<nu> \<in> fml_sem I (foldr (||) ((p \<rightarrow> q) # closeI \<Delta> j) FF)" 
          using imp seq_MP[OF assocced] AIjeq by auto
        show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
(*         have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto*)
          apply(rule duh[of \<nu> "fml_sem I (foldr (||) ((p \<rightarrow> q) # closeI \<Delta> j) FF)"])
          apply(rule almost)
          by(rule closeI_ident_disj[of j \<Delta> "p \<rightarrow> q" I, OF jD AIjeq])
      qed
    qed
  show "sound (rres, nth SG i)" 
    using rres SG_dec big_sound by(auto)
next
  case AndR  then have L:"L = AndR" by auto
  obtain p q where eq:"snd (SG ! i) ! j = (p && q)"
    using some L apply(cases " snd (SG ! i) ! j", auto simp add: L)
    by(cases "(SG ! i)",auto)+
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  then have jD:"j < length \<Delta>" using SG_dec j by auto
  have AIjeq:"\<Delta> ! j = (p && q)" 
    using SG_dec eq snd_conv
    by metis
  have rres:"rres = [(\<Gamma>, replaceI \<Delta> j p), (\<Gamma>, replaceI \<Delta> j q)]"
    using some L AIjeq apply(cases "SG ! i",auto)
    subgoal for a b
      using some L AIjeq  \<Gamma> \<Delta> by(cases "b ! j",auto simp add: \<Gamma> \<Delta>) done
  have res_eq:"RightRule_result AndR j (\<Gamma>,\<Delta>) = Some [(\<Gamma>, replaceI \<Delta> j p), (\<Gamma>, replaceI \<Delta> j q)]"
    using rres some AIjeq by auto
  have big_sound:"sound ([(\<Gamma>, replaceI \<Delta> j p), (\<Gamma>, replaceI \<Delta> j q)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I::"interp" and \<nu>
    assume good:"is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow>
             i < length [(\<Gamma>, replaceI \<Delta> j p), (\<Gamma>, replaceI \<Delta> j q)] \<Longrightarrow>
             \<nu> \<in> seq_sem I (nth [(\<Gamma>, replaceI \<Delta> j p), (\<Gamma>,replaceI \<Delta> j q)] i))"
    assume \<Gamma>_sem:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    have sg1:"\<nu> \<in> seq_sem I (\<Gamma>, replaceI \<Delta> j p)" using sgs[of 0] by auto
    have sg2:"\<nu> \<in> seq_sem I (\<Gamma>, replaceI \<Delta> j q)" using sgs[of 1] by auto
    have "\<nu> \<in> fml_sem I (foldr (||) (replaceI \<Delta> j p) FF)"  by(rule seq_MP[OF sg1 \<Gamma>_sem])
    then have  \<Delta>1:"\<nu> \<in> fml_sem I (foldr (||) (p # closeI \<Delta> j) FF)" using replaceI_assoc_disj[OF jD, of I p] by auto
    have "\<nu> \<in> fml_sem I (foldr (||) (replaceI \<Delta> j q) FF)"  by(rule seq_MP[OF sg2 \<Gamma>_sem])
    then have  \<Delta>2:"\<nu> \<in> fml_sem I (foldr (||) (q # closeI \<Delta> j) FF)" using replaceI_assoc_disj[OF jD, of I q] by auto
    have \<Delta>':"\<nu> \<in> fml_sem I (foldr (||) (replaceI \<Delta> j (p && q)) FF)" using \<Delta>1 \<Delta>2 replaceI_assoc_disj[OF jD, of I "p && q"] by auto
    then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" 
    using replaceI_ident[OF j eq] \<Delta> by auto
  qed
  show "sound (rres, nth SG i)" 
    using rres SG_dec big_sound by(auto)
next
  case CohideRR  then have L:"L = CohideRR" by auto
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have cohideRR_simp:"\<And>\<Gamma> \<Delta> SS p q. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    RightRule_result CohideRR j SS = Some [([], [nth \<Delta> j])]"
    subgoal for AI SI SS p q by(cases SS, auto) done
  have res_eq:"RightRule_result CohideRR j (SG ! i) =  Some [([], [nth \<Delta> j])]"
    using SG_dec cohideRR_simp by auto
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  then have jD:"j < length \<Delta>" using SG_dec j by auto
  have rres:"rres = [([], [nth \<Delta> j])]"
    using some L  apply(cases "SG ! i",auto)
    subgoal for a b
      using some L \<Delta> apply(cases "b ! j",auto simp add:  \<Delta>) done done
  have big_sound:"sound ([([], [nth \<Delta> j])], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I \<nu>
    assume pres:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [([], [\<Delta> ! j])] \<Longrightarrow> \<nu> \<in> seq_sem I ([([], [\<Delta> ! j])] ! i))"
    then have pre:"\<nu> \<in> seq_sem I ([], [nth \<Delta> j])" by auto
    then have fsem:"\<nu> \<in> fml_sem I (nth \<Delta> j)" by auto
    then have "\<nu> \<in> fml_sem I (foldr (||) ((nth \<Delta> j) # closeI \<Delta> j) FF)"
      by auto
    then show " \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using closeI_ident_disj[OF jD , of "\<Delta> ! j", of I, OF refl] by auto
  qed
  show "sound (rres, nth SG i)" 
    using SG_dec big_sound rres by(auto)
next
  case TrueR then have L:"L = TrueR" by auto
  have eq:"nth (snd (nth SG  i)) j = TT"
    using some L apply(cases " \<^cancel>\<open>snd \<close>(SG ! i)\<^cancel>\<open> ! j\<close>")
    apply (auto simp add: L)
    subgoal for a b
      apply(cases "b ! j", auto split: trm.splits if_splits)
      by (metis Rep_bword_inverse TT_def Zero_def bword_zero_def)
    done
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  then have jD:"j < length \<Delta>" using SG_dec j by auto
  have AIjeq:"\<Delta> ! j = (TT)"
    using SG_dec eq snd_conv
    by metis
  have rres:"rres = []"
    using some L AIjeq apply(cases "SG ! i",auto)
    subgoal for a b
      using some L AIjeq  \<Gamma> \<Delta> eq apply(cases "b ! j",auto simp add: \<Gamma> \<Delta> eq)
      subgoal for x11 x12 
        apply(cases x11, auto) subgoal for x2
          apply(cases x12, auto) subgoal for x2a
            apply(cases "x2 = x2a \<and> Rep_bword x2 = 0")
            apply(auto simp add: bword_zero_def Rep_bword_inverse)
        done done done done done
  have big_sound:"sound ([], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I::" interp" and \<nu>
    assume good:"is_interp I"
    have "\<nu> \<in> fml_sem I (foldr (||) (TT # closeI \<Delta> j) FF)"  by(auto simp add: TT_def)
    then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta>  FF)"
      using closeI_ident_disj[OF jD AIjeq, of I] by auto
  qed
  then show ?thesis using rres SG_dec big_sound by(auto)    
next
  case EquivR then have L:"L = EquivR" by auto
  have exist:"\<exists> p q.(snd (SG ! i) ! j) =  Equiv p q"
    using some i L apply(auto simp add: some i L) apply(cases "SG ! i",auto simp add: L Equiv_def Implies_def Or_def)
    subgoal for a b
      apply(cases "b ! j",auto)
      subgoal for x3 apply(cases x3,auto)
        subgoal for x41 x42 apply(cases x41,auto, cases x42, auto)
          subgoal for x3a x11 x12
            by(cases x3a,auto)
          subgoal for x3a x11 x12
            by(cases x3a,auto)
          subgoal for x3a x11 
            apply(cases x3a,auto,cases x11,auto)
            subgoal for x41a x42a x41aa x42aa
              apply(cases "x41aa",auto, cases x42aa,auto)
              subgoal for x3b x3aa
                by(cases "x41a = x3b \<and> x42a = x3aa",auto) done
            subgoal for x41a x42a x41aa x42aa
              apply(cases "x41aa",auto, cases x42aa,auto)
              subgoal for x3b x3aa
                by(cases "x41a = x3b \<and> x42a = x3aa",auto) done done
          subgoal for x3a x41a x42a
            by(cases x3a,auto)
          subgoal for x3a x51 x52
            by(cases x3a,auto)
          subgoal for x3a x61 x62
            by(cases x3a,auto)
          subgoal for x3a x71 x72
            by(cases x3a,auto) done done done done
  then obtain p q where eq:"(snd (SG ! i) ! j) = (p \<leftrightarrow> q)" by auto
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have equivR_simp:"\<And>\<Gamma> \<Delta> SS p q. 
    (nth \<Delta> j) = Equiv p q \<Longrightarrow> 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    RightRule_result EquivR j SS = Some [( \<Gamma> @ [p],  (closeI \<Delta> j) @ [q]), ( \<Gamma> @ [q], (closeI \<Delta> j) @ [p])]"
    subgoal for AI SI SS p q apply(cases SS) by (auto simp add: Equiv_def Implies_def Or_def) done
  have res_eq:"RightRule_result EquivR j (SG ! i) = 
    Some [( \<Gamma> @ [p], (closeI \<Delta> j) @ [q]), (\<Gamma> @ [q], (closeI \<Delta> j) @ [p])]"
    apply(rule equivR_simp)
    subgoal using eq SG_dec by (metis snd_conv)
    by (rule SG_dec) 
  have rres:"rres = [( \<Gamma> @ [p], (closeI \<Delta> j) @ [q]), (\<Gamma> @ [q], (closeI \<Delta> j) @ [p])]" 
    using res_eq SG_dec equivR_simp eq some  i j L by auto
  have AIjeq:"\<Delta> ! j = (p \<leftrightarrow> q)" 
    using SG_dec eq snd_conv
    by metis
  have big_sound:"sound ([(\<Gamma> @ [p],  (closeI \<Delta> j) @ [q]), (\<Gamma> @ [q], (closeI \<Delta> j) @ [p])], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(\<Gamma> @ [p], (closeI \<Delta> j) @ [q]), (\<Gamma> @ [q], (closeI \<Delta> j) @ [p])] \<Longrightarrow> \<nu> \<in> seq_sem I ([(\<Gamma> @ [p], (closeI \<Delta> j) @ [q]), (\<Gamma> @ [q], (closeI \<Delta> j) @ [p])] ! i))"
         have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
    have "\<nu> \<in> seq_sem I (\<Gamma> @ [p], closeI \<Delta> j @ [q])" using sgs[of 0] by auto
    then have sg1:"\<nu> \<in> seq_sem I (p # \<Gamma>, q # closeI \<Delta> j)"
      apply(rule duh[of \<nu> "seq_sem I (\<Gamma> @ [p], closeI \<Delta> j @ [q])" "seq_sem I (p # \<Gamma>, q # closeI \<Delta> j)"]) 
      by(rule HOL.sym[OF snoc_assoc_sequent[of I p \<Gamma> q "closeI \<Delta> j"]])
    have "\<nu> \<in> seq_sem I (\<Gamma> @ [q], closeI \<Delta> j @ [p])" using sgs[of 1] by auto
    then have sg2:"\<nu> \<in> seq_sem I (q # \<Gamma>, p # closeI \<Delta> j)"
      apply(rule duh[of \<nu> "seq_sem I (\<Gamma> @ [q], closeI \<Delta> j @ [p])" "seq_sem I (q # \<Gamma>, p # closeI \<Delta> j)"]) 
      by(rule HOL.sym[OF snoc_assoc_sequent[of I q \<Gamma> p "closeI \<Delta> j"]])
    assume \<Gamma>_sem:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    have case1:"\<nu> \<in> fml_sem I p \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
    proof -
      assume sem:"\<nu> \<in> fml_sem I p"
      have "\<nu> \<in> fml_sem I (foldr (||) (q # (closeI \<Delta> j)) FF)"
        using sem \<Gamma>_sem sg1 
        by(auto)
 
      then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
        using AIjeq SG_dec closeI_sub[of  j \<Delta>] iff_sem[of "\<nu>" I p q] j sublist_def
        member_rec(1)[of q "closeI \<Delta> j"] sem snd_conv
        or_foldl_sem_conv[of \<nu> I "q # closeI \<Delta>  j"]
        or_foldl_sem[of "\<Delta>", where I=I and \<nu>=\<nu>]
        nth_member[of j "snd (SG ! i)"]
        by metis
    qed
    have case2:"\<nu> \<notin> fml_sem I p \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
    proof -
      assume sem:"\<nu> \<notin> fml_sem I p"
      have "\<nu> \<in> fml_sem I q \<Longrightarrow>  \<nu> \<notin> fml_sem I (foldr (||) \<Delta> FF) \<Longrightarrow> False"
        using  
          and_foldl_sem[OF \<Gamma>_sem]
          and_foldl_sem_conv
          closeI.simps
          sublist_def
          member_rec(1)[of "p" "closeI \<Delta> j"]
          member_rec(1)[of "q" "\<Gamma>"]
          or_foldl_sem[of "\<Delta>"]
          or_foldl_sem_conv[of \<nu>  I "p # closeI \<Delta> j"]
          sem
          sg2
          seq_MP[of \<nu> I "q # \<Gamma>" "p # closeI \<Delta> j", OF sg2]
      proof -
        assume a1: "\<nu> \<in> fml_sem I q"
        assume a2: "\<nu> \<notin> fml_sem I (foldr (||) \<Delta> FF)"
        have blub:" sublist (closeI \<Delta> j) \<Delta>" using closeI_sub[OF j] SG_dec by(cases "SG ! i",auto) 
        obtain ff :: "formula" where
          "\<nu> \<in> fml_sem I ff \<and> List.member (p # closeI \<Delta> j) ff"
          using a1 by (metis (no_types) \<open>\<And>\<phi>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>\<close> \<open>\<And>y. List.member (q # \<Gamma>) y = (q = y \<or> List.member \<Gamma> y)\<close> \<open>\<nu> \<in> fml_sem I (foldr (&&) (q # \<Gamma>) TT) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) (p # closeI \<Delta> j) FF)\<close> \<open>\<nu> \<in> fml_sem I (foldr (||) (p # closeI \<Delta> j) FF) \<Longrightarrow> \<exists>\<phi>. \<nu> \<in> fml_sem I \<phi> \<and> List.member (p # closeI \<Delta> j) \<phi>\<close> and_foldl_sem_conv closeI.simps)
        then show ?thesis
          using blub a2 by (metis (no_types) \<open>\<And>\<phi> \<nu> I. \<lbrakk>List.member \<Delta> \<phi>; \<nu> \<in> fml_sem I \<phi>\<rbrakk> \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)\<close> \<open>\<And>y. List.member (p # closeI \<Delta> j) y = (p = y \<or> List.member (closeI \<Delta> j) y)\<close> closeI.simps  sublist_def sem )
      qed
      show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
        by (metis AIjeq SG_dec \<open>\<lbrakk>\<nu> \<in> fml_sem I q; \<nu> \<notin> fml_sem I (foldr (||) \<Delta> FF)\<rbrakk> \<Longrightarrow> False\<close> iff_sem j nth_member or_foldl_sem sem snd_eqD)
    qed
    show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      by(cases "\<nu> \<in> fml_sem I p", (simp add: case1 case2)+)
  qed
  then show ?thesis using rres SG_dec big_sound by(auto)
next
  case Skolem then have L:"L = Skolem" by auto
  obtain x p where eq:"(snd (SG ! i) ! j) = (Forall x p)"      
    using some i L apply(auto simp add: some i L) apply(cases "SG ! i",auto simp add: L Forall_def)
    subgoal for a b apply(cases "b ! j", auto) subgoal for x3 apply(cases "x3", auto) subgoal for x51 x52 by(cases "x52",auto) done done done
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have jD:"j < length \<Delta>" using j SG_dec by(cases "SG ! i",auto)
  have fvseq:"(Inl x \<notin> FVSeq (\<Gamma>,\<Delta>))"
   and fsafe1:"fsafe (foldr (&&) \<Gamma> TT)"
   and fsafe2:"fsafe (foldr (||) (closeI \<Delta> j) FF)"
using eq apply(simp)
    using some L eq apply(cases "SG ! i",auto) subgoal for a b using eq  apply(cases b,auto simp add: eq,cases "b ! j",auto simp add: eq) 
      subgoal for x3 using eq apply(cases x3,auto simp add: eq) subgoal for x51 x52 apply(cases "x52",auto)
          using j eq by(cases "Inl x51 \<notin> foldr (\<lambda>x acc. acc \<union> FVF x) a {} \<and> fsafe (foldr (&&) a TT) \<and> fsafe (foldr (||) undefined FF)",auto)
        done
      subgoal for xx xs using j apply(cases "(xx # xs) !  j",auto) 
        subgoal for x3 unfolding Forall_def by(cases x3,auto) 
          subgoal for  x52 by(cases "Forall x p" ,auto) 
            subgoal for x3a
              using jD L SG_dec j eq unfolding Forall_def by(cases "Forall x p",auto)
            subgoal for x31 x32 by(cases "Forall x p" ,auto)
            subgoal for x4 by(cases "Forall x p" ,auto)
            subgoal for x51 x52 by(cases "Forall x p" ,auto)
            subgoal for x61 x62 by(cases "Forall x p" ,auto)
            done
          done
        unfolding Forall_def apply(cases "Forall x p" ,auto)
        unfolding Forall_def apply(auto simp add: Forall_def)
        subgoal for a b
          apply(cases " Inl x \<notin> foldr (\<lambda>x acc. acc \<union> FVF x) a {} \<and>
        Inl x \<notin> foldr (\<lambda>x acc. acc \<union> FVF x) b {} \<and> fsafe (foldr (&&) a TT) \<and> fsafe (foldr (||) (closeI b j) FF)",auto)
          using SG_dec by auto
        subgoal
          using some L eq jD apply(cases "SG ! i",auto)
          subgoal for a b using eq jD   
            apply(cases "Inl x \<notin> foldr (\<lambda>x acc. acc \<union> FVF x) a {} \<and>
        Inl x \<notin> foldr (\<lambda>x acc. acc \<union> FVF x) b {} \<and> fsafe (foldr (&&) a TT) \<and> fsafe (foldr (||) (closeI b j) FF)",auto)
            unfolding Forall_def SG_dec apply(cases "! (Exists x (! p))",auto) using SG_dec by auto done
        subgoal
          using some L eq jD apply(cases "SG ! i",auto)
          subgoal for a b using eq jD   
            apply(cases "Inl x \<notin> foldr (\<lambda>x acc. acc \<union> FVF x) a {} \<and>
        Inl x \<notin> foldr (\<lambda>x acc. acc \<union> FVF x) b {} \<and> fsafe (foldr (&&) a TT) \<and> fsafe (foldr (||) (closeI b j) FF)",auto)
            unfolding Forall_def SG_dec apply(cases "! (Exists x (! p))",auto) using SG_dec by auto done
        done
  have skolemR_simp:"\<And>\<Gamma> \<Delta> SS p q. 
    (nth \<Delta> j) = Forall x p \<Longrightarrow> 
    (Inl x \<notin> FVSeq (\<Gamma>,\<Delta>)) \<Longrightarrow>
    fsafe (foldr (&&) \<Gamma> TT) \<Longrightarrow>
    fsafe (foldr (||) (closeI \<Delta> j) FF) \<Longrightarrow>
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    RightRule_result Skolem j SS = Some [( \<Gamma>,  (replaceI \<Delta> j p))]"
    subgoal for AI SI SS p q apply(cases SS) apply (auto simp add: Forall_def Implies_def Or_def)  done done
  have res_eq:"RightRule_result Skolem j (SG ! i) = 
    Some [( \<Gamma>,  (replaceI \<Delta> j p))]"
    apply(rule skolemR_simp)
    subgoal using eq SG_dec by (metis snd_conv)
    using fvseq fsafe1 fsafe2 apply auto
    by (rule SG_dec) 
  have rres:"rres = [( \<Gamma>,  (replaceI \<Delta> j p))]" 
    using res_eq SG_dec skolemR_simp eq some  i j L by auto
  have AIjeq:"\<Delta> ! j = (Forall x p)" 
    using SG_dec eq snd_conv
    by metis
  have big_sound:"sound ([( \<Gamma>,  (replaceI \<Delta> j p))], (\<Gamma>,\<Delta>))"
    apply(rule soundI)
    apply(rule seq_sem_UNIV_I)
(*    using  seq_semI'*)
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume "(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(\<Gamma>, replaceI \<Delta> j p)] \<Longrightarrow> seq_sem I ([(\<Gamma>, replaceI \<Delta> j p)] ! i) = UNIV)"
    then have sgs:"(\<And> \<nu> i. 0 \<le> i \<Longrightarrow> i < length [( \<Gamma>,  (replaceI \<Delta> j p))] \<Longrightarrow> \<nu> \<in> seq_sem I ([( \<Gamma>,  (replaceI \<Delta> j p))] ! i))"
      by auto
    have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
    have sg1:"\<And>\<nu>. \<nu> \<in> seq_sem I ( \<Gamma>,  (replaceI \<Delta> j p))" using sgs[of 0] by auto
    then have sg2:"\<And>\<nu>. \<nu> \<in> seq_sem I ( \<Gamma>,  p # (closeI \<Delta> j))" 
      subgoal for \<nu> using replaceI_closeI_disj[of \<nu> I \<Delta> j p] jD by auto done
    have disj:"\<nu> \<in> fml_sem I (foldr Or (replaceI \<Delta> j p) FF)" 
      using seq_MP ante sg1[of \<nu>] by auto
    then have disj2:"\<nu> \<in> fml_sem I (foldr (||) (p # closeI \<Delta> j) FF)" 
      using replaceI_closeI_disj[of \<nu> I \<Delta> j p, OF disj jD] by auto
    then have disjOr:"\<nu> \<notin> fml_sem I (foldr (||) (closeI \<Delta> j) FF) \<or> \<nu> \<in> fml_sem I (foldr (||) (closeI \<Delta> j) FF)" 
      by auto  
     have disjOr2:"\<nu> \<in> fml_sem I (Forall x p) \<or> \<nu> \<in> fml_sem I (foldr (||) (closeI \<Delta> j) FF)" 
       apply(rule disjE[OF disjOr])
       subgoal 
       proof (rule disjI1, auto)
          fix r
          let ?upsem = "(\<lambda> \<nu> p. (\<forall>r. (\<chi> y. if x = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I p))"
          let ?upnsem = "(\<lambda> \<nu> p. (\<forall>r. (\<chi> y. if x = y then r else fst \<nu> $ y, snd \<nu>) \<notin> fml_sem I p))"
          have upgam:"?upsem \<nu> (foldr (&&) \<Gamma> TT)"
            apply(auto)
            subgoal for r proof -
              have conj_fvf_foldr_sub:"FVF (foldr (&&) \<Gamma> TT) \<subseteq> foldr (\<lambda>x acc. acc \<union> FVF x) \<Gamma> {}"
                by(induction \<Gamma>,auto simp add: TT_def)
              have VA:"Vagree \<nu> (\<chi> y. if x = y then r else fst \<nu> $ y, snd \<nu>) (FVF (foldr (&&) \<Gamma> TT))" 
                using fvseq conj_fvf_foldr_sub by(auto simp add: Vagree_def)
              note coin =  coincidence_formula[OF fsafe1 good good Iagree_refl VA]
              show " (\<chi> y. if x = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
                using coin ante by auto
            qed
            done
          assume del:"\<nu> \<notin> fml_sem I (foldr (||) (closeI \<Delta> j) FF)"
          then have updel:"?upnsem \<nu> (foldr (||) (closeI \<Delta> j) FF)"
            apply(auto)
            subgoal for r proof -
              assume nosem:"\<nu> \<notin> fml_sem I (foldr (||) (closeI \<Delta> j) FF)"
              assume sem:"(\<chi> y. if x = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (foldr (||) (closeI \<Delta> j) FF)"
              have disj_fvf_sub:"FVF (foldr (||) (closeI \<Delta> j) FF) \<subseteq> FVF (foldr (||) \<Delta> FF)" 
              proof -
                have "j < length \<Delta> \<Longrightarrow> FVF (foldr (||) (closeI \<Delta> j) FF) \<subseteq> FVF (foldr (||) \<Delta> FF)"
                  apply(induction rule: index_list_induct)
                  subgoal for L
                    by(auto simp add: FF_def Or_def, induction L,auto simp add: member_rec Or_def FF_def)  
                  by(auto simp add: member_rec Or_def FF_def jD)
                then show "FVF (foldr (||) (closeI \<Delta> j) FF) \<subseteq> FVF (foldr (||) \<Delta> FF)"   
                  using jD by auto
              qed
              have disj_fvf_foldr_sub:"FVF (foldr (||) \<Delta> FF) \<subseteq> foldr (\<lambda>x acc. acc \<union> FVF x) \<Delta> {}"
                by (induction \<Delta>) auto
              have VA:"Vagree \<nu> (\<chi> y. if x = y then r else fst \<nu> $ y, snd \<nu>) (FVF (foldr (||) (closeI \<Delta> j) FF))" 
                using fvseq disj_fvf_sub disj_fvf_foldr_sub by(auto simp add: Vagree_def)
              note coin =  coincidence_formula[OF fsafe2 good good Iagree_refl VA]
              show False  
                using coin nosem sem by auto
            qed
            done
          then show "(\<chi> y. if x = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I p " 
            using sg2[of "(\<chi> y. if x = y then r else fst \<nu> $ y, snd \<nu>)"] updel upgam by(auto)
        qed
        by(auto)
     then have disj3:"\<nu> \<in> fml_sem I (foldr (||) (Forall x p # closeI \<Delta> j) FF)"
       by(auto)
     then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" 
       using closeI_ident_disj[OF jD AIjeq, of I] by auto
     qed
  then show ?thesis using some SG_dec rres by auto
next
  case NotR then have L:"L = NotR" by auto
  obtain x p where eq:"(snd (SG ! i) ! j) = (Not p)"      
    using some i L apply(auto simp add: some i L) apply(cases "SG ! i",auto simp add: L Forall_def)
    subgoal for a b by(cases "b ! j", auto) done 
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have notR_simp:"\<And>\<Gamma> \<Delta> SS p. 
    (nth \<Delta> j) = Not p \<Longrightarrow> 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    RightRule_result NotR j SS = Some [(\<Gamma> @ [p], closeI \<Delta> j)]"
    subgoal for AI SI SS p apply(cases SS) apply (auto simp add: Forall_def Implies_def Or_def) done done
  have res_eq:"RightRule_result NotR j (SG ! i) = 
    Some [(\<Gamma> @ [p], closeI \<Delta> j)]"
    apply(rule notR_simp)
    subgoal using eq SG_dec by (metis snd_conv)
    by (rule SG_dec) 
  have rres:"rres = [(\<Gamma> @ [p], closeI \<Delta> j)]" 
    using res_eq SG_dec notR_simp eq some  i j L by auto
  have AIjeq:"\<Delta> ! j = (Not  p)" 
    using SG_dec eq snd_conv
    by metis
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  then have jD:"j < length \<Delta>" using SG_dec j by auto
  have big_sound:"sound ([(\<Gamma> @ [p], closeI \<Delta> j)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(\<Gamma> @ [p], closeI \<Delta> j)] \<Longrightarrow> \<nu> \<in> seq_sem I ([(\<Gamma> @ [p], closeI \<Delta> j)] ! i))"
     have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
     have "\<nu> \<in> seq_sem I (\<Gamma> @ [p], closeI \<Delta> j)" using sgs[of 0] by auto
     have s1:"\<nu> \<in> seq_sem I (p # \<Gamma> , closeI \<Delta> j)" using sgs[of 0]   snoc_assoc_conj by auto
     then have s2:"\<nu> \<in> seq_sem I ( \<Gamma> , Not p # closeI \<Delta> j)" using sgs[of 0] by(auto)
     then have s3:"\<nu> \<in> seq_sem I ( \<Gamma> , nth \<Delta> j # closeI \<Delta> j)" using sgs[of 0]  AIjeq by (auto simp add: \<Delta> AIjeq)
     then have s4:"\<nu> \<in> seq_sem I ( \<Gamma> , \<Delta>)" using sgs[of 0]  AIjeq 
       closeI_ident_disj[OF jD , of "\<Delta> ! j", of I, OF refl] by auto
     then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" 
       using closeI_ident_disj[OF jD AIjeq, of I] ante seq_MP[OF s3 ante] by auto
     qed
  then show ?thesis using some SG_dec rres by auto
next
  case HideR then have L:"L = HideR" by auto
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have hideR_simp:"\<And>\<Gamma> \<Delta> SS. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    RightRule_result HideR j SS = Some [(\<Gamma>, closeI \<Delta> j)]"
    subgoal for AI SI SS apply(cases SS) apply (auto) done done
  have res_eq:"RightRule_result HideR j (SG ! i) = 
    Some [(\<Gamma>, closeI \<Delta> j)] "
    apply(rule hideR_simp)
    subgoal using  SG_dec by (metis snd_conv) done
  have rres:"rres = [(\<Gamma>, closeI \<Delta> j)]" 
    using res_eq SG_dec hideR_simp some  i j L by auto
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  then have jD:"j < length \<Delta>" using SG_dec j by auto
  have big_sound:"sound ([(\<Gamma>, closeI \<Delta> j)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(\<Gamma>, closeI \<Delta> j)] \<Longrightarrow> \<nu> \<in> seq_sem I ([(\<Gamma>, closeI \<Delta> j)] ! i))"
     have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
     have "\<nu> \<in> seq_sem I (\<Gamma>, closeI \<Delta> j)" using sgs[of 0] by auto
    then have "\<nu> \<in> fml_sem I (foldr (||) ((nth \<Delta> j) # closeI \<Delta> j) FF)"
      using ante by auto
    then show " \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using closeI_ident_disj[OF jD , of "\<Delta> ! j", of I, OF refl] by auto
     qed
  then show ?thesis using some SG_dec rres by auto
next
  case (CutRight cutFml)  then have L:"L = CutRight cutFml" by auto
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have cutR_simp:"\<And>\<Gamma> \<Delta> SS. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    RightRule_result (CutRight cutFml) j SS = Some [(\<Gamma>, replaceI \<Delta> j cutFml), (\<Gamma>, replaceI \<Delta> j (Implies cutFml (nth \<Delta> j)))]"
    subgoal for AI SI SS apply(cases SS) apply (auto) done done
  have res_eq:"RightRule_result (CutRight cutFml) j (SG ! i) = 
    Some [(\<Gamma>, replaceI \<Delta> j cutFml), (\<Gamma>, replaceI \<Delta> j (Implies cutFml (nth \<Delta> j)))]"
    apply(rule cutR_simp)
    subgoal using  SG_dec by (metis snd_conv) done
  have rres:"rres = [(\<Gamma>, replaceI \<Delta> j cutFml), (\<Gamma>, replaceI \<Delta> j (Implies cutFml (nth \<Delta> j)))]" 
    using res_eq SG_dec cutR_simp some  i j L by auto
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  then have jD:"j < length \<Delta>" using SG_dec j by auto
  have big_sound:"sound ([(\<Gamma>, replaceI \<Delta> j cutFml), (\<Gamma>, replaceI \<Delta> j (Implies cutFml (nth \<Delta> j)))], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(\<Gamma>, replaceI \<Delta> j cutFml), (\<Gamma>, replaceI \<Delta> j (Implies cutFml (nth \<Delta> j)))] \<Longrightarrow> \<nu> \<in> seq_sem I ([(\<Gamma>, replaceI \<Delta> j cutFml), (\<Gamma>, replaceI \<Delta> j (Implies cutFml (nth \<Delta> j)))] ! i))"
     have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
    have l1:"\<nu> \<in> seq_sem I (\<Gamma>, replaceI \<Delta> j cutFml)" using sgs[of 0] by auto
    then have l2:"\<nu> \<in> seq_sem I (\<Gamma>, cutFml # closeI \<Delta> j)"
       using replaceI_closeI_disj[of \<nu> I \<Delta> j cutFml] jD by(auto)
    have r1:"\<nu> \<in> seq_sem I (\<Gamma>, replaceI \<Delta> j (Implies cutFml (nth \<Delta> j)))" using sgs[of 1] by auto
    then have r2:"\<nu> \<in> seq_sem I (\<Gamma>, (Implies cutFml (nth \<Delta> j)) # closeI \<Delta> j )" 
       using replaceI_closeI_disj[of \<nu> I \<Delta> j "(Implies cutFml (nth \<Delta> j))"] jD by(auto)
    from l2  have fl1:"\<nu> \<in> fml_sem I (foldr (||) (cutFml # closeI \<Delta> j) FF)"
      using ante by auto
    then have disjL:"\<nu> \<in> fml_sem I cutFml \<or> \<nu> \<in> fml_sem I (foldr (||) ( closeI \<Delta> j) FF)" by auto
    from r2  have fr1:"\<nu> \<in> fml_sem I (foldr (||) ((Implies cutFml (nth \<Delta> j)) # closeI \<Delta> j) FF)"
      using ante by auto
    then have disjR:"\<nu> \<in> fml_sem I (Implies cutFml (nth \<Delta> j)) \<or> \<nu> \<in> fml_sem I (foldr (||) ( closeI \<Delta> j) FF)" by auto
    from disjL disjR have ors:"(\<nu> \<in> fml_sem I cutFml \<and> \<nu> \<in> fml_sem I (Implies cutFml (nth \<Delta> j))) \<or> \<nu> \<in> fml_sem I (foldr (||) ( closeI \<Delta> j) FF)"
      by auto
    have f:"\<nu> \<in> fml_sem I (foldr (||) ( (nth \<Delta> j) # closeI \<Delta> j) FF)" 
      apply(rule disjE[OF ors])
      subgoal unfolding Implies_def Or_def by auto
      by(auto)
    then show " \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using closeI_ident_disj[OF jD , of "\<Delta> ! j", of I, OF refl] by auto
     qed
  then show ?thesis using some SG_dec rres by auto
next
  case EquivifyR  then have L:"L = EquivifyR" by auto
  obtain p q where eq:"(snd (SG ! i) ! j) = (Implies p q)"      
    using some i L apply(auto simp add: some i L) apply(cases "SG ! i",auto simp add: L Implies_def Or_def)
    subgoal for a b 
    apply(cases "b ! j", auto) 
    subgoal for x3 apply(cases x3,auto) subgoal for x41 x42 apply(cases x41,auto) 
    subgoal for x3a apply(cases x42,auto) subgoal for x3b by(cases x3b,auto) done done done done done
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have equivifyR_simp:"\<And>\<Gamma> \<Delta> SS p q. 
    (nth \<Delta> j) = Implies p  q \<Longrightarrow> 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    RightRule_result EquivifyR j SS = Some [(\<Gamma>, replaceI \<Delta> j (Equiv p q))]"
    subgoal for AI SI SS p q apply(cases SS) apply (auto simp add: Equiv_def Forall_def Implies_def Or_def) done done
  have res_eq:"RightRule_result EquivifyR j (SG ! i) = 
    Some [(\<Gamma>, replaceI \<Delta> j (Equiv p q))]"
    apply(rule equivifyR_simp)
    subgoal using eq SG_dec by (metis snd_conv)
    by (rule SG_dec) 
  have rres:"rres = [(\<Gamma>, replaceI \<Delta> j (Equiv p q))]" 
    using res_eq SG_dec equivifyR_simp eq some  i j L by auto
  have AIjeq:"\<Delta> ! j = (Implies p q)" 
    using SG_dec eq snd_conv
    by metis
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  then have jD:"j < length \<Delta>" using SG_dec j by auto
  have big_sound:"sound ([(\<Gamma>, replaceI \<Delta> j (Equiv p q))], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(\<Gamma>, replaceI \<Delta> j (Equiv p q))] \<Longrightarrow> \<nu> \<in> seq_sem I ([(\<Gamma>, replaceI \<Delta> j (Equiv p q))] ! i))"
     have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
     have s1:"\<nu> \<in> seq_sem I (\<Gamma>, replaceI \<Delta> j (Equiv p q))" using sgs[of 0] by auto
     then have f1:"\<nu> \<in> fml_sem I (foldr (||)  (replaceI \<Delta> j (Equiv p q)) FF)"
       using ante seq_MP by auto
     have f2:"\<nu> \<in> fml_sem I (foldr (||)  ((Equiv p q) # closeI \<Delta> j) FF)" 
       by (rule replaceI_closeI_disj[of \<nu> I \<Delta> j "(p \<leftrightarrow> q)", OF f1 jD])
     then have f3:"\<nu> \<in> fml_sem I (foldr (||)  ((Implies p q) # closeI \<Delta> j) FF)" 
       by(auto simp add: Equiv_def)
     then have s3:"\<nu> \<in> fml_sem I (foldr (||) (nth \<Delta> j # closeI \<Delta> j) FF)" using sgs[of 0]  AIjeq by (auto simp add: \<Delta> AIjeq)
     then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" using closeI_ident_disj[OF jD , of "\<Delta> ! j", of I, OF refl]  by auto
     qed
  then show ?thesis using some SG_dec rres by auto
next
  case CommuteEquivR  then have L:"L = CommuteEquivR" by auto
  obtain p q where eq:"(snd (SG ! i) ! j) = (Equiv p q)"      
    using some i L apply(auto simp add: some i L) apply(cases "SG ! i",auto simp add: L Implies_def Or_def)
    subgoal for a b 
    apply(cases "b ! j", auto) 
    subgoal for x3 apply(cases x3,auto) subgoal for x41 x42 apply(cases x41,auto) 
      subgoal for x3a apply(cases x42,auto) 
        apply(cases x3a,auto) 
        apply(cases x3a,auto) apply(cases x3a,auto)
        subgoal for x3b x41 x42 apply(cases x3b,auto)
          subgoal for x41b x42b
            apply(cases x41b,auto)
            apply(cases x42b,auto) subgoal for x3c x3aa
              by(cases " x41 = x3c \<and> x42 = x3aa",auto simp add: Equiv_def Or_def)
            done done 
       apply(cases x3a,auto)+
      done done done done done
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have equivifyR_simp:"\<And>\<Gamma> \<Delta> SS p q. 
    (nth \<Delta> j) = Equiv p  q \<Longrightarrow> 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    RightRule_result CommuteEquivR j SS = Some [(\<Gamma>, replaceI \<Delta> j (Equiv q p))]"
    subgoal for AI SI SS p q apply(cases SS) apply (auto simp add: Equiv_def Forall_def Implies_def Or_def) done done
  have res_eq:"RightRule_result CommuteEquivR j (SG ! i) = 
    Some [(\<Gamma>, replaceI \<Delta> j (Equiv q p))]"
    apply(rule equivifyR_simp)
    subgoal using eq SG_dec by (metis snd_conv)
    by (rule SG_dec) 
  have rres:"rres = [(\<Gamma>, replaceI \<Delta> j (Equiv q p))]" 
    using res_eq SG_dec equivifyR_simp eq some  i j L by auto
  have AIjeq:"\<Delta> ! j = (Equiv p q)" 
    using SG_dec eq snd_conv
    by metis
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  then have jD:"j < length \<Delta>" using SG_dec j by auto
  have big_sound:"sound ([(\<Gamma>, replaceI \<Delta> j (Equiv q p))], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(\<Gamma>, replaceI \<Delta> j (Equiv q p))] \<Longrightarrow> \<nu> \<in> seq_sem I ([(\<Gamma>, replaceI \<Delta> j (Equiv q p))] ! i))"
     have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
     have s1:"\<nu> \<in> seq_sem I (\<Gamma>, replaceI \<Delta> j (Equiv q p))" using sgs[of 0] by auto
     then have f1:"\<nu> \<in> fml_sem I (foldr (||)  (replaceI \<Delta> j (Equiv q p)) FF)"
       using ante seq_MP by auto
     have f2:"\<nu> \<in> fml_sem I (foldr (||)  ((Equiv q p) # closeI \<Delta> j) FF)" 
       by (rule replaceI_closeI_disj[of \<nu> I \<Delta> j "(q \<leftrightarrow> p)", OF f1 jD])
     then have f3:"\<nu> \<in> fml_sem I (foldr (||)  ((Equiv p q) # closeI \<Delta> j) FF)" 
       by(auto simp add: Equiv_def)
     then have s3:"\<nu> \<in> fml_sem I (foldr (||) (nth \<Delta> j # closeI \<Delta> j) FF)" using sgs[of 0]  AIjeq by (auto simp add: \<Delta> AIjeq)
     then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" using closeI_ident_disj[OF jD , of "\<Delta> ! j", of I, OF refl]  by auto
     qed
     then show ?thesis using some SG_dec rres by auto
next
  case (BRenameR what repl)
  then have L:"L = BRenameR what repl" by auto
  have exist:"(\<exists> t p.(snd (SG ! i) ! j) =  ([[what := t]]p)) \<or> (\<exists> p. (snd (SG ! i) ! j) = Forall what p)" 
    using some i L apply(auto simp add: some i L) apply(cases "SG ! i",auto simp add: L Equiv_def Implies_def Or_def)
    apply(cases "what = repl",auto)
    subgoal for a b
      apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto)
        subgoal for x61 x62 
          apply(cases x62,auto) subgoal for x3a
            apply(cases " what = x61 \<and>
        FRadmit (Forall x61 x3a) \<and>
        FRadmit x3a \<and>
        fsafe (Forall x61 x3a) \<and>
        Inl repl \<notin> FVF (Forall x61 x3a) \<and>
        Inr repl \<notin> FVF (Forall x61 x3a) \<and>
        Inr what \<notin> FVF (Forall x61 x3a) \<and>
        FRadmit (Forall repl (FUrename x61 repl x3a)) \<and>
        FRadmit (FUrename x61 repl x3a) \<and>
        fsafe (Forall repl (FUrename x61 repl x3a)) \<and>
        Inl x61 \<notin> FVF (Forall repl (FUrename x61 repl x3a)) \<and>
        Inr x61 \<notin> FVF (Forall repl (FUrename x61 repl x3a)) \<and> Inr repl \<notin> FVF (Forall repl (FUrename x61 repl x3a))")
            by(auto simp add: Box_def Forall_def) done
        subgoal for x61 x62 
          apply(cases x62,auto) subgoal for x3a by(cases x61,auto)
          subgoal for x21 x22 by(cases x61,auto)
          subgoal for x3a apply(cases x61,auto) subgoal for x21 x22
            by(cases "what = x21 \<and>
        TRadmit x22 \<and>
        FRadmit x3a \<and>
        dsafe x22 \<and>
        fsafe x3a \<and>
        Inl repl \<notin> FVT x22 \<and>
        (Inl repl \<in> FVF x3a \<longrightarrow> repl = x21) \<and>
        Inr repl \<notin> FVT x22 \<and>
        Inr repl \<notin> FVF x3a \<and>
        Inr what \<notin> FVT x22 \<and>
        Inr what \<notin> FVF x3a \<and>
        TRadmit x22 \<and>
        FRadmit (FUrename x21 repl x3a) \<and>
        dsafe x22 \<and>
        fsafe (FUrename x21 repl x3a) \<and>
        Inl x21 \<notin> FVT x22 \<and>
        (Inl x21 \<in> FVF (FUrename x21 repl x3a) \<longrightarrow> x21 = repl) \<and>
        Inr x21 \<notin> FVT x22 \<and> Inr x21 \<notin> FVF (FUrename x21 repl x3a) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF (FUrename x21 repl x3a)",auto simp add: Box_def Forall_def)

            done
          subgoal for x41 x42 by(cases x61,auto)
          subgoal for x51 x52 by(cases x61,auto)
          subgoal for x51 x52 by(cases x61,auto)
          subgoal for x51 x52 by(cases x61,auto)
          done done done done

  have all_case:"(\<exists>  p.(snd (SG ! i) ! j) =  (Forall what p)) \<Longrightarrow> ?thesis"
  proof -
    assume "(\<exists>  p.(snd (SG ! i) ! j) =  (Forall what p))"
    then obtain  p where eq:"(snd (SG ! i) ! j) = (Forall what p)" by(auto)
    have admits:
     " FRadmit (Forall what p) \<and> FRadmit p \<and> fsafe (Forall what  p) \<and>
           {Inl repl, Inr repl, Inr what} \<inter> FVF (Forall what p) = {} \<and>
          FRadmit (Forall repl (FUrename what  repl p)) \<and>
         FRadmit (FUrename what repl p) \<and>
         fsafe (Forall repl (FUrename what repl p)) \<and>
         {Inl what, Inr what, Inr repl} \<inter> FVF (Forall repl (FUrename what repl p)) = {}"

            using some i L  apply(cases "SG ! i", auto simp add: L Equiv_def Implies_def Or_def some i)apply(cases "what = repl",auto)
            subgoal for a b
              apply(cases "b ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62,auto)
                  subgoal for x3a using eq apply(cases "FRadmit p \<and> fsafe p \<and> Inl repl \<notin> FVF p \<and> Inr repl \<notin> FVF p \<and> Inr what \<notin> FVF p ",auto simp add: Box_def Forall_def eq) done done
                subgoal for x61 x62 apply(cases x61,auto,cases x62,auto) 
                  subgoal for x21 x22 x3a using eq
                  by(cases "what = x21 \<and>
           TRadmit x22 \<and>
           ((\<exists>\<theta>1 \<theta>2. ([[x21 := x22]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
            (\<exists>args. (\<exists>p. ([[x21 := x22]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
            (\<exists>\<phi>. ([[x21 := x22]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
            (\<exists>\<phi> \<psi>. ([[x21 := x22]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
            (\<exists>\<phi>. (\<exists>x. ([[x21 := x22]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x21 := x22]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
           FRadmit x3a \<and>
           fsafe ([[x21 := x22]]x3a) \<and>
           Inl repl \<notin> FVF ([[x21 := x22]]x3a) \<and> Inr repl \<notin> FVF ([[x21 := x22]]x3a) \<and> Inr what \<notin> FVF ([[x21 := x22]]x3a)",auto simp add: Forall_def)
                done done done
                subgoal for a b
                  apply(cases "what = repl",auto)
              apply(cases "b ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21  using eq apply(cases x62,auto) 
                    by(cases " what = x61 \<and>
        FRadmit (Forall x61 x21) \<and>
        FRadmit x21 \<and> fsafe (Forall x61 x21) \<and> Inl repl \<notin> FVF (Forall x61 x21) \<and> Inr repl \<notin> FVF (Forall x61 x21) \<and> Inr what \<notin> FVF (Forall x61 x21)
",auto simp add: Forall_def)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  done
                subgoal for a b
                 apply(cases "what = repl",auto)
              apply(cases "a",auto) apply(cases "b",auto simp add: Box_def)
                  subgoal for x21 x22 x3
                    apply(cases "what = x21 \<and>
        TRadmit x22 \<and>
        FRadmit x3 \<and>
        dsafe x22 \<and>
        fsafe x3 \<and>
        Inl repl \<notin> FVT x22 \<and> (Inl repl \<in> FVF x3 \<longrightarrow> repl = x21) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF x3 \<and> Inr what \<notin> FVT x22 \<and> Inr what \<notin> FVF x3
")
                    subgoal  using eq by(auto simp add: Box_def Forall_def)
                    subgoal  using eq by(auto simp add: Box_def Forall_def) done done done done

                subgoal for a b
                  apply(cases "what = repl",auto, cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Forall_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Forall_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Forall_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Box_def Forall_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Forall_def)  
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def Forall_def) 
                      done done
                    done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Forall_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def Forall_def) 
                      done done
                    done done 
              subgoal for a b
              apply(cases "what = repl",auto, cases "b ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62,auto)
                  subgoal for x3a using eq
                    apply(cases "what = x61 \<and>
        FRadmit (Forall x61 x3a) \<and>
        FRadmit x3a \<and>
        fsafe (Forall x61 x3a) \<and>
        Inl repl \<notin> FVF (Forall x61 x3a) \<and>
        Inr repl \<notin> FVF (Forall x61 x3a) \<and>
        Inr what \<notin> FVF (Forall x61 x3a) \<and>
        FRadmit (Forall repl (FUrename x61 repl x3a)) \<and>
        FRadmit (FUrename x61 repl x3a) \<and>
        fsafe (Forall repl (FUrename x61 repl x3a)) \<and>
        Inl x61 \<notin> FVF (Forall repl (FUrename x61 repl x3a)) \<and>
        Inr x61 \<notin> FVF (Forall repl (FUrename x61 repl x3a)) \<and> Inr repl \<notin> FVF (Forall repl (FUrename x61 repl x3a))",auto simp add: Box_def Forall_def eq) done done
                subgoal for x61 x62 apply(cases x61,auto,cases x62,auto) 
                  subgoal for x21 x22 x3a using eq
                  by(cases "what = x21 \<and>
           TRadmit x22 \<and>
           ((\<exists>\<theta>1 \<theta>2. ([[x21 := x22]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
            (\<exists>args. (\<exists>p. ([[x21 := x22]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
            (\<exists>\<phi>. ([[x21 := x22]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
            (\<exists>\<phi> \<psi>. ([[x21 := x22]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
            (\<exists>\<phi>. (\<exists>x. ([[x21 := x22]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x21 := x22]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
           FRadmit x3a \<and>
           fsafe ([[x21 := x22]]x3a) \<and>
           Inl repl \<notin> FVF ([[x21 := x22]]x3a) \<and> Inr repl \<notin> FVF ([[x21 := x22]]x3a) \<and> Inr what \<notin> FVF ([[x21 := x22]]x3a)",auto simp add: Forall_def)
                done done done
                subgoal for a b
                  apply(cases "what = repl",auto)
              apply(cases "b ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21  using eq apply(cases x62,auto) 
                    by(cases "what = x61 \<and>
        FRadmit (Forall x61 x21) \<and>
        FRadmit x21 \<and>
        fsafe (Forall x61 x21) \<and>
        Inl repl \<notin> FVF (Forall x61 x21) \<and>
        Inr repl \<notin> FVF (Forall x61 x21) \<and>
        Inr what \<notin> FVF (Forall x61 x21) \<and>
        FRadmit (Forall repl (FUrename x61 repl x21)) \<and>
        FRadmit (FUrename x61 repl x21) \<and>
        fsafe (Forall repl (FUrename x61 repl x21)) \<and>
        Inl x61 \<notin> FVF (Forall repl (FUrename x61 repl x21)) \<and>
        Inr x61 \<notin> FVF (Forall repl (FUrename x61 repl x21)) \<and> Inr repl \<notin> FVF (Forall repl (FUrename x61 repl x21))",auto simp add: Forall_def)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  done
                subgoal for a b
                 apply(cases "what = repl",auto)
              apply(cases "a",auto) apply(cases "b",auto simp add: Box_def)
                  subgoal for x21 x22 x3
                    apply(cases "what = x21 \<and>
        TRadmit x22 \<and>
        FRadmit x3 \<and>
        dsafe x22 \<and>
        fsafe x3 \<and>
        Inl repl \<notin> FVT x22 \<and> (Inl repl \<in> FVF x3 \<longrightarrow> repl = x21) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF x3 \<and> Inr what \<notin> FVT x22 \<and> Inr what \<notin> FVF x3
")
                    subgoal  using eq by(auto simp add: Box_def Forall_def)
                    subgoal  using eq by(auto simp add: Box_def Forall_def) done done done done

                subgoal for a b
                  apply(cases "what = repl",auto, cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and>
        FRadmit (Forall x51 x3a) \<and>
        FRadmit x3a \<and>
        fsafe (Forall x51 x3a) \<and>
        Inl repl \<notin> FVF (Forall x51 x3a) \<and>
        Inr repl \<notin> FVF (Forall x51 x3a) \<and>
        Inr what \<notin> FVF (Forall x51 x3a) \<and>
        FRadmit (Forall repl (FUrename x51 repl x3a)) \<and>
        FRadmit (FUrename x51 repl x3a) \<and>
        fsafe (Forall repl (FUrename x51 repl x3a)) \<and>
        Inl x51 \<notin> FVF (Forall repl (FUrename x51 repl x3a)) \<and>
        Inr x51 \<notin> FVF (Forall repl (FUrename x51 repl x3a)) \<and> Inr repl \<notin> FVF (Forall repl (FUrename x51 repl x3a))
     ",auto simp add: Forall_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Forall_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Forall_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Box_def Forall_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Forall_def)  
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def Forall_def) 
                      done done
                    done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Forall_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def Forall_def) 
                      done done
                    done done 
                  done
then have FRAwhat:"FRadmit (Forall what p)" 
     and  FRAp:"FRadmit p" 
     and fsafewhat:"fsafe (Forall what p)"
     and  fvars:"{Inl repl, Inr repl, Inr what} \<inter> FVF (Forall what p) = {}"
  by auto
  have neq:"what \<noteq> repl"
    using some i L apply(auto simp add: some i L) by(cases "SG ! i",auto simp add: L Equiv_def Implies_def Or_def Forall_def)
  from FRAwhat   have FRArepl:"FRadmit (Forall repl (FUrename what  repl p))" using admits by auto 
  from  FRAp     have FRAprepl:"FRadmit (FUrename what repl p)" using brenameR_fadmitP_lem using admits by auto 
  from fsafewhat have fsaferepl:"fsafe (Forall repl (FUrename what repl p))" using admits by auto
  from fvars     have fvarsrepl:"{Inl what, Inr what, Inr repl} \<inter> FVF (Forall repl (FUrename what repl p)) = {}" 
    using admits by auto
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have brenameR_simp:"\<And>\<Gamma> \<Delta> p SS. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    \<Delta> ! j = (Forall what p) \<Longrightarrow>
    what \<noteq> repl \<Longrightarrow>
  ( FRadmit((Forall what p)) \<and> FRadmit p \<and> fsafe (Forall what p) \<and>
     {Inl repl, Inr repl, Inr what} \<inter> FVF (Forall what p) = {})
\<and> FRadmit (Forall repl (FUrename what  repl p))
\<and> FRadmit (FUrename what repl p)
\<and> fsafe (Forall repl (FUrename what repl p))
\<and> {Inl what, Inr what, Inr repl} \<inter> FVF (Forall repl (FUrename what repl p)) = {} \<Longrightarrow>
    RightRule_result (BRenameR what repl) j SS =
    Some [(\<Gamma>,replaceI \<Delta> j (FBrename what repl (nth \<Delta> j)))]"
    subgoal for AI SI p  SS apply(cases SS) 
      by (auto simp add: Equiv_def Implies_def Or_def Box_def Forall_def)
    done
  have Gi:"\<Delta> ! j = (Forall what p)" using SG_dec eq by (cases "SG ! i",auto)
  have res_eq:"RightRule_result (BRenameR what repl) j (SG ! i) = 
    Some [(\<Gamma>,replaceI \<Delta> j (FBrename what repl (nth \<Delta> j)))]"
    apply(rule brenameR_simp)
    subgoal using  SG_dec by (metis snd_conv) 
    using SG_dec  apply(cases "SG ! i",auto  simp add: FRAwhat FRAp fsafewhat fvars eq)
            apply(rule Gi)
    subgoal using neq by auto
          defer 
          apply(rule  FRAp)
         apply(rule fsafewhat)
    subgoal using fvars by auto
    subgoal using fvars by auto
    subgoal using fvars by auto
    using FRAwhat FRAp fsafewhat fvars FRArepl FRAprepl fsaferepl fvarsrepl by auto
  have rres:"rres = [(\<Gamma>, replaceI \<Delta> j (FBrename what repl (nth \<Delta> j)))]"
    using res_eq SG_dec brenameR_simp some  i j L by auto
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  have jD:"j < length \<Delta>" using \<Delta> SG_dec j by auto
  have big_sound:"sound ([(\<Gamma>, replaceI \<Delta> j (FBrename what repl (nth \<Delta> j)))], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good_interp:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> 
    i < length [(\<Gamma>, replaceI \<Delta> j (FBrename what repl (\<Delta> ! j)))] \<Longrightarrow> 
          \<nu> \<in> seq_sem I ([(\<Gamma>, replaceI \<Delta> j (FBrename what repl (\<Delta> ! j)))] ! i))"
    have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
    from sgs have sg:"\<nu> \<in> seq_sem I (\<Gamma>, replaceI \<Delta> j (FBrename what repl (\<Delta> ! j)))" by auto
    then have sg1:"\<nu> \<in> seq_sem I (\<Gamma>, (FBrename what repl (nth \<Delta> j)) # closeI \<Delta> j )"
      using replaceI_closeI_disj[of \<nu> I  \<Delta> j "(FBrename what repl (nth \<Delta> j))"] jD by(auto)
    have sgN:"\<nu> \<in> seq_sem I (\<Gamma>, \<Delta>)"    
    proof(rule seq_semI')
      assume ante:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
      then have succ1:"\<nu> \<in> fml_sem I (foldr (||) ((FBrename what repl (nth \<Delta> j)) # closeI \<Delta> j) FF)"
        using seq_MP[OF sg1] by auto
      have case1:"\<nu> \<in> fml_sem I (FBrename what repl (nth \<Delta> j)) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) ( \<Delta> ) FF)" 
      proof - 
        have dEq:"\<Delta> ! j = (Forall what p)"           using eq \<Delta> SG_dec by auto
        have neq2:"repl \<noteq> what" using neq by auto
        assume renSem:"\<nu> \<in> fml_sem I (FBrename what repl (nth \<Delta> j))"
        then have renSem1:"\<nu> \<in> fml_sem I (FBrename what repl (Forall what  p))"
          using eq SG_dec \<Delta> by auto
        then have renSem2:"\<nu> \<in> fml_sem I (Forall repl (FUrename what repl p))"
          by(auto simp add: Box_def Forall_def)
        have renrenSem:"\<nu> \<in> fml_sem I (Forall what (FUrename repl  what (FUrename what repl p)))"
          using BRename_forall_local_sound_neq[OF  FRArepl  FRAprepl fsaferepl renSem2 fvarsrepl good_interp neq2] neq by auto
        then have canSem:"\<nu> \<in> fml_sem I (Forall what p)"
          using FUrename_cancel_sym[OF FRAp, of repl what] by auto
        then have con_sem:"\<nu> \<in> fml_sem I (foldr (||) (nth \<Delta> j # closeI  \<Delta> j) FF)"
          using eq \<Delta> SG_dec by auto
        then show "\<nu> \<in> fml_sem I (foldr (||) ( \<Delta> ) FF)"
          using closeI_ident_disj[OF jD refl,of I] by auto
      qed
      have case2:" \<nu> \<in> fml_sem I (foldr (||) (closeI \<Delta> j) FF) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) ( \<Delta> ) FF)"  
          using closeI_ident_disj[OF jD refl,of I] by auto
      show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" 
        using case1 case2 ante succ1 by auto
    qed
    show " \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      apply(rule seq_MP[OF sgN])
      using   ante eq \<Gamma>  by auto
  qed
    then show "sound (rres, SG ! i)"
      using some SG_dec rres by auto
  qed


  have box_case:"(\<exists> t p.(snd (SG ! i) ! j) =  ([[what := t]]p)) \<Longrightarrow> ?thesis"
  proof -
    assume "(\<exists> t p.(snd (SG ! i) ! j) =  ([[what := t]]p))"
    then obtain t p where eq:"(snd (SG ! i) ! j) = ([[what := t]]p)" by(auto)
          have admits:
             "TRadmit t \<and>  FRadmit ([[what := t]]p) \<and> FRadmit p \<and> fsafe ([[what := t]]p) \<and>
                 {Inl repl, Inr repl, Inr what} \<inter> FVF ([[what := t]]p) = {} \<and>
FRadmit ([[repl := t]]FUrename what  repl p) \<and>
FRadmit (FUrename what repl p) \<and>
fsafe ([[repl := t]]FUrename what repl p) \<and>
{Inl what, Inr what, Inr repl} \<inter> FVF ([[repl := t]]FUrename what repl p) = {}"
            using some i L  apply(cases "SG ! i", auto simp add: L Equiv_def Implies_def Or_def some i)apply(cases "what = repl",auto)
            subgoal for a b
              apply(cases "b ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62,auto) subgoal for x3a using eq by(auto simp add: Box_def eq) done 
                subgoal for x61 x62 apply(cases x62,auto) subgoal for x3a using eq by(auto simp add: Box_def eq)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x3a using eq apply(auto simp add: Box_def eq)by(cases "TRadmit t \<and>
        FRadmit p \<and>
        dsafe t \<and> fsafe p \<and> Inl repl \<notin> FVT t \<and> Inl repl \<notin> FVF p \<and> Inr repl \<notin> FVT t \<and> Inr repl \<notin> FVF p \<and> Inr what \<notin> FVT t \<and> Inr what \<notin> FVF p",auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              done done done

                subgoal for a b
                  apply(cases "what = repl",auto)
              apply(cases "b ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21  using eq apply(cases x62,auto) 
                    by(cases "what = x61 \<and>
        FRadmit (Forall x61 x21) \<and>
        FRadmit x21 \<and> fsafe (Forall x61 x21) \<and> Inl repl \<notin> FVF (Forall x61 x21) \<and> Inr repl \<notin> FVF (Forall x61 x21) \<and> Inr what \<notin> FVF (Forall x61 x21)",auto simp add: Box_def)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  done
                subgoal for a b
                 apply(cases "what = repl",auto)
              apply(cases "a",auto) apply(cases "b",auto simp add: Box_def)
                  subgoal for x21 x22 x3
                    apply(cases "what = x21 \<and> TRadmit x22 \<and> FRadmit x3 \<and> dsafe x22 \<and> fsafe x3 \<and> Inl repl \<notin> FVT x22 \<and> (Inl repl \<in> FVF x3 \<longrightarrow> repl = x21) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF x3 \<and> Inr what \<notin> FVT x22 \<and> Inr what \<notin> FVF x3")
                    subgoal  using eq by(auto simp add: Box_def)
                    subgoal  using eq by(auto simp add: Box_def) done

                  subgoal for x21 x22 x3
                    apply(cases "what = x21 \<and> TRadmit x22 \<and>  FRadmit x3 \<and> dsafe x22 \<and> fsafe x3 \<and> Inl repl \<notin> FVT x22 \<and> (Inl repl \<in> FVF x3 \<longrightarrow> repl = x21) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF x3 \<and> Inr what \<notin> FVT x22 \<and> Inr what \<notin> FVF x3")
                    subgoal  using eq by(auto simp add: Box_def)
                    subgoal  using eq by(auto simp add: Box_def) done
                  done done done
                subgoal for a b
                  apply(cases "what = repl",auto, cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Box_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Box_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Box_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Box_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done
                    done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done
                    done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done
                    done done 
                      apply(cases "what = repl",auto)
            subgoal for a b
              apply(cases "b ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62,auto) subgoal for x3a using eq by(auto simp add: Box_def eq) done 
                subgoal for x61 x62 apply(cases x62,auto) subgoal for x3a using eq by(auto simp add: Box_def eq)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x3a using eq apply(auto simp add: Box_def eq)
                done
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              subgoal for x21 x22 by(cases x61,auto)
              done done done

                subgoal for a b
                  apply(cases "what = repl",auto)
              apply(cases "b ! j",auto)
              subgoal for x3
                apply(cases x3,auto) subgoal for x61 x62 apply(cases x62)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21  using eq apply(cases x62,auto) 
                    by(cases "what = x61 \<and>
        FRadmit (Forall x61 x21) \<and>
        FRadmit x21 \<and> fsafe (Forall x61 x21) \<and> Inl repl \<notin> FVF (Forall x61 x21) \<and> Inr repl \<notin> FVF (Forall x61 x21) \<and> Inr what \<notin> FVF (Forall x61 x21)",auto simp add: Box_def)
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  subgoal for x21 x22 using eq apply(cases x62,auto) done
                  done
                subgoal for a b
                 apply(cases "what = repl",auto)
              apply(cases "a",auto) apply(cases "b",auto simp add: Box_def)
                  subgoal for x21 x22 x3
                    apply(cases "what = x21 \<and>
        TRadmit x22 \<and>
        FRadmit x3 \<and>
        dsafe x22 \<and>
        fsafe x3 \<and>
        Inl repl \<notin> FVT x22 \<and>
        (Inl repl \<in> FVF x3 \<longrightarrow> repl = x21) \<and>
        Inr repl \<notin> FVT x22 \<and>
        Inr repl \<notin> FVF x3 \<and>
        Inr what \<notin> FVT x22 \<and>
        Inr what \<notin> FVF x3 \<and>
        TRadmit x22 \<and>
        FRadmit (FUrename x21 repl x3) \<and>
        dsafe x22 \<and>
        fsafe (FUrename x21 repl x3) \<and>
        Inl x21 \<notin> FVT x22 \<and>
        (Inl x21 \<in> FVF (FUrename x21 repl x3) \<longrightarrow> x21 = repl) \<and>
        Inr x21 \<notin> FVT x22 \<and> Inr x21 \<notin> FVF (FUrename x21 repl x3) \<and> Inr repl \<notin> FVT x22 \<and> Inr repl \<notin> FVF (FUrename x21 repl x3)")
                    subgoal  using eq by(auto simp add: Box_def)
                    subgoal  using eq by(auto simp add: Box_def) done done done done
                subgoal for a b
                  apply(cases "what = repl",auto, cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Box_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or>
         (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and>
        Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and>
        Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and>
        Inr what \<notin> FVF ([[x51 := x52]]x3a) \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[repl := x52]]FUrename x51 repl x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[repl := x52]]FUrename x51 repl x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[repl := x52]]FUrename x51 repl x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[repl := x52]]FUrename x51 repl x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[repl := x52]]FUrename x51 repl x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or>
         (\<exists>\<alpha> \<phi>. ([[repl := x52]]FUrename x51 repl x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit (FUrename x51 repl x3a) \<and>
        fsafe ([[repl := x52]]FUrename x51 repl x3a) \<and>
        Inl x51 \<notin> FVF ([[repl := x52]]FUrename x51 repl x3a) \<and>
        Inr x51 \<notin> FVF ([[repl := x52]]FUrename x51 repl x3a) \<and> Inr repl \<notin> FVF ([[repl := x52]]FUrename x51 repl x3a)",auto simp add: Box_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for x3a
                        using eq by(cases "what = x51 \<and> FRadmit (Forall x51 x3a) \<and> FRadmit x3a \<and> fsafe (Forall x51 x3a) \<and> Inl repl \<notin> FVF (Forall x51 x3a) \<and> Inr repl \<notin> FVF (Forall x51 x3a) \<and> Inr what \<notin> FVF (Forall x51 x3a)",auto simp add: Box_def)
                      done
                    subgoal for x51 x52 apply(cases x51,auto,cases x52,auto) subgoal for x51 x52 x3a    
                      using eq by(cases "what = x51 \<and>
        TRadmit x52 \<and>
        ((\<exists>\<theta>1 \<theta>2. ([[x51 := x52]]x3a) = Geq \<theta>1 \<theta>2 \<and> TRadmit \<theta>1 \<and> TRadmit \<theta>2) \<or>
         (\<exists>args. (\<exists>p. ([[x51 := x52]]x3a) = $\<phi> p args) \<and> (\<forall>i. TRadmit (args i))) \<or>
         (\<exists>\<phi>. ([[x51 := x52]]x3a) = ! \<phi> \<and> FRadmit \<phi>) \<or>
         (\<exists>\<phi> \<psi>. ([[x51 := x52]]x3a) = (\<phi> && \<psi>) \<and> FRadmit \<phi> \<and> FRadmit \<psi>) \<or>
         (\<exists>\<phi>. (\<exists>x. ([[x51 := x52]]x3a) = Exists x \<phi>) \<and> FRadmit \<phi>) \<or> (\<exists>\<alpha> \<phi>. ([[x51 := x52]]x3a) = (\<langle> \<alpha> \<rangle> \<phi>) \<and> PRadmit \<alpha> \<and> FRadmit \<phi>)) \<and>
        FRadmit x3a \<and>
        fsafe ([[x51 := x52]]x3a) \<and> Inl repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr repl \<notin> FVF ([[x51 := x52]]x3a) \<and> Inr what \<notin> FVF ([[x51 := x52]]x3a)",auto simp add: Box_def)
                    done done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done
                    done done
                subgoal for a b
                 apply(cases "what = repl",auto) apply(cases "b ! j",auto) subgoal for x3 apply(cases x3,auto) 
                    subgoal for x51 x52 apply(cases x52,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done 
                    subgoal for x51 x52 apply(cases x51,auto) subgoal for  x3a    
                      using eq apply(auto simp add: Box_def) 
                      done done
                    done done done
then have TRA:"TRadmit t" 
     and  FRAwhat:"FRadmit ([[what := t]]p)" 
     and  FRAp:"FRadmit p" 
     and fsafewhat:"fsafe ([[what := t]]p)"
     and  fvars:"{Inl repl, Inr repl, Inr what} \<inter> FVF ([[what := t]]p) = {}"
  by auto
  have neq:"what \<noteq> repl"
    using some i L apply(auto simp add: some i L) by(cases "SG ! i",auto simp add: L Equiv_def Implies_def Or_def)
  from FRAwhat   have FRArepl:"FRadmit ([[repl := t]]FUrename what  repl p)"  using admits by auto
  from  FRAp     have FRAprepl:"FRadmit (FUrename what repl p)" using admits by auto
  from fsafewhat have fsaferepl:"fsafe ([[repl := t]]FUrename what repl p)" using admits by auto
  from fvars     have fvarsrepl:"{Inl what, Inr what, Inr repl} \<inter> FVF ([[repl := t]]FUrename what repl p) = {}" 
    using admits by auto
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have brenameR_simp:"\<And>\<Gamma> \<Delta> SS. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow>  \<^cancel>\<open> \<theta> p \<close>
    \<Delta> ! j = ([[Assign what t]]p) \<Longrightarrow>
    what \<noteq> repl \<Longrightarrow>
  (TRadmit t \<and>  FRadmit([[Assign what t]]p) \<and> FRadmit p \<and> fsafe ([[Assign what t]]p) \<and>
     {Inl repl, Inr repl, Inr what} \<inter> FVF ([[Assign what t]]p) = {}
\<and> FRadmit ([[repl := t]]FUrename what  repl p)
\<and> FRadmit (FUrename what repl p)
\<and> fsafe ([[repl := t]]FUrename what repl p)
\<and> {Inl what, Inr what, Inr repl} \<inter> FVF ([[repl := t]]FUrename what repl p) = {}
) \<Longrightarrow>
    RightRule_result (BRenameR what repl) j SS =
    Some [(\<Gamma>,replaceI \<Delta> j (FBrename what repl (nth \<Delta> j)))]"
    subgoal for AI SI (*p q*) SS apply(cases SS) 
      by (auto simp add: Equiv_def Implies_def Or_def Box_def)
    done
  have Gi:"\<Delta> ! j = ([[what := t]]p)" using SG_dec eq by (cases "SG ! i",auto)
  have res_eq:"RightRule_result (BRenameR what repl) j (SG ! i) = 
    Some [(\<Gamma>,replaceI \<Delta> j (FBrename what repl (nth \<Delta> j)))]"
    apply(rule brenameR_simp)
    subgoal using  SG_dec by (metis snd_conv) 
    using SG_dec  apply(cases "SG ! i",auto  simp add: TRA FRAwhat FRAp fsafewhat fvars eq)
            apply(rule Gi)
    subgoal using neq by auto
          defer defer
          apply(rule  FRAprepl)
         apply(rule fsaferepl)
    subgoal using fvarsrepl by auto
    subgoal using fvarsrepl by auto
    subgoal using fvarsrepl by auto
    apply(erule allE[where x=t])
    apply(erule allE[where x="Diamond (Assign what  t) (Not p)"])
    apply(erule allE)
    apply(erule allE[where x=p])
    apply(erule allE[where x="Assign what t"])
    apply(auto simp add: Box_def)
    using TRA FRAwhat FRAp fsafewhat fvars FRArepl FRAprepl fsaferepl fsaferepl
    by (auto simp add: TRA FRAwhat FRAp fsafewhat fvars FRArepl FRAprepl fsaferepl fvarsrepl)
  have rres:"rres = [(\<Gamma>, replaceI \<Delta> j (FBrename what repl (nth \<Delta> j)))]" 
    using res_eq SG_dec brenameR_simp some  i j L by auto
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  have jD:"j < length \<Delta>" using \<Delta> SG_dec j by auto
  have big_sound:"sound ([(\<Gamma>, replaceI \<Delta> j (FBrename what repl (nth \<Delta> j)))], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good_interp:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> 
    i < length [(\<Gamma>, replaceI \<Delta> j (FBrename what repl (\<Delta> ! j)))] \<Longrightarrow> 
          \<nu> \<in> seq_sem I ([(\<Gamma>, replaceI \<Delta> j (FBrename what repl (\<Delta> ! j)))] ! i))"
    have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
    from sgs have sg:"\<nu> \<in> seq_sem I (\<Gamma>, replaceI \<Delta> j (FBrename what repl (\<Delta> ! j)))" by auto
    then have sg1:"\<nu> \<in> seq_sem I (\<Gamma>, (FBrename what repl (nth \<Delta> j)) # closeI \<Delta> j )"
      using replaceI_closeI_disj[of \<nu> I  \<Delta> j "(FBrename what repl (nth \<Delta> j))"] jD by(auto)
    have sgN:"\<nu> \<in> seq_sem I (\<Gamma>, \<Delta>)"    
    proof(rule seq_semI')
      assume ante:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
      then have succ1:"\<nu> \<in> fml_sem I (foldr (||) ((FBrename what repl (nth \<Delta> j)) # closeI \<Delta> j) FF)"
        using seq_MP[OF sg1] by auto
      have case1:"\<nu> \<in> fml_sem I (FBrename what repl (nth \<Delta> j)) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) ( \<Delta> ) FF)" 
      proof - 
        have dEq:"\<Delta> ! j = ([[what := t]]p)"           using eq \<Delta> SG_dec by auto
        have neq2:"repl \<noteq> what" using neq by auto
        assume renSem:"\<nu> \<in> fml_sem I (FBrename what repl (nth \<Delta> j))"
        then have renSem1:"\<nu> \<in> fml_sem I (FBrename what repl ([[what := t]]p))"
          using eq SG_dec \<Delta> by auto
        then have renSem2:"\<nu> \<in> fml_sem I (([[repl := t]]FUrename what repl p))"
          by(auto simp add: Box_def)
        have renrenSem:"\<nu> \<in> fml_sem I ([[what := t]]FUrename repl  what (FUrename what repl p))"
          using BRename_local_sound_neq[OF TRA FRArepl  FRAprepl fsaferepl renSem2 fvarsrepl good_interp neq2] neq by auto
        then have canSem:"\<nu> \<in> fml_sem I ([[what := t]]p)"
          using FUrename_cancel_sym[OF FRAp, of repl what] by auto
        then have con_sem:"\<nu> \<in> fml_sem I (foldr (||) (nth \<Delta> j # closeI  \<Delta> j) FF)"
          using eq \<Delta> SG_dec by auto
        then show "\<nu> \<in> fml_sem I (foldr (||) ( \<Delta> ) FF)"
          using closeI_ident_disj[OF jD refl,of I] by auto
      qed
      have case2:" \<nu> \<in> fml_sem I (foldr (||) (closeI \<Delta> j) FF) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) ( \<Delta> ) FF)"  
          using closeI_ident_disj[OF jD refl,of I] by auto
      show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" 
        using case1 case2 ante succ1 by auto
    qed
    show " \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      apply(rule seq_MP[OF sgN])
      using   ante eq \<Gamma>  by auto
  qed

    then show ?thesis using some SG_dec rres by auto
  qed
  show " sound (rres, SG ! i)" using box_case all_case exist some   by(auto)
next 
  case (ExchangeR k)
 then have L:"L = ExchangeR k" by auto 
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases) 
  have jk:"j \<noteq> k"  using some L apply (cases "SG ! i",auto) done
  have kD:"k < length \<Delta>" using some L apply (cases "SG ! i",auto)
    subgoal for a b 
      using SG_dec by( cases "k < length b",auto) done
  have exchangeR_simp:"\<And>\<Gamma> \<Delta> SS. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
     k < length \<Delta> \<Longrightarrow>
    j \<noteq> k \<Longrightarrow> 
    RightRule_result (ExchangeR k) j SS = Some [(\<Gamma>, replaceI (replaceI \<Delta> j (nth \<Delta> k)) k (nth \<Delta> j))]"
    subgoal for AI SI SS apply(cases SS) apply (auto) done done
  have res_eq:"RightRule_result (ExchangeR k) j (SG ! i) = 
    Some [(\<Gamma>, replaceI (replaceI \<Delta> j (nth \<Delta> k)) k (nth \<Delta> j))]"
    apply(rule exchangeR_simp)
    subgoal using  SG_dec kD by (metis snd_conv)
     apply (rule kD) 
    by (rule jk)

  have rres:"rres =  [(\<Gamma>, replaceI (replaceI \<Delta> j (nth \<Delta> k)) k (nth \<Delta> j))]" 
    using res_eq SG_dec exchangeR_simp some  i j L by auto
  have \<Gamma>:"(fst (SG ! i)) = \<Gamma>" using SG_dec by (cases "SG ! i", auto)
  have \<Delta>:"(snd (SG ! i)) = \<Delta>" using SG_dec by (cases "SG ! i", auto)
  then have jD:"j < length \<Delta>" using SG_dec j by auto
  have big_sound:"sound ([(\<Gamma>, replaceI (replaceI \<Delta> j (nth \<Delta> k)) k (nth \<Delta> j))], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume ante:" \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(\<Gamma>, replaceI (replaceI \<Delta> j (nth \<Delta> k)) k (nth \<Delta> j))] \<Longrightarrow> 
      \<nu> \<in> seq_sem I ([(\<Gamma>, replaceI (replaceI \<Delta> j (nth \<Delta> k)) k (nth \<Delta> j))] ! i))"
    have sg0:"\<nu> \<in> seq_sem I (\<Gamma>, replaceI (replaceI \<Delta> j (nth \<Delta> k)) k (nth \<Delta> j))" using sgs[of 0] by auto
    let  ?p =  "(nth \<Delta> j)" let ?q = "(nth \<Delta> k)"
    have jRep:"j < length (replaceI \<Delta> j ?q)" using kD 
    proof -                                           
      have imp:"j < length \<Delta> \<longrightarrow> length \<Delta> = length (replaceI \<Delta> j ?q)"
        apply(induction rule: index_list_induct[where P = "(\<lambda>L n. n < length L \<longrightarrow> length L = length (replaceI L n ?q))", of j \<Delta>])   
          apply(auto simp add: jD)                               
        subgoal for L by(cases L,auto) done
      then show ?thesis
        using jD kD by auto
    qed
    have kRep:"k < length (replaceI \<Delta> j ?q)" using kD 
    proof -
      have imp:"j < length \<Delta> \<longrightarrow> length \<Delta> = length (replaceI \<Delta> j ?q)"
        apply(induction rule: index_list_induct[where P = "(\<lambda>L n. n < length L \<longrightarrow> length L = length (replaceI L n ?q))", of j \<Delta>]) 
          apply(auto simp add: jD) 
        subgoal for L by(cases L,auto) done
      then show ?thesis
        using jD kD by auto
    qed
    have replace_set_in:"\<And>i::nat. \<And> L::('a list). \<And>x::'a. i < length L \<Longrightarrow> L ! i \<in> set (closeI L i) \<Longrightarrow> set (replaceI L i x) = {x} \<union> set L"
    proof - 
      fix i::"nat"  and L::"'a list" and x::"'a"
      assume i:"i < length L"
      assume s:"L ! i \<in> set (closeI L i)"                        
      have imply:"i < length L \<and> L ! i \<in> set (closeI L i) \<and> L ! i \<in> set (closeI L i) \<longrightarrow> set (replaceI L i x) = {x} \<union> set L"
        apply(induction rule: index_list_induct[where P = "(\<lambda>L i. i < length L \<and> L ! i \<in> set (closeI L i) \<and>L ! i \<in> set (closeI L i) \<longrightarrow> set (replaceI L i x) = {x} \<union> set L)"]) 
        subgoal for L  by(induction L,auto)
        subgoal for xa xs i 
          by (metis insert_absorb2 insert_is_Un list.simps(15) mk_disjoint_insert replaceI_closeI_set replaceI_ident)
        apply(auto simp add: i)done
      then show " set (replaceI L i x) = {x} \<union> set L"
        using i s by auto
    qed
    have replace_set_notin:"\<And>i L x. i < length L \<Longrightarrow> L ! i \<notin> set (closeI L i) \<Longrightarrow> set (replaceI L i x) = {x} \<union> (set L - {L ! i})"
    proof - 
      fix i::"nat"  and L::"'a list" and x::"'a"
      assume i:"i < length L"
      assume s:"L ! i \<notin> set (closeI L i)"                        
      have imply:"i < length L \<and> L ! i \<notin> set (closeI L i) \<longrightarrow> set (replaceI L i x) = {x} \<union> (set L - {L ! i})"
        apply(induction rule: index_list_induct[where P = "(\<lambda>L i. i < length L \<and>  L ! i \<notin> set (closeI L i) \<longrightarrow> set (replaceI L i x) = {x} \<union> (set L - {L ! i}))"]) 
        subgoal for L  by(induction L,auto)
        subgoal for xa xs i 
          using insert_absorb2 insert_is_Un list.simps(15) mk_disjoint_insert replaceI_closeI_set replaceI_ident
          by auto
        apply(auto simp add: i)done
      then show "set (replaceI L i x) = {x} \<union> (set L - {L ! i})"
        using i s by auto
    qed
    have memP:"?p \<in> set \<Delta>" using nth_member jD by auto
    have memQ:"?q \<in> set \<Delta>" using nth_member kD by auto
    have set_fml:"\<And>P Q. set P = set Q \<Longrightarrow> (\<nu> \<in> fml_sem I (foldr Or P FF)) =( \<nu> \<in> fml_sem I (foldr Or Q FF))"
      subgoal for P Q
        by (simp add: foldr_fml_sem) done
    have mem_lem:"\<And>L j k x. j \<noteq> k \<Longrightarrow> j < length L \<Longrightarrow> k < length L \<Longrightarrow> (replaceI L j x) ! k = L ! k"
      subgoal for L j k x
      apply(cases "j < k")
    proof -
      assume jk:"j < k"
      assume j:"j < length L"                         
      assume k:"k < length L"                                         
      have imp:"(\<forall>k. j < k \<longrightarrow>  k < length L \<longrightarrow> (replaceI L j x) ! k = L ! k)"
        apply(induction rule: index_list_induct[of "(\<lambda> L j. (\<forall>k. j < k  \<longrightarrow> k < length L \<longrightarrow> (replaceI L j x) ! k = L ! k))"] )
        subgoal for L by (cases L,auto)
        subgoal for xa xs i
          by(auto)
        by (rule j)
      show  "(replaceI L j x) ! k = L ! k" using jk j k imp by auto
    next
      assume neq:"j \<noteq> k"
      assume j:"j < length L"                         
      assume k:"k < length L"                                         
      assume not:"\<not>(j < k)"
      from neq not have jk:"j > k" by auto
      have imp:"(\<forall>j. j > k \<longrightarrow>  k < length L \<longrightarrow> (replaceI L j x) ! k = L ! k)"
        apply(induction rule: index_list_induct[of "(\<lambda> L k. (\<forall>j. j > k  \<longrightarrow> k < length L \<longrightarrow> (replaceI L j x) ! k = L ! k))"] )
        subgoal for L apply(auto) subgoal for j by(cases j,auto,cases L,auto) done 
        subgoal for xa xs i
          apply(auto)
            using Suc_less_eq2 by auto
        by (rule k)
      show  "(replaceI L j x) ! k = L ! k" using jk j k imp by auto
    qed done
  have close_lem:"\<And>L::('a list). \<And>j k::nat. \<And>x::'a. j \<noteq> k \<Longrightarrow> j < length L \<Longrightarrow> k < length L \<Longrightarrow> L ! k  \<in> set (closeI L j)"
      subgoal for L j k x
      apply(cases "j < k")
    proof -
      assume jk:"j < k"
      assume j:"j < length L"              
      assume k:"k < length L"              
      have imp:"(\<forall>k. j < Suc k \<longrightarrow>  Suc k < length L \<longrightarrow> (List.nth L (Suc k) = List.nth (closeI L j) k))"
        apply(induction rule: index_list_induct[of "(\<lambda> L j. (\<forall>k. j < Suc k  \<longrightarrow> (Suc k) < length L \<longrightarrow> (List.nth L (Suc k) = List.nth (closeI L j) k)))"] )
        subgoal for L
          apply(auto) subgoal for k by(cases L,auto) done
        subgoal for xa xs i
          apply(auto) subgoal for k 
            apply(erule allE[where x="k-1"]) 
            by(cases k,auto) done
        by (rule j)
      have closeI_length:"\<And>j. 0 < length L \<Longrightarrow> j < length L \<Longrightarrow> length(closeI L j) = length(L) - 1"
        subgoal for j proof -
          assume L:"0 < length L" assume j:"j < length L"
          have imp:"L \<noteq> [] \<longrightarrow> length(closeI L j) = length(L) - 1"
            apply(induction rule: index_list_induct[of "(\<lambda>L j. L \<noteq> [] \<longrightarrow> length(closeI L j) = length(L) - 1)"])
            subgoal for L by (auto,cases L,auto)
            subgoal for x xs i by(auto)
            by (rule j)
          show "length (closeI L j) = length L - 1" using imp L j by auto
        qed done
      have inst:"length (closeI L j) = length L - 1" using closeI_length[of j] j k jk by (auto,cases L,auto)
      have less:"k - 1 < length (closeI L j)"  using inst j k jk by auto
      show  "L ! k \<in> set (closeI L j)" 
        using jk j k spec[OF imp, of "k-1"] 
          nth_member[of "k-1" "(closeI L j)", OF less]  
          List.member_def[of "(closeI L j)" "L ! k"] by auto
    next
      assume neq:"j \<noteq> k"
      assume j:"j < length L"                         
      assume k:"k < length L"                                         
      assume not:"\<not>(j < k)"
      from neq not have jk:"j > k" by auto
      have imp:"(\<forall>j. j >  k \<longrightarrow> j < length L \<longrightarrow> (List.nth L k = List.nth (closeI L j) k))"
        apply(induction rule: index_list_induct[of "(\<lambda> L k. (\<forall>j. j > k  \<longrightarrow> j < length L \<longrightarrow> (List.nth L k = List.nth (closeI L j) k)))"] )
        subgoal for L
          apply(auto) subgoal for j 
            by(cases L,auto,cases j,auto) done
        subgoal for xa xs i
          apply(auto) subgoal for k 
            apply(erule allE[where x="k-1"]) 
            by(cases k,auto) done
        by (rule k)
      have closeI_length:"\<And>j. 0 < length L \<Longrightarrow> j < length L \<Longrightarrow> length(closeI L j) = length(L) - 1"
        subgoal for j proof -
          assume L:"0 < length L" assume j:"j < length L"
          have imp:"L \<noteq> [] \<longrightarrow> length(closeI L j) = length(L) - 1"
            apply(induction rule: index_list_induct[of "(\<lambda>L j. L \<noteq> [] \<longrightarrow> length(closeI L j) = length(L) - 1)"])
            subgoal for L by (auto,cases L,auto)
            subgoal for x xs i by(auto)
            by (rule j)
          show "length (closeI L j) = length L - 1" using imp L j by auto
        qed done
      have inst:"length (closeI L j) = length L - 1" using closeI_length[of j] j k jk by (auto,cases L,auto)
      have less:"k  < length (closeI L j)"  using inst j k jk by auto
      show  "L ! k \<in> set (closeI L j)" 
        using jk j k spec[OF imp, of "j"] 
          nth_member[of "k" "(closeI L j)", OF less]  
          List.member_def[of "(closeI L j)" "L ! k"] by auto
    qed done
    have rep_up_lem:"\<And>L i x. i < length L \<Longrightarrow> (replaceI L i x) ! i = x" 
    proof -
      fix L i x 
      assume i:"i < length L"
      have imp:"(i < length L \<Longrightarrow> (replaceI L i x) ! i = x)"
        apply(rule index_list_induct[of "(\<lambda> L i. (replaceI L i x) ! i = x)"])
        subgoal for La using j by(cases La,auto simp add:  member_rec)
        subgoal for xa xs i
          by(auto simp add: j member_rec )
        using i by auto
      then show " replaceI L i x ! i = x "
        using i by auto
    qed
    have atK:"(replaceI \<Delta> j ?q) ! k = \<Delta> ! k" 
      using mem_lem[OF jk jD kD] by auto
    have atJ:"(replaceI \<Delta> j ?q) ! j = \<Delta> ! k" using rep_up_lem[OF jD] by auto
    have preMem:"((replaceI \<Delta> j ?q) ! j) \<in> set (closeI (replaceI \<Delta> j ?q) k)"  
      apply(rule close_lem) using jk kRep jRep by auto
    have mem:"(replaceI \<Delta> j ?q) ! k \<in> set (closeI (replaceI \<Delta> j ?q) k)"
      using atK atJ preMem by auto
    have e1:"set (replaceI (replaceI \<Delta> j ?q) k ?p)
        = {?p} \<union> set (replaceI \<Delta> j ?q)"
      using replace_set_in[OF kRep mem, of ?p] by auto
    have set_eq:"set (replaceI (replaceI \<Delta> j ?q) k ?p) = (set \<Delta>)"
        apply(cases "\<Delta> ! j \<in> set (closeI \<Delta> j)")
      proof -      
        assume elem:" \<Delta> ! j \<in> set (closeI \<Delta> j)"
        have e2:"{?p} \<union> set (replaceI \<Delta> j ?q) = {?p} \<union> {?q} \<union> set \<Delta>"
          using replace_set_in[of j, OF jD, of ?q, OF elem] by auto
        have e3:"... = set \<Delta>" using memP memQ by auto
        then show ?thesis
          using e1 e2 e3 by auto
      next 
        assume elem:" \<Delta> ! j \<notin> set (closeI \<Delta> j)"
        have e2:"{?p} \<union> set (replaceI \<Delta> j ?q) = {?p} \<union> {?q} \<union> set \<Delta>"
          using replace_set_notin[of j, OF jD, of ?q, OF elem] by auto
        have e3:"... = set \<Delta>" using memP memQ by auto
        then show ?thesis
          using e1 e2 e3 by auto
      qed
     have same_sem:"(\<nu> \<in> fml_sem I (foldr Or (replaceI (replaceI \<Delta> j ?q) k ?p) FF)) =
               (\<nu> \<in> fml_sem I (foldr Or \<Delta> FF))"
       apply(rule set_fml)
       by(rule set_eq)
    then show " \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using seq_MP[OF sg0 ante] by auto
     qed
  then show ?thesis using some SG_dec rres by auto

next 
  case OrR then have L:"L = OrR" by auto
  obtain p q where eq:"(snd (SG ! i) ! j) = (p || q)" 
    using some L apply(cases "SG ! i",auto simp add: Or_def) subgoal for a b 
      apply(cases "b ! j", auto simp add: Or_def)
      subgoal for x3 apply(cases x3,auto) subgoal for x41 x42 apply(cases x41,auto) subgoal for x3a by(cases x42,auto) done done done
  done
  have andL_simp:"\<And>AI SI SS p q.
   (nth SI j) = Or p q \<Longrightarrow>
   (AI,SI) = SS \<Longrightarrow>
   RightRule_result OrR j SS = Some [(AI, ((closeI SI j) @ [p, q]))]" 
    subgoal for AI SI SS p q by(cases SS, auto simp add: Implies_def Or_def) done
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)" by (metis seq2fml.cases)
  have res_eq:"RightRule_result OrR j (SG ! i) = Some [(\<Gamma>, (closeI \<Delta> j) @ [p, q])]" 
    apply(rule andL_simp)
    using SG_dec eq by (metis sndI)+
  have rres:"rres = [(\<Gamma>, (closeI \<Delta> j) @ [p, q])]" using some res_eq L by auto
  have AIjeq:"\<Delta> ! j = (p || q)" using SG_dec eq unfolding Implies_def Or_def by (metis snd_conv)
  have jG:"j < length \<Delta>" using j SG_dec by(cases "SG ! i", auto)
  have big_sound:"sound  ([(\<Gamma>, (closeI \<Delta> j) @ [p, q])], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I::"interp" and \<nu>::"state"
    assume good:"is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(\<Gamma>, (closeI \<Delta> j) @ [p, q])] \<Longrightarrow> \<nu> \<in> seq_sem I ([(\<Gamma>, (closeI \<Delta> j) @ [p, q])] ! i))"
    assume ante:"\<nu> \<in> fml_sem I (foldr And \<Gamma> TT)"
    have sg1:"\<nu> \<in> seq_sem I (\<Gamma>, (closeI \<Delta> j) @ [p, q])" using sgs[of 0] by auto
    have duh:"\<And>S T x. x \<in> S \<Longrightarrow> S = T \<Longrightarrow> x \<in> T" by auto
    have succ1:"\<nu> \<in> fml_sem I (foldr Or ((closeI \<Delta> j) @ [p, q]) FF)"
      using  seq_MP[OF sg1 ante] by auto
    then have succ2:"\<nu> \<in> fml_sem I (foldr Or (((closeI \<Delta> j) @ [p]) @ [ q]) FF)"
      by auto
    then have succ3:"\<nu> \<in> fml_sem I (foldr Or (q # p # (closeI \<Delta> j)) FF)"
      using snoc_assoc_disj[of I "((closeI \<Delta> j) @ [p])" q]
        snoc_assoc_disj[of I "(closeI \<Delta> j)" p]  
      by auto
    then have succ4:"\<nu> \<in> fml_sem I (foldr Or ((nth \<Delta> j) # (closeI \<Delta> j)) FF)"
      using AIjeq by auto
    then have succ5:"\<nu> \<in> fml_sem I (foldr Or \<Delta> FF)"
      using closeI_ident_disj[OF jG , of "\<Delta> ! j", of I, OF refl ] by auto
    show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" using succ5 sg1 ante by auto
  qed
  then show ?thesis using some SG_dec rres by auto
qed


lemma list_mem_closeI:
  fixes L::"'a list" and x::"'a"
  assumes mem:"List.member L x"
  assumes j:"j < length L"
  shows "List.member ((nth L j)#(closeI L j)) x"
proof -
  have imp:"(j < length L \<Longrightarrow> (List.member L x \<longrightarrow> List.member ((nth L j)#(closeI L j)) x))"
    apply(rule index_list_induct[of "(\<lambda> L j. List.member L x \<longrightarrow> List.member ((nth L j)#(closeI L j)) x)"])
    subgoal for La using j by(cases La,auto simp add:  member_rec)
    by(auto simp add: j mem member_rec )
  then show ?thesis using mem j by(auto simp add: mem j member_rec)
qed

lemma list_mem_replaceI:
  fixes L::"'a list" and x::"'a"
  assumes j:"j < length L"
  shows "List.member (replaceI L j x) x"
proof -
  have imp:"(j < length L \<Longrightarrow> (List.member (replaceI L j x) x))"
    apply(rule index_list_induct[of "(\<lambda> L j. (List.member (replaceI L j x) x))"])
    subgoal for La using j by(cases La,auto simp add:  member_rec)
    by(auto simp add: j member_rec )
  then show ?thesis using  j by(auto simp add:  j member_rec)
qed

lemma list_mem_replaceI_closeI:
  fixes L::"'a list" and x::"'a"
  assumes j:"j < length L"
  assumes close:"List.member (closeI L j ) y"
  shows "List.member (replaceI L j x) y"
proof -
  have imp:"(j < length L \<Longrightarrow> (List.member (closeI L j) y \<longrightarrow> (List.member (replaceI L j x) y)))"
    apply(rule index_list_induct[of "(\<lambda> L j. List.member (closeI L j) y \<longrightarrow> (List.member (replaceI L j x) y))"])
    subgoal for La using j by(cases La,auto simp add:  member_rec)
    by(auto simp add: j member_rec )
  then show ?thesis using j close by(auto simp add:  j member_rec)
qed


lemma core_rule_sound:
  fixes R1 R2 :: "rule" and RA :: " ruleApp" and n :: nat
  assumes sound:"sound R1"
  assumes i:"i < length (fst R1)"
  assumes some:"rule_result R1 (i,RA) = Some R2"
  shows "sound R2"
  apply(cases R1)
  apply(cases RA)
  (* urename *)
  subgoal for P A S what repl using sound some i using sound some apply (cases "FRadmit (seq2fml (P ! i)) \<and> FRadmit (seq2fml (SUrename what repl (P ! i))) \<and> fsafe (seq2fml (SUrename what repl (P ! i)))", auto)
  proof (rule soundI_mem, simp)
    fix I::"interp"
    assume sound:"sound (P, A, S)"
    assume i:"i < length P"
    assume good_interp:"is_interp I"
    assume mem:"(\<And>\<phi>. List.member (replaceI P i (SUrename what repl (P ! i))) \<phi> \<Longrightarrow> fml_sem I (seq2fml \<phi>) = UNIV)"
    assume fradmit:"FRadmit (seq2fml ( (P ! i)))"
    assume fradmit2:"FRadmit (seq2fml (SUrename what repl (P ! i)))"
    assume fsafe:"fsafe (seq2fml (SUrename what repl (P ! i)))"

    have mem1:"(\<And>\<phi>. List.member ((SUrename what repl (P ! i)) # closeI P i ) \<phi> \<Longrightarrow> fml_sem I (seq2fml \<phi>) = UNIV)"
      apply(rule mem)
      apply(auto simp add: member_rec)
      subgoal for v vv
        apply(rule list_mem_replaceI) by(auto simp add: i)
      subgoal for v vv  
        apply(rule list_mem_replaceI_closeI) by(auto simp add: i)
      done
    have memL:"fml_sem I (seq2fml (SUrename what repl (P ! i))) = UNIV"
      apply(rule mem1) by(auto simp add: member_rec)
    then have memL2:"\<And>\<nu>. \<nu> \<in> fml_sem I (seq2fml (SUrename what repl (P ! i)))"
      by(auto simp add: valid_def)
    have memL3:"\<And>\<nu>. \<nu> \<in> fml_sem I (FUrename what repl (seq2fml (SUrename what repl (P ! i))))"
      apply(rule URename_local_sound[OF good_interp, of "(seq2fml (SUrename what repl (P ! i)))"])
      subgoal using fradmit2 by auto
      subgoal using fsafe by auto
      using memL2 by auto
    then have memL4:"\<And>\<nu>. \<nu> \<in> fml_sem I (FUrename what repl  (FUrename what repl (seq2fml(P ! i))))"
      using SUrename_FUrename by auto
    then have memL5:"\<And>\<nu>. \<nu> \<in> fml_sem I  (seq2fml(P ! i))"
      using FUrename_cancel[of "(seq2fml(P ! i))"] fradmit by(auto)
    have memR:"(\<And>\<phi>. List.member (closeI P i ) \<phi> \<Longrightarrow> fml_sem I (seq2fml \<phi>) = UNIV)"
      apply(rule mem1) by(auto simp add: member_rec)
    have midMem:"(\<And>\<phi>. List.member (P ! i # closeI P i) \<phi> \<Longrightarrow> fml_sem I (seq2fml \<phi>) = UNIV)"
      apply(auto simp add: member_rec)
      subgoal for A S v vv using memL5 by auto
      subgoal for A S v vv using memR[of "(A,S)"] by auto 
      done
    have bigMem:"(\<And>\<phi>. List.member (P) \<phi> \<Longrightarrow> fml_sem I (seq2fml \<phi>) = UNIV)"
      apply(rule midMem)
      apply(rule list_mem_closeI)
      by(auto simp add: i)
    show "fml_sem I (foldr (&&) A TT \<rightarrow> foldr (||) S FF) = UNIV"
      using soundE_mem[OF sound good_interp] bigMem by(auto)
  qed
  (* rrule *)
  subgoal for P A S R m using sound some apply auto
    apply(cases "length (snd (P ! i)) \<le> m", auto)
    apply(cases "RightRule_result R m (P ! i)",auto)
    apply(rule merge_rules_sound)
        apply(auto)
    subgoal for a
      apply(cases R2)
      subgoal for P1 A1 S1
      apply(rule rrule_sound[of R m P i a])
        using i sound some by(auto simp add: sound i some)
      done
    subgoal for a
      apply(cases R2)
      subgoal for P1 A1 S1
      using i sound some by(auto simp add: sound i some)
      done
    done
  (* lrule *)
  subgoal for P A S R m using sound some apply auto
    apply(cases "length (fst (P ! i)) \<le> m", auto)
    apply(cases "LeftRule_result R m (P ! i)",auto)
    apply(rule merge_rules_sound)
  apply(auto)
    subgoal for a
      apply(cases R2)
      subgoal for P1 A1 S1
      apply(rule lrule_sound[of R m P i a])
        using i sound some by(auto simp add: sound i some)
      done
    subgoal for a
      apply(cases R2)
      subgoal for P1 A1 S1
      using i sound some by(auto simp add: sound i some)
      done
    done
  (* closeid *)
  subgoal for SG A S j k using sound some apply auto
    apply(cases "j < length (fst (SG ! i)) \<and> k < length (snd (SG ! i)) \<and> fst (SG ! i) ! j = snd (SG ! i) ! k",auto)
  proof -
    let ?C = "(A,S)"
    assume PAS:"R1 = (SG, A, S)"
    assume RA:"RA = CloseId j k"
    assume sound:"sound (SG, A, S)"
    assume R2:"R2 = (closeI SG i, A, S)"
    have ii:"i < length SG" using i PAS by auto
    assume jL:"j < length (fst (SG ! i))"
    assume kL:"k < length (snd (SG ! i))"
    assume match:"fst (SG ! i) ! j = snd (SG ! i) ! k"
    obtain \<Gamma> \<Delta> where SG_dec:"(\<Gamma>, \<Delta>) = SG ! i" 
      using prod.collapse by blast
    have j\<Gamma>:"j < length \<Gamma>"
      using SG_dec jL
      by (metis fst_conv)
    have k\<Delta>:"k < length \<Delta>"
      using SG_dec kL
      by (metis snd_conv)
    have "\<And>I \<nu>. is_interp I \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
    proof -
      fix I::"interp" and \<nu>::"state"
      assume good:"is_interp I"
      assume \<Gamma>_sem:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
      have mem:"List.member \<Gamma> (\<Gamma> ! j)"
        using j\<Gamma> nth_member by blast
      have mem2:"List.member \<Delta> (\<Delta> ! k)"
        using k\<Delta> nth_member by blast
      have "\<nu> \<in> fml_sem I (\<Gamma> ! j)"
        using \<Gamma>_sem mem
        using and_foldl_sem by blast
      then have "\<nu> \<in> fml_sem I (\<Delta> ! k)"
        using match SG_dec
        by (metis fst_conv snd_conv)
      then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
        using mem2
        using or_foldl_sem by blast
    qed
    then have seq_valid:"seq_valid (SG ! i)"
    unfolding seq_valid_def using SG_dec
    by (metis UNIV_eq_I seq_semI')
  then show " sound (closeI SG i, A, S)" 
    using closeI_valid_sound[OF ii sound seq_valid] by simp
  qed
  (* cohide2 *)
  subgoal for SG A S j k  using sound some apply auto
    apply(cases "length (fst (SG ! i)) \<le> j \<or> length (snd (SG ! i)) \<le> k", auto)
    apply(cases "i < length SG",auto)
  proof (rule soundI_mem, cases "SG ! i", simp)
    fix I::"interp" and \<Gamma> \<Delta>::"formula list"
    assume R1:"R1 = (SG, A, S)"
    assume RA:"RA = Cohide2 j k"
    assume sound:"sound (SG, A, S)"
    assume "\<not> length \<Gamma> \<le> j" then have j:"j < length \<Gamma>" by auto
    assume "\<not> length \<Delta> \<le> k" then have  k:"k < length \<Delta>" by auto
    assume i:"i < length SG"
    assume R2:" R2 = (replaceI SG i ([nth \<Gamma> j], [nth \<Delta> k]), A, S)"
    assume good_interp:"is_interp I"
    assume "(\<And>\<phi>. List.member (replaceI SG i ([\<Gamma> ! j], [\<Delta> ! k])) \<phi> \<Longrightarrow> fml_sem I (seq2fml \<phi>) = UNIV)" 
    then have mem:"(\<And>\<phi>. List.member (replaceI SG i ([\<Gamma> ! j], [\<Delta> ! k])) \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)" by auto
    assume SG_dec:"SG ! i = (\<Gamma>, \<Delta>)"
    have rep_mem_seq_sem:"seq_sem I ([fst (SG ! i) ! j], [snd (SG ! i) ! k]) = UNIV"
      apply(rule mem)
      using SG_dec apply(auto)
      apply(rule list_mem_replaceI)
      using i by auto
    have rep_close_seq_sem:"\<And>\<phi>. List.member (closeI SG i) \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV"
      apply(rule mem)         
      apply(rule list_mem_replaceI_closeI)
      by(auto simp add: i)
    have seq_imp:"\<And>\<nu>. \<nu> \<in> seq_sem I ([fst (SG ! i) ! j], [snd (SG ! i) ! k]) \<Longrightarrow>  \<nu> \<in> seq_sem I (SG ! i)" 
    proof -
      fix \<nu>
      assume sem:"\<nu> \<in> seq_sem I ([fst (SG ! i) ! j], [snd (SG ! i) ! k])"
      then have sem1:"\<nu> \<in> seq_sem I ([\<Gamma> ! j], [\<Delta> ! k])" using SG_dec by auto
      then have sem2:"\<nu> \<in> seq_sem I ((\<Gamma> ! j) # (closeI \<Gamma> j), (\<Delta> ! k) # (closeI \<Delta> k))" by auto
      then have sem3:"\<nu> \<in> seq_sem I (\<Gamma>, \<Delta>)" 
        using closeI_ident_conj[OF j refl, of I ] closeI_ident_disj[OF k refl, of I ] by auto
      then show "\<nu> \<in> seq_sem I (SG ! i)"
        using SG_dec by auto
    qed  
    then have seq_imp_univ:"seq_sem I ([fst (SG ! i) ! j], [snd (SG ! i) ! k]) = UNIV \<Longrightarrow> seq_sem I (SG ! i) = UNIV" by auto
    have "(\<And>\<phi>. List.member (([fst (SG ! i) ! j], [snd (SG ! i) ! k]) # closeI SG i) \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)" 
      apply(auto simp add: member_rec)
      subgoal for a b using seq_imp_univ rep_mem_seq_sem by auto
      subgoal for A S v vv
        using rep_close_seq_sem[of "(A,S)"] by(auto)
      done
    have close_univ:"(\<And>\<phi>. List.member ((nth SG i) # closeI SG i) \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)" 
      apply(auto simp add: member_rec) 
      subgoal for A S v vv using seq_imp_univ rep_mem_seq_sem by auto
      subgoal for A S v vv using rep_close_seq_sem[of "(A,S)"] by(auto)
      done
    have "(\<And>\<phi>. List.member SG \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)" 
      apply(rule close_univ)
      apply(rule list_mem_closeI)
      by(auto simp add: i)
    then show" fml_sem I (foldr (&&) A TT \<rightarrow> foldr (||) S FF) = UNIV" 
      using soundE_mem[OF sound good_interp] by auto
  qed
  (* cut *)
   subgoal for SG A S cutFml  using sound some apply (auto, cases " SG ! i",auto)
     subgoal for \<Gamma> \<Delta>
     proof ( cases "fsafe cutFml",auto, cases "i < length SG",auto)
       let ?C = "(A,S)"
       assume R1:" R1 = (SG, A, S)"
       assume SG_dec:"SG ! i = (\<Gamma>,\<Delta>)"
       assume iSG:"i < length SG"
       assume safe:"fsafe cutFml"
       assume sound:"sound (SG, ?C)"
       assume R2:"R2 = (replaceI SG i (\<Gamma> @ [cutFml], \<Delta>) @ [(\<Gamma>, \<Delta> @ [cutFml])], A, S)"
       have "sound (replaceI SG i (\<Gamma> @ [cutFml], \<Delta>) @ [(\<Gamma>, \<Delta> @ [cutFml])], A, S)"
         apply(rule soundI_memv)
       proof -
         have assoc_mem_cons:"\<And>x::'a. \<And>y::'a. \<And>L::'a list. List.member (y#L) x \<Longrightarrow> List.member (L@[y]) x" 
           subgoal for x y L 
             by(induction L,auto simp add: member_rec) done
         have closeI_replace_mem:"\<And>x::'a. \<And>y::'a. \<And>i::nat. \<And>L::'a list. i < length L \<Longrightarrow> List.member (replaceI L i y) x \<Longrightarrow> List.member (y # closeI L i) x" 
         proof -
           fix x y :: 'a and i::nat and L::"'a list"
           assume mem:"List.member (replaceI L i y) x"
           assume i:"i < length L"
           have imp:"i < length L \<Longrightarrow> (List.member (replaceI L i y) x \<longrightarrow> List.member (y # closeI L i) x)"
             apply(rule index_list_induct[of "(\<lambda> L i. List.member (replaceI L i y) x \<longrightarrow> List.member (y # closeI L i) x)"])
             subgoal for La by(cases La,auto) 
             using i by (auto simp add: member_rec)
           then show " List.member (y # closeI L i) x" using i mem by auto
         qed 
         have replace_closeI_mem:"\<And>x::'a. \<And>y::'a. \<And>i::nat. \<And>L::'a list. i < length L \<Longrightarrow> List.member (y # closeI L i) x \<Longrightarrow> List.member (replaceI L i y) x" 
         proof -
           fix x y :: 'a and i::nat and L::"'a list"
           assume mem:"List.member (y # closeI L i) x"
           assume i:"i < length L"
           have imp:"i < length L \<Longrightarrow> (List.member (y # closeI L i) x) \<longrightarrow> (List.member (replaceI L i y) x)"
             apply(rule index_list_induct[of "(\<lambda> L i. List.member (y # closeI L i) x \<longrightarrow> List.member (replaceI L i y) x)"])
             subgoal for La by(cases La,auto) 
             using i by (auto simp add: member_rec)
           then show "List.member (replaceI L i y) x" using i mem by auto
         qed 

         fix I::"interp" and \<nu>::"state"
         assume good:"is_interp I"
         assume sgs:"(\<And>\<phi>' \<nu>. List.member (replaceI SG i (\<Gamma> @ [cutFml], \<Delta>) @ [(\<Gamma>, \<Delta> @ [cutFml])]) \<phi>' \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>')"
         then have sgs1:"(\<And>\<phi>' \<nu>. List.member ((\<Gamma>, \<Delta> @ [cutFml]) # replaceI SG i (\<Gamma> @ [cutFml], \<Delta>) ) \<phi>' \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>')"
           using assoc_mem_cons[of "(\<Gamma>, \<Delta> @ [cutFml])" "replaceI SG i (\<Gamma> @ [cutFml], \<Delta>)"]
           by(auto)
         have sgs2:"(\<And>\<phi>' \<nu>. List.member ((\<Gamma>, \<Delta> @ [cutFml]) # (\<Gamma> @ [cutFml], \<Delta>) # closeI SG i  ) \<phi>' \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>')"
         proof -
           fix \<phi>' \<nu>
           assume mem:"List.member ((\<Gamma>, \<Delta> @ [cutFml]) # (\<Gamma> @ [cutFml], \<Delta>) # closeI SG i) \<phi>'"
           then have mem_or:"\<phi>' = (\<Gamma>, \<Delta> @ [cutFml]) \<or> List.member ((\<Gamma> @ [cutFml], \<Delta>) # closeI SG i) \<phi>'"
             by(auto simp add: member_rec)
           show "\<nu> \<in> seq_sem I \<phi>'"
             apply(rule disjE[OF mem_or])
             subgoal by(rule sgs1,auto simp add: member_rec)
           proof -
             assume mem2:"List.member ((\<Gamma> @ [cutFml], \<Delta>) # closeI SG i) \<phi>'"
             have "List.member (replaceI SG i (\<Gamma> @ [cutFml], \<Delta>)) \<phi>'"
               using replace_closeI_mem[of i SG "(\<Gamma> @ [cutFml], \<Delta>)" \<phi>', OF iSG] mem2 by auto
             then have mem3:"List.member ((\<Gamma>, \<Delta> @ [cutFml]) # replaceI SG i (\<Gamma> @ [cutFml], \<Delta>)) \<phi>'" by(auto simp add: member_rec)
             then show "\<nu> \<in> seq_sem I \<phi>' " using sgs1 by auto
           qed
         qed 
         have sgL:"\<And>\<nu>. \<nu> \<in> seq_sem I (\<Gamma> @ [cutFml], \<Delta>)" 
           apply(rule sgs2)
           by(auto simp add: member_rec)
         have sgR:"\<And>\<nu>. \<nu> \<in> seq_sem I (\<Gamma>, \<Delta> @ [cutFml])"
           apply(rule sgs2)
           by(auto simp add: member_rec)
         have sg1:"\<And>\<nu>. \<nu> \<in> seq_sem I (cutFml # \<Gamma>, \<Delta>)" 
           subgoal for \<nu>
             using sgL[of \<nu>] snoc_assoc_conj[of I \<Gamma> cutFml] by auto done
         have sg2:"\<And>\<nu>. \<nu> \<in> seq_sem I (\<Gamma>, cutFml # \<Delta>)" 
           subgoal for \<nu>
             using sgR[of \<nu>] snoc_assoc_disj[of I \<Delta> cutFml] by auto done
         have sgs:"\<And>\<phi> \<nu>. (List.member (closeI SG i) \<phi>) \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>"
           apply(rule sgs2) by (simp add: member_rec(1))
         have sgNew:"\<And>\<nu>. \<nu> \<in> seq_sem I (\<Gamma>, \<Delta>)"
           using sg1 sg2 by auto
         have same_mem:"\<And>x. List.member SG x \<Longrightarrow> List.member ((\<Gamma>,\<Delta>) # closeI SG i) x"
         proof - 
           fix x
           assume mem:"List.member SG x"
           have len:"i < length SG"
             using i R1 by auto
           show "List.member ((\<Gamma>,\<Delta>) # closeI SG i) x"
             using list_mem_closeI[OF mem len] SG_dec by auto 
         qed
         have SGS:"(\<And>\<phi>' \<nu>. List.member SG \<phi>' \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>')"
           using sgNew sgs same_mem member_rec(1) seq_MP
           by metis
         show "\<nu> \<in> seq_sem I ?C"
           using sound apply simp
           apply(drule soundD_memv)
             apply(rule good)
           subgoal for \<phi> \<nu> using SGS 
             by auto
           by auto
       qed
       then show "sound (replaceI SG i (\<Gamma> @ [cutFml], \<Delta>) @ [(\<Gamma>, \<Delta> @ [cutFml])], A, S)" 
         by(auto)
qed
  done
(* DIGeqSchema*)
  subgoal for SG A S ODE T1 T2 using sound some apply auto
    apply(cases "([], [(DPredl Ix \<rightarrow> (Geq T1 T2 && [[EvolveODE ODE (DPredl Ix)]]Geq (Differential T1) (Differential T2))) \<rightarrow>
              [[EvolveODE ODE (DPredl Ix)]]Geq T1 T2]) =
        SG ! i \<and>
  osafe ODE \<and>
  dfree T1 \<and>
  dfree T2 \<and>
  FVT T1 \<subseteq> Inl ` ODE_dom ODE \<and>
  FVT T2 \<subseteq> Inl ` ODE_dom ODE", auto)
  proof -
    let ?C = "(A,S)"
    assume PAS:"R1 = (SG, ?C)"
    assume RA:"RA = DIGeqSchema ODE T1 T2"
    assume sound:"sound (SG, A, S)"
    assume R2:"R2 = (closeI SG i, A, S)"
    assume osafe:"osafe ODE"
    assume free1:"dfree T1"
    assume free2:"dfree T2"
    assume BVO1:"FVT T1 \<subseteq> Inl ` ODE_dom ODE"
    assume BVO2:"FVT T2 \<subseteq> Inl ` ODE_dom ODE"
    have ii:"i < length SG" using i PAS by auto
    assume seq_eq:"([], [(DPredl Ix \<rightarrow> (Geq T1 T2 && [[EvolveODE ODE (DPredl Ix)]]Geq (Differential T1) (Differential T2))) \<rightarrow>
          [[EvolveODE ODE (DPredl Ix)]]Geq T1 T2]) = SG ! i"
    obtain \<Gamma> \<Delta> where SG_dec:"(\<Gamma>, \<Delta>) = SG ! i" 
      using prod.collapse by blast
    have fml_to_seq:"\<And>\<phi>. valid \<phi> \<Longrightarrow> seq_valid ([],[\<phi>])"
      by(auto simp add: seq_valid_def valid_def)
    have val:"valid ((DPredl vid1 \<rightarrow> (Geq T1 T2 && [[EvolveODE ODE (DPredl Ix)]]Geq (Differential T1) (Differential T2))) \<rightarrow>
        [[EvolveODE ODE (DPredl vid1)]]Geq T1 T2)"
      using DIGeq_valid[OF osafe free1 free2 BVO1 BVO2] 
      unfolding DIGeqaxiom_def
      by auto
    then have sval:"seq_valid ([],[(DPredl vid1 \<rightarrow> (Geq T1 T2 && [[EvolveODE ODE (DPredl vid1)]]Geq (Differential T1) (Differential T2))) \<rightarrow>
        [[EvolveODE ODE (DPredl vid1)]]Geq T1 T2])"
      using fml_to_seq[OF val] by auto
 show " sound (closeI SG i, A, S)" 
   using closeI_valid_sound[OF ii sound ] sval seq_eq by simp
qed 
  subgoal for SG A S ODE T1 T2 using sound some apply auto
    apply(cases "([], [(DPredl Ix \<rightarrow> (Greater T1 T2 && [[EvolveODE ODE (DPredl Ix)]]Geq (Differential T1) (Differential T2))) \<rightarrow>
              [[EvolveODE ODE (DPredl Ix)]]Greater T1 T2]) =
        SG ! i \<and>
  osafe ODE \<and>
  dfree T1 \<and>
  dfree T2 \<and>
  FVT T1 \<subseteq> Inl ` ODE_dom ODE \<and>
  FVT T2 \<subseteq> Inl ` ODE_dom ODE", auto)
  proof -
    let ?C = "(A,S)"
    assume PAS:"R1 = (SG, ?C)"
    assume RA:"RA = DIGrSchema ODE T1 T2"
    assume sound:"sound (SG, A, S)"
    assume R2:"R2 = (closeI SG i, A, S)"
    assume osafe:"osafe ODE"
    assume free1:"dfree T1"
    assume free2:"dfree T2"
    assume BVO1:"FVT T1 \<subseteq> Inl ` ODE_dom ODE"
    assume BVO2:"FVT T2 \<subseteq> Inl ` ODE_dom ODE"
    have ii:"i < length SG" using i PAS by auto
    assume seq_eq:"([], [(DPredl Ix \<rightarrow> (Greater T1 T2 && [[EvolveODE ODE (DPredl Ix)]]Geq (Differential T1) (Differential T2))) \<rightarrow>
          [[EvolveODE ODE (DPredl Ix)]]Greater T1 T2]) = SG ! i"
    obtain \<Gamma> \<Delta> where SG_dec:"(\<Gamma>, \<Delta>) = SG ! i" 
      using prod.collapse by blast
    have fml_to_seq:"\<And>\<phi>. valid \<phi> \<Longrightarrow> seq_valid ([],[\<phi>])"
      by(auto simp add: seq_valid_def valid_def)
    have val:"valid ((DPredl vid1 \<rightarrow> (Greater T1 T2 && [[EvolveODE ODE (DPredl vid1)]]Geq (Differential T1) (Differential T2))) \<rightarrow>
        [[EvolveODE ODE (DPredl vid1)]]Greater T1 T2)"
      using DIGr_valid[OF osafe free1 free2 BVO1 BVO2] 
      unfolding DIGraxiom_def
      by auto
    then have sval:"seq_valid ([],[(DPredl vid1 \<rightarrow> (Greater T1 T2 && [[EvolveODE ODE (DPredl vid1)]]Geq (Differential T1) (Differential T2))) \<rightarrow>
        [[EvolveODE ODE (DPredl vid1)]]Greater T1 T2])"
      using fml_to_seq[OF val] by auto
 show " sound (closeI SG i, A, S)" 
    using closeI_valid_sound[OF ii sound ] sval seq_eq by simp
qed
  subgoal for SG A S ODE T1 T2 using sound some apply auto
    apply(cases "([], [(DPredl Ix \<rightarrow> (Equals T1 T2 && [[EvolveODE ODE (DPredl Ix)]]Equals (Differential T1) (Differential T2))) \<rightarrow>
              [[EvolveODE ODE (DPredl Ix)]]Equals T1 T2]) =
        SG ! i \<and>
  osafe ODE \<and>
  dfree T1 \<and>
  dfree T2 \<and>
  FVT T1 \<subseteq> Inl ` ODE_dom ODE \<and>
  FVT T2 \<subseteq> Inl ` ODE_dom ODE", auto)
  proof -
    let ?C = "(A,S)"
    assume PAS:"R1 = (SG, ?C)"
    assume RA:"RA = DIEqSchema ODE T1 T2"
    assume sound:"sound (SG, A, S)"
    assume R2:"R2 = (closeI SG i, A, S)"
    assume osafe:"osafe ODE"
    assume free1:"dfree T1"
    assume free2:"dfree T2"
    assume BVO1:"FVT T1 \<subseteq> Inl ` ODE_dom ODE"
    assume BVO2:"FVT T2 \<subseteq> Inl ` ODE_dom ODE"
    have ii:"i < length SG" using i PAS by auto
    assume seq_eq:"([], [(DPredl Ix \<rightarrow> (Equals T1 T2 && [[EvolveODE ODE (DPredl Ix)]]Equals (Differential T1) (Differential T2))) \<rightarrow>
          [[EvolveODE ODE (DPredl Ix)]]Equals T1 T2]) = SG ! i"
    obtain \<Gamma> \<Delta> where SG_dec:"(\<Gamma>, \<Delta>) = SG ! i" 
      using prod.collapse by blast
    have fml_to_seq:"\<And>\<phi>. valid \<phi> \<Longrightarrow> seq_valid ([],[\<phi>])"
      by(auto simp add: seq_valid_def valid_def)
    have val:"valid ((DPredl vid1 \<rightarrow> (Equals T1 T2 && [[EvolveODE ODE (DPredl Ix)]]Equals (Differential T1) (Differential T2))) \<rightarrow>
        [[EvolveODE ODE (DPredl Ix)]]Equals T1 T2)"
      using DIEq_valid[OF osafe free1 free2 BVO1 BVO2] 
      unfolding DIEqaxiom_def
      by auto
    then have sval:"seq_valid ([],[(DPredl Ix \<rightarrow> (Equals T1 T2 && [[EvolveODE ODE (DPredl Ix)]]Equals (Differential T1) (Differential T2))) \<rightarrow>
        [[EvolveODE ODE (DPredl Ix)]]Equals T1 T2])"
      using fml_to_seq[OF val] by auto
 show " sound (closeI SG i, A, S)" 
    using closeI_valid_sound[OF ii sound ] sval seq_eq by simp
qed

  done

inductive QEs_hold::"pt \<Rightarrow> bool"
where "valid f \<Longrightarrow> QEs_hold (FOLRConstant f)"
| "QEs_hold pt \<Longrightarrow> QEs_hold (RuleApplication pt ra i)"
| "QEs_hold (AxiomaticRule a)"
| "QEs_hold pt \<Longrightarrow> QEs_hold (PrUSubst pt \<sigma>)"
| "QEs_hold (Ax axiom)"
| "QEs_hold pt \<Longrightarrow> QEs_hold (FNC pt seq ra)"
| "QEs_hold pt1 \<Longrightarrow> QEs_hold pt2 \<Longrightarrow> QEs_hold (Pro pt1 pt2)"
| "QEs_hold (Start seq)"
| "QEs_hold pt1 \<Longrightarrow> QEs_hold pt2 \<Longrightarrow> QEs_hold (Sub pt1 pt2 i)"

inductive_simps   
    qe_folr[simp]: "QEs_hold (FOLRConstant f)"
and qe_ra[simp]: "QEs_hold (RuleApplication pt ra i)"
and qe_axrule[simp]: "QEs_hold (AxiomaticRule a)"
and qe_subst[simp]: "QEs_hold (PrUSubst pt \<sigma>)"
and qe_ax[simp]: "QEs_hold (Ax axiom)"
and qe_fnc[simp]: "QEs_hold (FNC pt seq ra)"
and qe_pro[simp]: "QEs_hold (Pro pt1 pt2)"
and qe_start[simp]: "QEs_hold (Start seq)"
and qe_sub[simp]: "QEs_hold (Sub pt1 pt2 i)"


lemma sound_valid:
  assumes sound: "sound ([], C)"
  shows "seq_valid C"
  using sound by(auto simp add: seq_valid_def sound_def)

lemma proof_sound:"pt_result pt = Some rule \<Longrightarrow> QEs_hold pt \<Longrightarrow> sound rule"
proof (induction pt arbitrary: rule)
  case (FOLRConstant x)
  then show ?case 
    by(auto simp add: sound_valid sound_def valid_def)
next
  case (RuleApplication pt RA branch)
  then show ?case 
    apply auto
    apply(cases "pt_result pt",auto) subgoal for P  A S
      apply(cases "length P \<le> branch", auto)
      by(rule core_rule_sound,auto)
    done
next
  case (AxiomaticRule x)
  then show ?case 
    apply(auto)
    by(rule axrule_sound)
next
  case (PrUSubst pt \<sigma>)
  then show ?case 
    apply(auto) 
    apply(cases "pt_result pt") apply( auto)
    subgoal for P A S
      apply(cases "ssafe \<sigma> \<and>
                Radmit \<sigma> (P, A, S) \<and>
                (\<forall>i<length P.
                    (\<forall>ia<length (fst (P ! i)). fsafe (fst (P ! i) ! ia)) \<and> (\<forall>ia<length (snd (P ! i)). fsafe (snd (P ! i) ! ia))) \<and>
                (\<forall>i<length A. fsafe (A ! i)) \<and> (\<forall>i<length S. fsafe (S ! i)) \<and> (FVS \<sigma> = {} \<or> P = [] \<or> (P, A, S) = CQaxrule)",
auto simp del: Rsubst.simps)
      apply(rule subst_rule)
      subgoal by auto
      subgoal by auto
      subgoal apply auto done
      subgoal apply auto done
      subgoal by auto 
      subgoal proof -
        assume "pt_result pt = Some ([], A, S)"
        assume "rule = Rsubst ([], A, S) \<sigma>"
        assume ssafe:"ssafe \<sigma>"
        assume Rad:"Radmit \<sigma> ([], A, S)"
        assume Rsafe:"\<forall>i<length A. fsafe (A ! i)"  "\<forall>i<length S. fsafe (S ! i) "
        assume "P = []"
        assume "(\<And>a aa b. [] = a \<and> A = aa \<and> S = b \<Longrightarrow> sound ([], aa, b))"
        then have as_sound:"sound ([], A,S)" by auto
        have as_valid:"seq_valid (A,S)" by (rule sound_valid[OF as_sound])
        have sub_valid:"seq_valid (Ssubst (A,S) \<sigma>)"
          apply(rule Ssubst_sound)
          subgoal using Rad unfolding Radmit_def by auto
          subgoal using Rsafe unfolding Rsafe_def by auto
          subgoal by (rule ssafe)
          subgoal by (rule as_valid) done
        have dist:"(Rsubst ([], A, S) \<sigma>) = ([], Ssubst (A,S) \<sigma>)" by auto
        have rsound:"sound ([], Ssubst (A,S) \<sigma>)" apply(rule valid_to_sound) by(rule sub_valid)
        show "sound (Rsubst ([], A, S) \<sigma>)"
          using rsound dist by auto
      qed
      subgoal 
        apply(unfold CQaxrule_def)
        apply(simp only: Rsubst.simps)
        apply(rule soundI)
      proof -
        fix I::"interp"
        assume pasEq:"(P, A, S) = ([([], [Equals ($$F Ix) ($$F Iy)])], [], [$\<phi> Iz (singleton ($$F Ix)) \<leftrightarrow> $\<phi> Iz (singleton ($$F Iy))])"
        assume "(\<And>a aa b. P = a \<and> A = aa \<and> S = b \<Longrightarrow> sound (a, aa, b))"
        then have soundPAS:"sound ([([], [Equals ($$F Ix) ($$F Iy)])], 
                                     [], [$\<phi> Iz (singleton ($$F Ix)) 
                                       \<leftrightarrow> $\<phi> Iz (singleton ($$F Iy))])" 
          using pasEq by auto
        have apply_rule:"\<And>I \<nu>. is_interp I \<Longrightarrow>
          (\<nu> \<in> seq_sem I ([], [Equals ($$F fid1) ($$F fid2)])) \<Longrightarrow>
          (\<nu> \<in> seq_sem I (([],[$\<phi> vid3 (singleton ($$F fid1)) \<leftrightarrow> $\<phi> vid3 (singleton ($$F fid2))])))"
        proof (auto simp add: TT_def Implies_def soundPAS sound_def)
          fix I::"interp" and a b
          assume good:"is_interp I"
          assume predl:"Predicates I Iz (\<chi> i. dterm_sem I (if i = Ix then $$F Ix else \<^bold>0) (a, b))"
            assume funls:" (Funls I Ix (a, b) = Funls I Iy (a, b))"
            have vec_eq:"(\<chi> i. dterm_sem I (if i = Ix then $$F Ix else \<^bold>0) (a, b)) = (\<chi> i. dterm_sem I (if i = Ix then $$F Iy else \<^bold>0) (a, b))"
              apply(rule vec_extensionality)
              by(auto simp add: funls)
            show " Predicates I Iz (\<chi> i. dterm_sem I (if i = Ix then $$F Iy else \<^bold>0) (a, b))"  
              using soundPAS unfolding sound_def apply (auto simp add: TT_def Implies_def)
              apply(erule allE[where x=I])
              using predl funls good vec_eq by auto
          next
          fix I::"interp" and a b
          assume good:"is_interp I"
          assume predl:"Predicates I Iz (\<chi> i. dterm_sem I (if i = Ix then $$F Iy else \<^bold>0) (a, b))"
          assume funls:" Funls I Ix (a, b) = Funls I Iy (a, b)"
          have vec_eq:"(\<chi> i. dterm_sem I (if i = Ix then $$F Iy else \<^bold>0) (a, b)) = (\<chi> i. dterm_sem I (if i = Ix then $$F Ix else \<^bold>0) (a, b))"
            apply(rule vec_extensionality)
            by(auto simp add: funls)
          show " Predicates I Iz (\<chi> i. dterm_sem I (if i = Ix then $$F Ix else \<^bold>0) (a, b))"  
              using soundPAS unfolding sound_def apply (auto simp add: TT_def Implies_def)
              apply(erule allE[where x=I])
              using predl vec_eq by auto
          qed
        assume "rule = (map (\<lambda>\<phi>. Ssubst \<phi> \<sigma>) [([], [Equals ($$F Ix) ($$F Iy)])],
                 Ssubst ([], [$\<phi> Iz (singleton ($$F Ix)) \<leftrightarrow> $\<phi> Iz (singleton ($$F Iy))]) \<sigma>)"
        assume ssafe:"ssafe \<sigma>"
        then have frees:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
          subgoal for i f'
          apply (auto simp add: ssafe_def) apply(erule allE[where x=i]) by(auto) done
        assume Radmit:"Radmit \<sigma> ([([], [Equals ($$F Ix) ($$F Iy)])], [], [$\<phi> Iz (singleton ($$F Ix)) \<leftrightarrow> $\<phi> Iz (singleton ($$F Iy))])"
        assume Rsafe:"\<forall>i<length P. (\<forall>ia<length (fst (P ! i)). fsafe (fst (P ! i) ! ia)) \<and> (\<forall>ia<length (snd (P ! i)). fsafe (snd (P ! i) ! ia))"
       "  \<forall>i<length A. fsafe (A ! i) "
         "\<forall>i<length S. fsafe (S ! i)"
        then have RRsafe:"Rsafe (P,A,S)" by auto
           
        assume good_interp:" is_interp I"
        have Fad:"Fadmit \<sigma> (Equals ($$F Ix) ($$F Iy))" 
          using Radmit 
          by(auto simp add: Equals_def Radmit_def Sadmit_def)
        have fsafe:"fsafe (Equals ($$F Ix) ($$F Iy)) " 
          by(auto simp add: Equals_def Ix_def Iy_def max_str ilength_def FSENT_def SSENT_def FSENTINEL_def SSENTINEL_def invX invY ident_expose_def)
        assume mems:"(\<And>i. 0 \<le> i \<Longrightarrow>
               i < length (map (\<lambda>\<phi>. Ssubst \<phi> \<sigma>) [([], [Equals ($$F Ix) ($$F Iy)])]) \<Longrightarrow>
               seq_sem I (nth (map (\<lambda>\<phi>. Ssubst \<phi> \<sigma>) [([], [Equals ($$F Ix) ($$F Iy)])])  i) = UNIV)"
        then have "seq_sem I (Ssubst([], [Equals ($$F Ix) ($$F Iy)]) \<sigma>) = UNIV" by (auto)
        then have "fml_sem I (Fsubst(Equals ($$F Ix) ($$F Iy)) \<sigma>) = UNIV" by (auto)
        then have "\<And>\<nu>. \<nu> \<in> fml_sem I (Fsubst(Equals ($$F Ix) ($$F Iy)) \<sigma>)" by (auto)
        then have "\<And>\<nu>. \<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (Equals ($$F Ix) ($$F Iy)) "
          using subst_fml[OF good_interp,where \<phi>="(Equals ($$F Ix) ($$F Iy))", where \<sigma>=\<sigma>, OF Fad fsafe ssafe] by auto
        then have Feq_adj:"\<And>\<nu>. \<nu> \<in> seq_sem (adjoint I \<sigma> \<nu>) ([], [Equals ($$F Ix) ($$F Iy)])"  by (auto)
        have safes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
                   "(\<And>i x ODE. SODEs \<sigma> i (NB x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"
          using ssafe unfolding ssafe_def  apply auto
          subgoal for x y using frees  by auto
          subgoal for i x ode
            apply (erule allE[where x=i])
            apply (erule allE[where x=i])
            apply (erule allE[where x=i])
            apply (erule allE[where x=i])
            apply (erule allE[where x=i])
            apply(erule allE[where x="NB x"])
            apply(erule allE[where x="x"])
            apply(cases " SODEs \<sigma> i (NB x)")
            subgoal by auto
            subgoal by (metis option.case(2) ssafe ssafe_def) done done
        have ruleres:"\<And>\<nu>. \<nu> \<in> seq_sem (adjoint I \<sigma> \<nu>) ([], [$\<phi> vid3 (singleton ($$F fid1)) \<leftrightarrow> $\<phi> vid3 (singleton ($$F fid2))])"
          subgoal for \<nu>
            apply(rule apply_rule[of "adjoint I \<sigma> \<nu>" \<nu>])
             apply(rule adjoint_safe)
               apply(rule good_interp)
            subgoal for i f' using frees by auto
            subgoal for i x ODE using safes by auto     
            using Feq_adj by auto
          done
        have Sad:"Sadmit \<sigma> ([], [$\<phi> Iz (singleton ($$F Ix)) \<leftrightarrow> $\<phi> Iz (singleton ($$F Iy))])" 
          using Radmit by(auto simp add: Radmit_def)
          have Ssafe:"Ssafe ([], [$\<phi> Iz (singleton ($$F Ix)) \<leftrightarrow> $\<phi> Iz (singleton ($$F Iy))])" 
            using Rsafe apply (auto simp add: Ssafe_def Rsafe_def expand_singleton Equiv_def Or_def)
          by(auto simp add: Equals_def Ix_def Iy_def Iz_def max_str ilength_def FSENT_def SSENT_def FSENTINEL_def SSENTINEL_def invX invY invZ ident_expose_def)
          have ssafe:"ssafe \<sigma>" by (rule ssafe)
        show "seq_sem I (Ssubst ([], [$\<phi> Iz (singleton ($$F Ix)) \<leftrightarrow> $\<phi> Iz (singleton ($$F Iy))]) \<sigma>) = UNIV" 
        using subst_sequent[OF good_interp Sad Ssafe ssafe] ruleres  by auto
      qed
      done
    done
next
  case (Ax x)
  then show ?case 
    apply(auto) 
    apply(rule valid_to_sound)
    apply(rule fml_seq_valid)
    by(rule axiom_valid)
next
  case (FNC pt newCon RA)
  then show ?case 
  proof (auto,cases "pt_result pt", auto,cases "rule_result ([newCon], newCon) (0, RA)",  auto)
    fix P1 A1 S1 P2 A2 S2
    assume mr: "merge_rules (P2, A2, S2) (P1, A1, S1) 0 = Some rule"
    assume ptr:"pt_result pt = Some (P1, A1, S1)"
    assume rr:"rule_result ([newCon], newCon) (0, RA) = Some (P2, A2, S2)"
    assume"(\<And>ab ac ba. P1 = ab \<and> A1 = ac \<and> S1 = ba \<Longrightarrow> sound (ab, ac, ba))"
    then have sound:"sound (P1,A1,S1)" by auto
     show "sound rule"
        apply(rule merge_rules_sound[where R="rule", where ?SG1.0="P2",where ?C1.0="(A2,S2)" , 
              where ?SG2.0="P1", where ?C2.0 ="(A1,S1)", where i=0])
       subgoal 
         apply(rule core_rule_sound[of "([newCon],newCon)" 0 RA "(P2,A2,S2)"])
         subgoal by(auto simp add: sound_def)
         subgoal by(auto)
         by (rule rr) 
          apply(rule sound)
       subgoal using mr apply(simp) by(cases P1,auto)
       by (rule mr)
   qed
next                                     
  case (Pro pt1 pt2)
  then show ?case 
    apply auto
    apply(cases "pt_result pt2") apply auto
    subgoal for P2 C2A C2S
    apply(cases " Suc 0 \<noteq> length P2") apply(auto)
    apply(cases "pt_result pt1") apply auto
      subgoal for P1 C1A C1S
        apply(rule merge_rules_sound[where R="rule",where ?SG1.0=P2, where ?C1.0="(C2A,C2S)",where ?SG2.0=P1, where ?C2.0="(C1A,C1S)",where i=0])
        apply auto
        done done done
next
  case (Start x)
  then show ?case by(auto simp add: sound_def)
next
  case (Sub pt1 pt2 branch)
  then show ?case 
    apply auto
    apply(cases "pt_result pt1") apply auto
    subgoal for P1 C1A C1S
    apply(cases "length P1 \<le> branch") apply(auto)
    apply(cases "pt_result pt2") apply auto
      subgoal for P2 C2A C2S
        apply(rule merge_rules_sound[where R="rule",where ?SG1.0=P1, where ?C1.0="(C1A,C1S)",where ?SG2.0=P2, where ?C2.0="(C2A,C2S)",where i=branch])
        by auto done done       
qed




(*  apply(induct rule: proof_ok.induct)
  unfolding proof_result.simps  apply(rule deriv_sound)
  apply assumption
  by(rule start_proof_sound)*)
 (*
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
   (0, RightRule ImplyR 0)  (* 1 *)
  ,(0, LeftRule AndL 0)
  ,(0, RightRule ImplyR 0)
  ,(0, Cut DIAndCutP1)
  ,(1, Cut DIAndSG1)
  ,(0, RightRule CohideR 0)
  ,(Suc (Suc 0), LeftRule ImplyL 0)
  ,(Suc (Suc (Suc 0)), CloseId 1 0)
  ,(Suc (Suc 0), LeftRule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc (Suc 0), Cut DIAndCut34Elim1) (* 11 *)
  ,(0, LeftRule ImplyL 0)
  ,(Suc (Suc (Suc 0)), LeftRule ImplyL 0)
  ,(0, RightRule CohideRR 0)
  ,(0, RightRule CohideRR 0)
  ,(Suc 0, RightRule CohideRR 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), G)  
  ,(0, RightRule ImplyR 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), LeftRule AndL 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), CloseId 0 0)
  ,(Suc (Suc (Suc 0)), AxSubst AK DIAndSubst341) (* 21 *)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc 0, CloseId 0 0)
  ,(0, Cut DIAndCut12Intro)
  ,(Suc 0, RightRule CohideRR 0)
  ,(Suc (Suc 0), AxSubst AK DIAndSubst12)
  ,(0, LeftRule ImplyL 0)
  ,(1, LeftRule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc 0, Cut DIAndCutP12)
  ,(0, LeftRule ImplyL 0) (* 31 *)
  ,(0, RightRule CohideRR 0)
  ,(Suc (Suc (Suc (Suc 0))), AxSubst AK DIAndCurry12)
  ,(Suc (Suc (Suc 0)), RightRule CohideRR 0)
  ,(Suc (Suc 0), LeftRule ImplyL 0)
  ,(Suc (Suc 0), G)  
  ,(0, RightRule ImplyR 0)  
  ,(Suc (Suc (Suc (Suc 0))), RightRule ImplyR 0)  
  ,(Suc (Suc (Suc (Suc 0))), RightRule AndR 0)  
  ,(Suc (Suc (Suc (Suc (Suc 0)))), CloseId 0 0)
  ,(Suc (Suc (Suc (Suc 0))), CloseId 1 0) (* 41 *)
  ,(Suc (Suc  0), CloseId 0 0)   
  ,(Suc 0, Cut DIAndCut34Elim2)
  ,(0, LeftRule ImplyL 0)
  ,(0, RightRule CohideRR 0)
  ,(Suc (Suc (Suc (Suc 0))), AxSubst AK DIAndSubst342) (* 46 *)
  ,(Suc (Suc (Suc 0)), RightRule CohideRR 0)
  ,(Suc (Suc (Suc 0)), G) (* 48 *)
  ,(0, RightRule ImplyR 0)
  ,(Suc (Suc (Suc 0)), LeftRule AndL 0) (* 50 *)
  ,(Suc (Suc (Suc 0)), CloseId 1 0)
  ,(Suc (Suc 0), LeftRule ImplyL 0)
  ,(Suc 0, CloseId 0 0)
  ,(1, Cut DIAndSG2)
  ,(0, LeftRule ImplyL 0)
  ,(0, RightRule CohideRR 0)
  ,(Suc (Suc (Suc 0)), CloseId 4 0)
  ,(Suc (Suc 0), LeftRule ImplyL 0)
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
  
section \<open>Example 2: Concrete Hybrid System\<close>

(* v \<ge> 0 \<and> A() \<ge> 0 \<longrightarrow> [v' = A, x' = v]v' \<ge> 0*)
definition SystemConcl::"('sf,'sc,'sz) sequent"
where "SystemConcl = 
  ([],[
  Implies (And (Geq (Var vid1) \<^bold>0) (Geq (f0 fid1) \<^bold>0))
  ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (TT)]]Geq (Var vid1) \<^bold>0)
  ])"

definition SystemDICut :: "('sf,'sc,'sz) formula"
where "SystemDICut =
  Implies
  (Implies TT ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]]
     (Geq (Differential (Var vid1)) (Differential \<^bold>0))))
  (Implies
     (Implies TT (Geq (Var vid1) \<^bold>0))
     ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (Var vid1) \<^bold>0)))"
(*
    (Implies (Geq (Var vid1) \<^bold>0) 
      (Implies (And TT ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]]
                  (Geq (Differential (Var vid1)) (Differential \<^bold>0))
   )) ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (Var vid1) \<^bold>0))))"
*)  
definition SystemDCCut::"('sf,'sc,'sz) formula"
where "SystemDCCut =
(([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (f0 fid1) \<^bold>0)) \<rightarrow>
   (([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]]((Geq (Differential (Var vid1)) (Differential \<^bold>0)))) 
   \<leftrightarrow>  
   ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) \<^bold>0))]](Geq (Differential (Var vid1)) (Differential \<^bold>0)))))"
  
definition SystemVCut::"('sf,'sc,'sz) formula"
where "SystemVCut = 
  Implies (Geq (f0 fid1) \<^bold>0) ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) \<^bold>0))]](Geq (f0 fid1) \<^bold>0))" 

definition SystemVCut2::"('sf,'sc,'sz) formula"
where "SystemVCut2 = 
  Implies (Geq (f0 fid1) \<^bold>0) ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (f0 fid1) \<^bold>0))" 

definition SystemDECut::"('sf,'sc,'sz) formula"
where "SystemDECut = (([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) \<^bold>0))]] ((Geq (Differential (Var vid1)) (Differential \<^bold>0)))) \<leftrightarrow>
 ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) \<^bold>0))]]
    [[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential \<^bold>0))))"

definition SystemKCut::"('sf,'sc,'sz) formula"
where "SystemKCut =
  (Implies ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) \<^bold>0))]]
                (Implies ((And TT (Geq (f0 fid1) \<^bold>0))) ([[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential \<^bold>0)))))
      (Implies ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) \<^bold>0))]] ((And TT (Geq (f0 fid1) \<^bold>0))))
               ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) \<^bold>0))]] ([[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential \<^bold>0))))))"

definition SystemEquivCut::"('sf,'sc,'sz) formula"
where "SystemEquivCut =
  (Equiv (Implies ((And TT (Geq (f0 fid1) \<^bold>0))) ([[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential \<^bold>0))))
         (Implies ((And TT (Geq (f0 fid1) \<^bold>0))) ([[DiffAssign vid1 (f0 fid1)]](Geq (DiffVar vid1) \<^bold>0))))"

definition SystemDiffAssignCut::"('sf,'sc,'sz) formula"
where "SystemDiffAssignCut =
  (([[DiffAssign vid1  ($f fid1 empty)]] (Geq (DiffVar vid1) \<^bold>0))
\<leftrightarrow> (Geq ($f fid1 empty) \<^bold>0))"
  
definition SystemCEFml1::"('sf,'sc,'sz) formula"
where "SystemCEFml1 = Geq (Differential (Var vid1)) (Differential \<^bold>0)"

definition SystemCEFml2::"('sf,'sc,'sz) formula"
where "SystemCEFml2 = Geq (DiffVar vid1) \<^bold>0"


(*
definition diff_const_axiom :: "formula"
  where [axiom_defs]:"diff_const_axiom \<equiv> Equals (Differential ($f fid1 empty)) \<^bold>0"

definition diff_var_axiom :: "formula"
  where [axiom_defs]:"diff_var_axiom \<equiv> Equals (Differential (Var vid1)) (DiffVar vid1)"*)

  
definition CQ1Concl::"('sf,'sc,'sz) formula"
where "CQ1Concl = (Geq (Differential (Var vid1)) (Differential \<^bold>0) \<leftrightarrow> Geq (DiffVar vid1) (Differential \<^bold>0))"

definition CQ2Concl::"('sf,'sc,'sz) formula"
where "CQ2Concl = (Geq (DiffVar vid1) (Differential \<^bold>0) \<leftrightarrow> Geq ($' vid1) \<^bold>0)"

definition CEReq::"('sf,'sc,'sz) formula"
where "CEReq = (Geq (Differential (trm.Var vid1)) (Differential \<^bold>0) \<leftrightarrow> Geq ($' vid1) \<^bold>0)"

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
    SPredicates = (\<lambda>p. (if p = vid1 then (Some (Geq  (Function  (Inr vid1)  empty) (Differential \<^bold>0))) else None)),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

definition CEProof::"('sf,'sc,'sz) pf"
where "CEProof = (([],[CEReq]), [
  (0, Cut CQ1Concl)
 ,(0, Cut CQ2Concl)
 ,(1, RightRule CohideRR 0)
 ,(Suc (Suc 0), CQ (Differential \<^bold>0) \<^bold>0 CQRightSubst)
 ,(1, RightRule CohideRR 0)
 ,(1, CQ (Differential (Var vid1)) (DiffVar vid1) CQLeftSubst)
 ,(0, RightRule EquivR 0)
 ,(0, LeftRule EquivForwardL 1)
 ,(Suc (Suc 0), LeftRule EquivForwardL 1)
 ,(Suc (Suc (Suc 0)), CloseId 0 0)
 ,(Suc (Suc 0), CloseId 0 0)
 ,(Suc 0, CloseId 0 0)
 ,(0, LeftRule EquivBackwardL (Suc (Suc 0)))
 ,(0, CloseId 0 0)
 ,(0, LeftRule EquivBackwardL (Suc 0))
 ,(0, CloseId 0 0)
 ,(0, CloseId 0 0)
 ])"  

lemma CE_result_correct:"proof_result CEProof = ([],([],[CEReq]))"
  unfolding CEProof_def CEReq_def CQ1Concl_def  CQ2Concl_def Implies_def Or_def f0_def TT_def Equiv_def Box_def CQRightSubst_def
  by (auto simp add: id_simps)

definition DiffConstSubst::"('sf,'sc,'sz) subst"
where "DiffConstSubst = \<lparr>
    SFunctions = (\<lambda>f. (if f = fid1 then (Some \<^bold>0) else None)),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

definition DiffConstProof::"('sf,'sc,'sz) pf"
where "DiffConstProof = (([],[(Equals (Differential \<^bold>0) \<^bold>0)]), [
  (0, AxSubst AdConst DiffConstSubst)])"

lemma diffconst_result_correct:"proof_result DiffConstProof = ([], ([],[Equals (Differential \<^bold>0) \<^bold>0]))"
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

lemma almost_diff_const_sound:"sound ([], ([], [Equals (Differential \<^bold>0) \<^bold>0]))"
  using diffconst_result_correct diffconst_sound_lemma by simp

lemma almost_diff_const:"valid (Equals (Differential \<^bold>0) \<^bold>0)"
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
    
lemma CE1pre_valid2:"valid (! (! (Geq (Differential (trm.Var vid1)) (Differential \<^bold>0) && Geq ($' vid1) \<^bold>0) &&
              ! (! (Geq (Differential (trm.Var vid1)) (Differential \<^bold>0)) && ! (Geq ($' vid1) \<^bold>0)))) "
  using CE1pre_valid unfolding CEReq_def Equiv_def Or_def by auto

definition SystemDISubst::"('sf,'sc,'sz) subst"
where "SystemDISubst = 
  \<lparr> SFunctions = (\<lambda>f. 
    (     if f = fid1 then Some(Function (Inr vid1) empty)
     else if f = fid2 then Some\<^bold>0
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
     (Geq (Differential (Var vid1)) (Differential \<^bold>0))))
  (Implies
     (Implies TT (Geq (Var vid1) \<^bold>0))
     ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (Var vid1) \<^bold>0)))
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
      Some (Geq (Differential (Var vid1)) (Differential \<^bold>0))
    else if C = pid3 then
      Some (Geq (Function fid1 empty) \<^bold>0) 
    else 
     None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>c. if c = vid1 then Some (OProd (OSing vid1 (Function fid1 empty)) (OSing vid2 (trm.Var vid1))) else None)
  \<rparr>"

definition SystemVSubst::"('sf,'sc,'sz) subst"
where "SystemVSubst = 
  \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>p. if p = vid1 then Some (Geq (Function (Inl fid1) empty) \<^bold>0) else None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>a. if a = vid1 then 
      Some (EvolveODE (OProd 
                         (OSing vid1 (Function fid1 empty)) 
                         (OSing vid2 (Var vid1))) 
                      (And TT (Geq (Function fid1 empty) \<^bold>0))) 
                      else None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

definition SystemVSubst2::"('sf,'sc,'sz) subst"
where "SystemVSubst2 = 
  \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>p. if p = vid1 then Some (Geq (Function (Inl fid1) empty) \<^bold>0) else None),
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
    SPredicates = (\<lambda>p. if p = vid2 then Some(And TT (Geq (Function (Inl fid1) empty) \<^bold>0)) else None),
    SContexts = (\<lambda>C. if C = pid1 then Some(Geq (Differential (Var vid1)) (Differential \<^bold>0)) else None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

lemma systemdesubst_correct:"\<exists> ODE.(([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) \<^bold>0))]] ((Geq (Differential (Var vid1)) (Differential \<^bold>0)))) \<leftrightarrow>
 ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) \<^bold>0))]]
    [[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential \<^bold>0))))
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
        (Some (And (Geq \<^bold>0 \<^bold>0) (Geq (Function fid1 empty) \<^bold>0))) 
      else if C = pid2 then 
        (Some ([[DiffAssign vid1 (Function fid1 empty)]](Geq (Differential (Var vid1)) (Differential \<^bold>0)))) else None),
    SPrograms = (\<lambda>c. if c = vid1 then Some (EvolveODE (OProd (OSing vid1 (Function fid1 empty)) (OSing vid2 (Var vid1))) (And (Geq \<^bold>0 \<^bold>0) (Geq (Function fid1 empty) \<^bold>0))) else None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

lemma subst_imp_simp:"Fsubst (Implies p q) \<sigma> = (Implies (Fsubst p \<sigma>) (Fsubst q \<sigma>))"
  unfolding Implies_def Or_def by auto

lemma subst_equiv_simp:"Fsubst (Equv p q) \<sigma> = (Equiv (Fsubst p \<sigma>) (Fsubst q \<sigma>))"
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
    SContexts = (\<lambda>C. if C = pid1 then Some (And (Geq \<^bold>0 \<^bold>0) (Geq (Function fid1 empty) \<^bold>0)) else None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>c. if c = vid1 then Some (OProd (OSing vid1 (Function fid1 empty)) (OSing vid2 (Var vid1))) else None)
  \<rparr>"

definition SystemCESubst::"('sf,'sc,'sz) subst"
where "SystemCESubst = \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. if C = pid1 then Some(Implies(And (Geq \<^bold>0 \<^bold>0) (Geq (Function fid1 empty) \<^bold>0)) ([[DiffAssign vid1 (Function fid1 empty)]](Predicational (Inr ())))) else None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

lemma SystemCESubstOK:
  "step_ok 
  ([([],[Equiv (Implies(And (Geq \<^bold>0 \<^bold>0) (Geq (Function fid1 empty) \<^bold>0)) ([[DiffAssign vid1 (Function fid1 empty)]]( SystemCEFml1))) 
         (Implies(And (Geq \<^bold>0 \<^bold>0) (Geq (Function fid1 empty) \<^bold>0)) ([[DiffAssign vid1 (Function fid1 empty)]]( (SystemCEFml2))))
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
    SPredicates = (\<lambda>p. if p = vid1 then Some (Geq (Function (Inr vid1) empty) \<^bold>0) else None),
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
  (0, RightRule ImplyR 0)
  ,(0, LeftRule AndL 0)
  ,(0, Cut SystemDICut)
  ,(0, LeftRule ImplyL 0)
  ,(0, RightRule CohideRR 0)
  ,(0, LeftRule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc 0, AxSubst ADIGeq SystemDISubst) (* 8 *)
  ,(Suc 0, RightRule ImplyR 0)
(*  ,(0, CloseId 0 0)        *)
  ,(Suc 0, CloseId 1 0)        
(*  ,(0, RightRule AndR 0)*)
  ,(0, RightRule ImplyR 0)   
  ,(0, Cut SystemDCCut)
  ,(0, LeftRule ImplyL 0)
  ,(0, RightRule CohideRR 0)
  ,(0, LeftRule EquivBackwardL 0)
  ,(0, RightRule CohideR 0)
  ,(0, AxSubst ADC SystemDCSubst) (* 17 *)
  ,(0, CloseId 0 0)
  ,(0, RightRule CohideRR 0)
  ,(0, Cut SystemVCut)
  ,(0, LeftRule ImplyL 0) 
  ,(0, RightRule CohideRR 0)
  ,(0, Cut SystemDECut)
  ,(0, LeftRule EquivBackwardL 0)
  ,(0, RightRule CohideRR 0)
  ,(1, CloseId (Suc 1) 0) (* Last step *)
  ,(Suc 1, CloseId 0 0)
  ,(1, AxSubst AV SystemVSubst) (* 28 *)
  ,(0, Cut SystemVCut2)
  
  ,(0, LeftRule ImplyL 0)
  ,(0, RightRule CohideRR 0)
  ,(Suc 1, CloseId 0 0)
  ,(Suc 1, CloseId (Suc 2) 0)
  
  ,(Suc 1, AxSubst AV SystemVSubst2) (* 34 *)
  ,(0, RightRule CohideRR 0)
  ,(0, DEAxiomSchema (OSing vid2 (trm.Var vid1)) SystemDESubst) (* 36 *)
  ,(0, Cut SystemKCut)
  ,(0, LeftRule ImplyL 0)
  ,(0, RightRule CohideRR 0)
  ,(0, LeftRule ImplyL 0)
  ,(0, RightRule CohideRR 0)
  ,(0, AxSubst AK SystemKSubst) (* 42 *)
  ,(0, CloseId 0 0)
  ,(0, RightRule CohideR 0)
  ,(1, AxSubst ADW SystemDWSubst) (* 45 *)
  ,(0, G)
  ,(0, Cut SystemEquivCut)
  ,(0, LeftRule EquivBackwardL 0)
  ,(0, RightRule CohideR 0)
  ,(0, CloseId 0 0)
  ,(0, RightRule CohideR 0)
  ,(0, CE SystemCEFml1 SystemCEFml2 SystemCESubst) (* 52 *)
  ,(0, RightRule ImplyR 0)
  ,(0, LeftRule AndL 0)
  ,(0, Cut SystemDiffAssignCut) 
  ,(0, LeftRule EquivBackwardL 0)
  ,(0, RightRule CohideRR 0)
  ,(0, CloseId 0 0)
  ,(0, CloseId 1 0)
  ,(0, AxSubst Adassign SystemDiffAssignSubst) (* 60 *)
  ])"
  
lemma system_result_correct:"proof_result SystemProof = 
  ([],
  ([],[Implies (And (Geq (Var vid1) \<^bold>0) (Geq (f0 fid1) \<^bold>0))
        ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (TT)]]Geq (Var vid1) \<^bold>0)]))"
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
  
lemma DIAnd_result_correct:"proof_result (proof_take 61 DIAndProof) = DIAnd"
  unfolding DIAndProof_def DIAndConcl_def Implies_def Or_def 
  proof_result.simps deriv_result.simps start_\<forall>i<length A. fsafe (A ! proof.simps DIAndCutP12_def  DIAndSG1_def DIAndSG2_def DIAndCutP1_def Box_def DIAndCut34Elim1_def DIAndCut12Intro_def DIAndCut34Elim2_def DIAnd_def
  using pne12 pne13 pne14 pne23 pne24 pne34 by (auto)

theorem DIAnd_sound: "sound DIAnd"
  using DIAndSound_lemma DIAnd_result_correct by auto
*)
end
 