theory Interval_Arithmetic
imports 
  Complex_Main
  "./Word_Lib/Word_Lib"
  "./Word_Lib/Word_Lemmas"
begin

type_synonym word = "32 Word.word"

definition NEG_INF::"word"
where "NEG_INF = -((2 ^ 31) -1)"

definition POS_INF::"word"
where "POS_INF = (2^31) - 1"

typedef bword = "{n::word. sint n \<ge> sint NEG_INF \<and> sint n \<le> sint POS_INF}"
  apply(rule exI[where x=NEG_INF])
  by (auto simp add: NEG_INF_def POS_INF_def)

setup_lifting type_definition_bword


(*export_code xCoord in Haskell module_name Example 
definition *)

type_synonym id = string

(* To make running the proof easier, don't include ODEs yet *)
datatype trm =
  Const bword     ("_ \<in> \<R>" 10)
| Var id         ("_ \<in> \<V>" 10)
| Plus trm trm  (infix "+" 10)
| Times trm trm (infix "*" 10)
| Max trm trm
| Min trm trm
| Neg trm        ("-")

datatype fml =
  Le trm trm     ("_ < _")
| Leq trm trm
| Equals trm trm
| And fml fml    ("_ & _")
| Or fml fml    
| Not fml        ("\<not>")

datatype hp =
  Test fml       ("?")
| Seq hp hp      ("_ ; _")
| Assign id trm  ("_ <- _")
| Choice hp hp

type_synonym rstate = "id \<Rightarrow> real"
type_synonym wstate = "(id + id) \<Rightarrow> word"


definition word::"word \<Rightarrow> bool"
where word_def[simp]:"word w \<equiv> w \<in> {NEG_INF..POS_INF}"

definition wstate::"wstate \<Rightarrow> prop"
where wstate_def[simp]:"wstate \<nu> \<equiv> (\<And>i. word (\<nu> (Inl i)) \<and> word (\<nu> (Inr i)))"

named_theorems rep_simps "Simplifications for representation functions"

(* Note: 0x80000000 is never used. This way there's no awkward asymmetry but I can still use existing
 * support for 2's complement *)
inductive repe ::"word \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>E" 10)
where 
  repPOS_INF:"r \<ge> real_of_int (sint POS_INF) \<Longrightarrow> repe POS_INF r" 
| repNEG_INF:"r \<le> real_of_int (sint NEG_INF) \<Longrightarrow> repe NEG_INF r"
| repINT:    "(sint w) < real_of_int(sint POS_INF) \<Longrightarrow> (sint w) > real_of_int(sint NEG_INF) \<Longrightarrow> repe w (sint w)"

inductive_simps 
    repePos_simps[rep_simps]:"repe POS_INF r"
and repeNeg_simps[rep_simps]:"repe NEG_INF r"
and repeInt_simps[rep_simps]:"repe w (sint w)"

definition repU ::"word \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>U" 10)
where "repU w r \<equiv> \<exists> r'. r' \<ge> r \<and> repe w r'"

definition repL ::"word \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>L" 10)
where "repL w r \<equiv> \<exists> r'. r' \<le> r \<and> repe w r'"

definition repP ::"word * word \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>P" 10)
where "repP w r \<equiv> let (w1, w2) = w in repL w1 r \<and> repU w2 r" 

inductive rtsem :: "trm \<Rightarrow> rstate \<Rightarrow> real  \<Rightarrow> bool"  ("([_]_ \<down> _)" 10)
where "Rep_bword w \<equiv>\<^sub>E r \<Longrightarrow> ([w \<in> \<R>]\<nu> \<down> r)"
| "([x \<in> \<V>]\<nu> \<down> \<nu> x)"
| "\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> ([\<theta>\<^sub>1 + \<theta>\<^sub>2]\<nu> \<down> (r\<^sub>1 + r\<^sub>2))"
| "\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> ([\<theta>\<^sub>1 * \<theta>\<^sub>2]\<nu> \<down> (r\<^sub>1 * r\<^sub>2))"
| "\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> ([Max \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> (max r\<^sub>1 r\<^sub>2))"
| "\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> ([Min \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> (min r\<^sub>1 r\<^sub>2))"
| "([\<theta>]\<nu> \<down> r) \<Longrightarrow> ([-\<theta>]\<nu> \<down> -r)"

inductive_simps 
    rtsem_Const_simps[simp] : "([w \<in> \<R>]\<nu> \<down> r)"
and rtsem_Var_simps[simp] : "([x \<in> \<V>]\<nu> \<down> r)"
and rtsem_PlusU_simps[simp] : "([\<theta>\<^sub>1 + \<theta>\<^sub>2]\<nu> \<down> r)"
and rtsem_TimesU_simps[simp] : "([\<theta>\<^sub>1 * \<theta>\<^sub>2]\<nu> \<down> r)"
and rtsem_Max_simps[simp] : "([Max \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<down> r)"
and rtsem_Min_simps[simp] : "([Min \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<down> r)"
and rtsem_Neg_simps[simp] : "([-\<theta>] \<nu> \<down> r)"

definition set_less :: "real set \<Rightarrow> real set \<Rightarrow> bool" (infix "<\<^sub>S" 10)
where "set_less A B \<equiv> (\<forall> x y. x \<in> A \<and> y \<in> B \<longrightarrow> x < y)"

definition set_geq :: "real set \<Rightarrow> real set \<Rightarrow> bool" (infix "\<ge>\<^sub>S" 10)
where "set_geq A B \<equiv> (\<forall> x y. x \<in> A \<and> y \<in> B \<longrightarrow> x \<ge> y)"

inductive rfsem :: "fml \<Rightarrow> rstate \<Rightarrow> bool \<Rightarrow> bool" ("([_]_) \<down> _" 20)
where 
  rLeT:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 < r\<^sub>2 \<Longrightarrow> ([\<theta>\<^sub>1 < \<theta>\<^sub>2] \<nu> \<down> True)"
| rLeF:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 \<ge> r\<^sub>2 \<Longrightarrow> ([\<theta>\<^sub>1 < \<theta>\<^sub>2] \<nu> \<down> False)"
| rLeqT:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 \<le> r\<^sub>2 \<Longrightarrow> ([Leq \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<down> True)"
| rLeqF:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 > r\<^sub>2 \<Longrightarrow> ([Leq \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<down> False)"
| rEqualsT:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 = r\<^sub>2 \<Longrightarrow> ([Equals \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<down> True)"
| rEqualsF:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 \<noteq> r\<^sub>2 \<Longrightarrow> ([Equals \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<down> False)"
| rAndT:"\<lbrakk>([\<phi>]\<nu> \<down> True); ([\<psi>]\<nu> \<down> True)\<rbrakk> \<Longrightarrow> ([\<phi> & \<psi>]\<nu> \<down> True)"
| rAndF1:"([\<phi>]\<nu> \<down> False) \<Longrightarrow> ([\<phi> & \<psi>]\<nu> \<down> False)"
| rAndF2:"([\<psi>]\<nu> \<down> False) \<Longrightarrow> ([\<phi> & \<psi>]\<nu> \<down> False)"
| rOrT1:"([\<phi>]\<nu> \<down> True) \<Longrightarrow> ([Or \<phi> \<psi>]\<nu> \<down> True)"
| rOrT2:"([\<psi>]\<nu> \<down> True) \<Longrightarrow> ([Or \<phi> \<psi>]\<nu> \<down> True)"
| rOrF:"\<lbrakk>([\<phi>]\<nu> \<down> False) ;([\<psi>]\<nu> \<down> False)\<rbrakk> \<Longrightarrow> ([\<phi> & \<psi>]\<nu> \<down> False)"
| rNotT:"([\<phi>]\<nu> \<down> False) \<Longrightarrow> ([(\<not>\<phi>)]\<nu> \<down> True)"
| rNotF:"([\<phi>]\<nu> \<down> True) \<Longrightarrow> ([(\<not>\<phi>)]\<nu> \<down> False)"

inductive_simps
    rfsem_Gr_simps[simp]: "([\<theta>\<^sub>1 < \<theta>\<^sub>2]\<nu> \<down> b)"
and rfsem_Leq_simps[simp]: "([Leq \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> b)"
and rfsem_Equals_simps[simp]: "([Equals \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> b)"
and rfsem_And_simps[simp]: "([\<phi> & \<psi>]\<nu> \<down> b)"
and rfsem_Or_simps[simp]: "([(Or \<phi> \<psi>)]\<nu> \<down> b)"
and rfsem_Not_simps[simp]: "([\<not>\<phi>]\<nu> \<down> b)"

inductive rpsem :: "hp \<Rightarrow> rstate \<Rightarrow> rstate \<Rightarrow> bool" ("([_]_) \<down> _" 20)
where
  rTest[simp]:"\<lbrakk>([\<phi>]\<nu> \<down> True); \<nu> = \<omega>\<rbrakk> \<Longrightarrow> ([? \<phi>]\<nu> \<down> \<omega>)"
| rSeq[simp]:"\<lbrakk>([\<alpha>]\<nu> \<down> \<mu>); ([\<beta>]\<mu> \<down> \<omega>)\<rbrakk> \<Longrightarrow> ([\<alpha>; \<beta>]\<nu> \<down> \<omega>)"
| rAssign[simp]:"\<lbrakk>([\<theta>]\<nu> \<down> r); \<omega> = (\<nu> (x := r))\<rbrakk> \<Longrightarrow> ([x <- \<theta>]\<nu> \<down> \<omega>)"
| rChoice1[simp]:"([\<alpha>]\<nu> \<down> \<omega>) \<Longrightarrow> ([Choice \<alpha> \<beta>]\<nu> \<down> \<omega>)"
| rChoice2[simp]:"([\<beta>]\<nu> \<down> \<omega>) \<Longrightarrow> ([Choice \<alpha> \<beta>]\<nu> \<down> \<omega>)"

inductive_simps
    rpsem_Test_simps[simp]: "([? \<phi>]\<nu> \<down> b)"
and rpsem_Seq_simps[simp]: "([\<alpha>; \<beta>]\<nu> \<down> b)"
and rpsem_Assign_simps[simp]: "([x <- \<theta>]\<nu> \<down> b)"
and rpsem_Choice_simps[simp]: "([Choice \<alpha> \<beta>]\<nu> \<down> b)"


lemma int_not_posinf:
  assumes b1:"real_of_int (sint ra) <  real_of_int (sint POS_INF)"
  assumes b2:"real_of_int (sint NEG_INF) <  real_of_int (sint ra)"
  shows "ra \<noteq> POS_INF"
  using b1 b2 unfolding POS_INF_def NEG_INF_def by auto
        
lemma int_not_neginf:
  assumes b1:" real_of_int (sint ra) <  real_of_int (sint POS_INF)"
  assumes b2:" real_of_int (sint NEG_INF) <  real_of_int (sint ra)"
  shows "ra \<noteq> NEG_INF"
  using b1 b2 unfolding POS_INF_def NEG_INF_def by auto

lemma int_not_undef:
  assumes b1:"real_of_int (sint ra) <  real_of_int (sint POS_INF)"
  assumes b2:"real_of_int (sint NEG_INF) < real_of_int (sint ra)"
  shows "ra \<noteq> NEG_INF-1"
  using b1 b2 unfolding POS_INF_def NEG_INF_def by auto

lemma sint_range:
  assumes b1:"real_of_int (sint ra) < real_of_int (sint POS_INF)"
  assumes b2:"real_of_int (sint NEG_INF) < real_of_int (sint ra)"
  shows "sint ra  \<in> {i. i > -((2^31)-1)  \<and> i < (2^31)-1}"
  using b1 b2 unfolding POS_INF_def NEG_INF_def by auto

lemma word_size_neg:
  fixes w :: "32 Word.word"
  shows "size (-w) = size w"
  using Word.word_size[of w] Word.word_size[of "-w"] by auto

lemma uint_distinct:
  fixes w1 w2
  assumes foo:"w1 \<noteq> w2"
  shows "uint w1 \<noteq> uint w2"
  using foo by auto

fun pu :: "word \<Rightarrow> word \<Rightarrow> word"
where "pu w1 w2 = 
(if w1 = POS_INF then POS_INF
 else if w2 = POS_INF then POS_INF
 else if w1 = NEG_INF then 
  (if w2 = NEG_INF then NEG_INF 
   else
     (let sum::64 Word.word = ((scast w2)::64 Word.word) + ((scast NEG_INF)::64 Word.word) in
     if (sum::64 Word.word) <=s ((scast NEG_INF)::64 Word.word) then NEG_INF
     else scast sum))
 else if w2 = NEG_INF then 
  (let sum::64 Word.word = ((scast w1)::64 Word.word) + ((scast NEG_INF)::64 Word.word) in
   if (sum::64 Word.word) <=s ((scast NEG_INF)::64 Word.word) then NEG_INF
   else scast sum)
 else 
  (let sum::64 Word.word = ((scast w1)::64 Word.word) + ((scast w2)::64 Word.word) in
   if ((scast POS_INF)::64 Word.word) <=s (sum::64 Word.word) then POS_INF
   else if (sum::64 Word.word) <=s ((scast NEG_INF)::64 Word.word) then NEG_INF
   else scast sum))"

lemma scast_down_range:
fixes w::"'a::len Word.word"
assumes "sint w \<in> sints (len_of (TYPE('b::len)))"
shows "sint w = sint ((scast w)::'b Word.word)"
unfolding scast_def
by (simp add: assms word_sint.Abs_inverse)
   
lemma pu_lemma:
  assumes up1:"w\<^sub>1 \<equiv>\<^sub>U (r\<^sub>1::real)"
  assumes up2:"w\<^sub>2 \<equiv>\<^sub>U (r\<^sub>2::real)"
  shows   "pu w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>U (r\<^sub>1 + r\<^sub>2)"
apply(cases "w\<^sub>1 = POS_INF")
subgoal 
  apply (auto simp add: POS_INF_def repU_def repe.simps NEG_INF_def)
  using linear by blast
apply(cases "w\<^sub>2 = POS_INF")
subgoal 
  apply (auto simp add: POS_INF_def repU_def repe.simps NEG_INF_def)
  using linear by blast
  apply(cases "w\<^sub>1 = NEG_INF")
  subgoal
  apply(cases "w\<^sub>2 = NEG_INF")
  subgoal  
    using up1 up2 
    by (auto simp add: POS_INF_def NEG_INF_def repU_def repe.simps)
  subgoal
    apply(simp)
    proof -
    assume neq1:"w\<^sub>2 \<noteq> POS_INF"
    assume eq2:"w\<^sub>1 = NEG_INF"
    assume neq3:"w\<^sub>2 \<noteq> NEG_INF"
    let ?sum = "(scast w\<^sub>2 + scast NEG_INF)::64 Word.word"
    have scast_eq1:"sint((scast w\<^sub>1)::64 Word.word) = sint w\<^sub>1" 
      apply(rule Word.sint_up_scast)
      unfolding Word.is_up by auto
    have scast_eq3:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2"
      apply(rule Word.sint_up_scast)
      unfolding Word.is_up by auto
    have scast_eq2:"sint((scast (0x80000001::word))::64 Word.word) = sint ((0x80000001::32 Word.word))"
      by auto
    have sints64:"sints 64 = {i. - (2 ^ 63) \<le> i \<and> i < 2 ^ 63}"
      using sints_def[of 64] Bit_Representation.range_sbintrunc[of 63] by auto 
    have sints32:"sints 32 = {i. - (2 ^ 31) \<le> i \<and> i < 2 ^ 31}"
      using sints_def[of 32] Bit_Representation.range_sbintrunc[of 31] by auto 
    have thing1:"0 \<le> 9223372034707292161 + ((-(2 ^ 31))::real)" by auto
    have thing2:"sint ((scast w\<^sub>2)::64 Word.word) \<ge> - (2 ^ 31) " 
      using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] sints32 
      Word.word_size[of "(scast w\<^sub>2)::64 Word.word"] scast_eq1 scast_eq2 scast_eq3 len32 mem_Collect_eq 
      by auto
    have aLeq:"2 ^ 31 < (9223372039002259455::int)" by auto
    have bLeq:"sint ((scast w\<^sub>2)::64 Word.word) \<le> 2 ^ 31"
      apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] sints32 
          scast_eq3 len32)
      using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] len32[of "TYPE(32)"] sints32 by auto
    have thing3:"sint ((scast w\<^sub>2)::64 Word.word) < 9223372039002259455"
      using aLeq bLeq by auto
    have truth:" - (2 ^ (size ((scast w\<^sub>2)::64 Word.word) - 1)) \<le> sint ((scast w\<^sub>2)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) \<and> sint ((scast w\<^sub>2)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) \<le> 2 ^ (size ((scast w\<^sub>2)::64 Word.word) - 1) - 1"
      apply(auto simp add:
      Word.word_size[of "(scast w\<^sub>2)::64 Word.word"] Word.word_size[of "(scast (-0x7FFFFFFF))::64 Word.word"]
      scast_eq1 scast_eq2 
      Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]
      Word.word_sint.Rep[of "0x80000001::32 Word.word"]
      Word.word_sint.Rep[of "(scast w\<^sub>2)::64 Word.word"]
      Word.word_sint.Rep[of "-0x7FFFFFFF::64 Word.word"]
      sints64 sints32 thing2)
      using thing1 thing2 thing3 by auto
    have case1a:" sint (((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) =  sint ((scast w\<^sub>2)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
      by(rule signed_arith_sint(1)[OF truth])
    have case1b:"sint ((0xFFFFFFFF80000001)::64 Word.word) < 0"
      by auto
    have case1:"?sum <=s ((scast NEG_INF)::64 Word.word) \<Longrightarrow> NEG_INF \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2"
      using up1 up2 apply (simp add: repU_def NEG_INF_def repe.simps POS_INF_def word_sle_def)
      apply(rule exI[where x= "r\<^sub>1 + r\<^sub>2"])
      apply(auto)
      using case1a case1b 
          apply (auto simp add: NEG_INF_def neq1 eq2 neq3 repINT repU_def repe.simps repeInt_simps up2 word_sless_alt) 
      using repINT repU_def repe.simps repeInt_simps up2 word_sless_alt POS_INF_def NEG_INF_def apply (auto simp add: POS_INF_def NEG_INF_def)
      proof -
        fix r'
        assume a1:"sint ((scast w\<^sub>2)::64 Word.word) \<le> 0"
        then have h3:"sint w\<^sub>2 \<le> 0" using scast_eq3 by auto 
        assume a2:"r\<^sub>1 \<le> r'"
        assume a3:"r\<^sub>2 \<le>  (real_of_int (sint w\<^sub>2))"
        assume a4:"r' \<le>  (- 2147483647)"
        assume a5:"sint w\<^sub>2 < 2147483647"
        assume a6:"- 2147483647 < real_of_int (sint w\<^sub>2)"
        assume a7:"sint (scast w\<^sub>2 + 0xFFFFFFFF80000001) = sint (scast w\<^sub>2) - 2147483647"
        from a2 a4 have h1:"r\<^sub>1 \<le> - 2147483647" by auto
        from a1 a3 h3 have h2:"r\<^sub>2 \<le> 0" 
        using dual_order.trans of_int_le_0_iff by blast
        show "r\<^sub>1 + r\<^sub>2 \<le>  (- 2147483647)"
          using h1 h2 add.right_neutral add_mono by fastforce
      qed
    obtain r'\<^sub>1 and r'\<^sub>2 where   
              geq1:"r'\<^sub>1\<ge>r\<^sub>1" and equiv1:"w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1"
          and geq2:"r'\<^sub>2\<ge>r\<^sub>2" and equiv2:"w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2"
            using up1 up2 unfolding repU_def by auto
    have leq1:"r'\<^sub>1 \<le>  (real_of_int (sint NEG_INF))" 
      using equiv1 unfolding repe.simps
      using neq1 eq2 neq3 apply auto
        subgoal unfolding NEG_INF_def POS_INF_def by auto
        done
    have leq2:"r'\<^sub>2 =  (real_of_int (sint w\<^sub>2))"
      using equiv2 unfolding repe.simps
      using neq1 eq2 neq3 by auto      
    have case2:"\<not>(?sum <=s scast NEG_INF) \<Longrightarrow> scast ?sum \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2"
      apply (simp add: repU_def NEG_INF_def repe.simps POS_INF_def word_sle_def up1 up2)
      apply(rule exI[where x= "r'\<^sub>2 - 0x7FFFFFFF"]) (*r\<^sub>1 + r\<^sub>2*)
      apply(rule conjI)
      subgoal 
        proof -
          assume " \<not> sint (scast w\<^sub>2 + 0xFFFFFFFF80000001) \<le> - 2147483647"
          have bound1:"r\<^sub>1 \<le> - 2147483647"
            using leq1 geq1 by (auto simp add: NEG_INF_def)
          have bound2:"r\<^sub>2 \<le> r'\<^sub>2"
            using leq2 geq2 by auto        
          show "r\<^sub>1 + r\<^sub>2 \<le> r'\<^sub>2 - 2147483647"
            using bound1 bound2
            by(linarith)
        qed
      apply(rule disjI2)
      apply(rule disjI2)
      apply(auto)
      subgoal
        proof -
         have g:"(-0x7FFFFFFF::64 Word.word) = 0xFFFFFFFF80000001" by auto
         assume a:"\<not> sint (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
         then have sintw2_bound:"sint (((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
           unfolding g by auto 
         have case1a:" sint (((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) =  sint ((scast w\<^sub>2)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
           by(rule signed_arith_sint(1)[OF truth])
         have a1:"sint (((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF)) = sint((scast w\<^sub>2)::64 Word.word) + sint((-0x7FFFFFFF)::64 Word.word)" using case1a by auto
         have b1:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2" 
           apply(rule Word.sint_up_scast)
           unfolding Word.is_up by auto
         have c1:"sint((-0x7FFFFFFF)::64 Word.word) = -0x7FFFFFFF" 
           by auto
         have "- 0x7FFFFFFF < sint w\<^sub>2 + (- 0x7FFFFFFF)"
           using sintw2_bound case1a 
           using c1 scast_eq3 by linarith
         then have w2bound:"0 < sint w\<^sub>2" 
           using less_add_same_cancel2 by blast
         have rightSize:"sint (((scast w\<^sub>2)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
           unfolding case1a b1 c1 
           apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]  sints32 len32[of "TYPE(32)"])
           defer
           subgoal using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] by ( auto simp add:   sints32 len32[of "TYPE(32)"])
           using w2bound by auto
        have arith:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
          by auto
        have downcast:"sint ((scast (((scast w\<^sub>2)::64 Word.word) + ((- 0x7FFFFFFF))))::word) = sint (((scast w\<^sub>2)::64 Word.word) + ((- 0x7FFFFFFF)::64 Word.word)) "
          using scast_down_range[OF rightSize]
          by auto
        then have b:"sint ((scast (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001))::word) = sint (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001)" 
          using g by auto
        have c:"sint (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001) = sint ((scast w\<^sub>2)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word)"
          using g case1a by auto
        have d:"sint ((-0x7FFFFFFF)::64 Word.word) = (-0x7FFFFFFF)" by auto 
        have e:"sint ((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2" 
          using scast_eq3 by blast
        have f:"r'\<^sub>2 =  (real_of_int (sint w\<^sub>2))"
          by (simp add: leq2)
        show "r'\<^sub>2 -  2147483647 =  (real_of_int (sint ((scast (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001))::word)))"
          using a b c d e f 
          proof -
            have " (real_of_int (sint ((scast w\<^sub>2)::64 Word.word ) - 2147483647)) = r'\<^sub>2 - (real_of_int 2147483647)"
              by (simp add: e leq2)
            then show ?thesis
              using  b c d by(auto)
          qed
        qed
      subgoal  
      proof -
        have truth2a:" - (2 ^ (size ((scast w\<^sub>2)::64 Word.word) - 1)) \<le> sint ((scast w\<^sub>2)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) \<and> sint ((scast w\<^sub>2)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) \<le> 2 ^ (size ((scast w\<^sub>2)::64 Word.word) - 1) - 1"
          apply(auto simp add:
          Word.word_size[of "(scast w\<^sub>2)::64 Word.word"] Word.word_size[of "(scast (-0x7FFFFFFF))::64 Word.word"]
          scast_eq1 scast_eq2 
          Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]
          Word.word_sint.Rep[of "0x80000001::32 Word.word"]
          Word.word_sint.Rep[of "(scast w\<^sub>2)::64 Word.word"]
          Word.word_sint.Rep[of "-0x7FFFFFFF::64 Word.word"]
          sints64 sints32 thing2)
          using thing1 thing2 thing3 by auto
        have case2a:" sint (((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) =  sint ((scast w\<^sub>2)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
          by(rule signed_arith_sint(1)[OF truth2a])
        have min_cast:"(0xFFFFFFFF80000001::64 Word.word) =((scast (-0x7FFFFFFF::word))::64 Word.word)"
          by auto
        have neg64:"(((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001) = ((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF)" by auto
        assume "\<not> sint (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
        then have sintw2_bound:"sint (((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
          unfolding neg64 by auto 
        have a:"sint (((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF)) = sint((scast w\<^sub>2)::64 Word.word) + sint((-0x7FFFFFFF)::64 Word.word)" using case2a by auto
        have b:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2" 
          apply(rule Word.sint_up_scast)
          unfolding Word.is_up by auto
        have c:"sint((-0x7FFFFFFF)::64 Word.word) = -0x7FFFFFFF" 
          by auto
        have d:"sint w\<^sub>2 \<le> 2^31 - 1"
          using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] 
          by ( auto simp add:  sints32 len32[of "TYPE(32)"])
        have "- 0x7FFFFFFF < sint w\<^sub>2 + (- 0x7FFFFFFF)"
          using sintw2_bound case2a 
          using c scast_eq3 by linarith
        then have w2bound:"0 < sint w\<^sub>2" 
          using less_add_same_cancel2 by blast
        have rightSize:"sint (((scast w\<^sub>2)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
          unfolding case2a b c 
          apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]  sints32 len32[of "TYPE(32)"])
          defer
          subgoal using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] by ( auto simp add:   sints32 len32[of "TYPE(32)"])
          using w2bound by auto
        have arith:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
          by auto
        have downcast:"sint ((scast (((scast w\<^sub>2)::64 Word.word) + ((- 0x7FFFFFFF))))::word) = sint (((scast w\<^sub>2)::64 Word.word) + ((- 0x7FFFFFFF)::64 Word.word)) "
          using scast_down_range[OF rightSize]
          by auto
        have "sint (scast (((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF))::word) < 2147483647"
          unfolding downcast a b c
          using arith[of "sint w\<^sub>2", OF d]
          by auto
        then show "sint (scast (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001)::word) < 2147483647"
          by auto
      qed
      subgoal proof -
        assume notLeq:"\<not> sint (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
        then have gr:"sint (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001) > - 2147483647" 
          by auto
        have case2a:" sint (((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) =  sint ((scast w\<^sub>2)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
          by(rule signed_arith_sint(1)[OF truth])
        have min_cast:"(0xFFFFFFFF80000001::64 Word.word) =((scast (-0x7FFFFFFF::word))::64 Word.word)"
          by auto
        have neg64:"(((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001) = ((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF)" by auto
        then have sintw2_bound:"sint (((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
          unfolding neg64 using notLeq by auto 
        have a:"sint (((scast w\<^sub>2)::64 Word.word) + (-0x7FFFFFFF)) = sint((scast w\<^sub>2)::64 Word.word) + sint((-0x7FFFFFFF)::64 Word.word)" using case2a by auto
        have b:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2" 
          apply(rule Word.sint_up_scast)
          unfolding Word.is_up by auto
        have c:"sint((-0x7FFFFFFF)::64 Word.word) = -0x7FFFFFFF" 
          by auto
        have d:"sint w\<^sub>2 \<le> 2^31 - 1"
          using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] 
          by ( auto simp add:  sints32 len32[of "TYPE(32)"])
        have "- 0x7FFFFFFF < sint w\<^sub>2 + (- 0x7FFFFFFF)"
          using sintw2_bound case2a 
          using c scast_eq3 by linarith
        then have w2bound:"0 < sint w\<^sub>2" 
          using less_add_same_cancel2 by blast
        have rightSize:"sint (((scast w\<^sub>2)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
          unfolding case2a b c 
          apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]  sints32 len32[of "TYPE(32)"])
          defer
          subgoal using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] by ( auto simp add:   sints32 len32[of "TYPE(32)"])
          using w2bound by auto
        have downcast:"sint ((scast (((scast w\<^sub>2)::64 Word.word) + ((- 0x7FFFFFFF))))::word) = sint (((scast w\<^sub>2)::64 Word.word) + ((- 0x7FFFFFFF)::64 Word.word)) "
          using scast_down_range[OF rightSize]
          by auto
        have negEq:"(0xFFFFFFFF80000001:: 64 Word.word) = ((-0x7FFFFFFF)::64 Word.word)" by auto 
        have sintEq:" sint ((scast (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001))::word) =
            sint (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001) "
            using downcast by auto
        show "- 2147483647 < real_of_int (sint ((scast (((scast w\<^sub>2)::64 Word.word) + 0xFFFFFFFF80000001))::word))"
          unfolding sintEq  
          using gr of_int_less_iff of_int_minus of_int_numeral by linarith
        qed
        done
      
    show "(let sum = ?sum in if sum <=s scast NEG_INF then NEG_INF else scast sum) \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2"
      by (auto simp add: Let_def case1 case2)
  qed
  done
apply(cases "w\<^sub>2 = NEG_INF")
subgoal
    apply(simp)
    proof -
    assume neq1:"w\<^sub>1 \<noteq> POS_INF"
    assume eq2:"w\<^sub>2 = NEG_INF"
    assume neq3:"w\<^sub>1 \<noteq> NEG_INF"
    let ?sum = "(scast w\<^sub>1 + scast NEG_INF)::64 Word.word"
    have scast_eq1:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2" 
       apply(rule Word.sint_up_scast)
       unfolding Word.is_up by auto
    have scast_eq3:"sint((scast w\<^sub>1)::64 Word.word) = sint w\<^sub>1"
      apply(rule Word.sint_up_scast)
       unfolding Word.is_up by auto
    have scast_eq2:"sint((scast (0x80000001::word))::64 Word.word) = sint ((0x80000001::32 Word.word))"
       by auto
    have sints64:"sints 64 = {i. - (2 ^ 63) \<le> i \<and> i < 2 ^ 63}"
      using sints_def[of 64] Bit_Representation.range_sbintrunc[of 63] by auto 
    have sints32:"sints 32 = {i. - (2 ^ 31) \<le> i \<and> i < 2 ^ 31}"
      using sints_def[of 32] Bit_Representation.range_sbintrunc[of 31] by auto 
    have thing1:"0 \<le> 9223372034707292161 + ((-(2 ^ 31))::real)" by auto
    have thing2:"sint ((scast w\<^sub>1)::64 Word.word) \<ge> - (2 ^ 31) " 
      using Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] sints32 
      Word.word_size[of "(scast w\<^sub>1)::64 Word.word"] scast_eq1 scast_eq2 scast_eq3 len32 mem_Collect_eq 
      by auto
    have aLeq:"2 ^ 31 < (9223372039002259455::int)" by auto
    have bLeq:"sint ((scast w\<^sub>1)::64 Word.word) \<le> 2 ^ 31"
      apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] sints32 
          scast_eq3 len32)
      using Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] len32[of "TYPE(32)"] sints32 by auto
    have thing3:"sint ((scast w\<^sub>1)::64 Word.word) < 9223372039002259455"
      using aLeq bLeq by auto
    have truth:" - (2 ^ (size ((scast w\<^sub>1)::64 Word.word) - 1)) \<le> sint ((scast w\<^sub>1)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) 
    \<and> sint ((scast w\<^sub>1)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) \<le> 2 ^ (size ((scast w\<^sub>1)::64 Word.word) - 1) - 1"
      apply(auto simp add:
      Word.word_size[of "(scast w\<^sub>1)::64 Word.word"] Word.word_size[of "(scast (-0x7FFFFFFF))::64 Word.word"]
      scast_eq1 scast_eq2 
      Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"]
      Word.word_sint.Rep[of "0x80000001::32 Word.word"]
      Word.word_sint.Rep[of "(scast w\<^sub>1)::64 Word.word"]
      Word.word_sint.Rep[of "-0x7FFFFFFF::64 Word.word"]
      sints64 sints32 thing2)
      using thing1 thing2 thing3 by auto
    have case1a:" sint (((scast w\<^sub>1)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) =  sint ((scast w\<^sub>1)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
      by (rule signed_arith_sint(1)[of "(scast w\<^sub>1)::64 Word.word" "(- 0x7FFFFFFF)", OF truth])
    have case1b:"sint ((0xFFFFFFFF80000001)::64 Word.word) < 0"
      by auto
    have g:"(-0x7FFFFFFF::64 Word.word) = 0xFFFFFFFF80000001" by auto
    have c:"sint (((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001) = sint ((scast w\<^sub>1)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word)"
      using g case1a by auto
    have d:"sint ((-0x7FFFFFFF)::64 Word.word) = (-0x7FFFFFFF)" by auto 
    have e:"sint ((scast w\<^sub>1)::64 Word.word) = sint w\<^sub>1" 
      using scast_eq3 by blast
    have d2:"sint w\<^sub>1 \<le> 2^31 - 1"
      using Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] 
      by ( auto simp add:  sints32 len32[of "TYPE(32)"])
    have case1:"?sum <=s ((scast NEG_INF)::64 Word.word) \<Longrightarrow> NEG_INF \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2"
      using up1 up2 apply (simp add: repU_def NEG_INF_def repe.simps POS_INF_def word_sle_def)
      apply(rule exI[where x= "r\<^sub>1 + r\<^sub>2"])
      apply(auto)
      using case1a case1b 
      apply (auto simp add: NEG_INF_def neq1 eq2 neq3 repINT repU_def repe.simps repeInt_simps up2 word_sless_alt) 
      using repINT repU_def repe.simps repeInt_simps up2 word_sless_alt
      proof -
        fix r'
        assume a1:"sint ((scast w\<^sub>1)::64 Word.word) \<le> 0"
        then have h3:"sint w\<^sub>1 \<le> 0" using scast_eq3 by auto 
        assume a2:"r\<^sub>2 \<le> r'"
        assume a3:"r\<^sub>1 \<le>  (real_of_int (sint w\<^sub>1))"
        assume a4:"r' \<le>  (- 2147483647)"
        assume a5:"sint w\<^sub>1 < 2147483647"
        assume a6:"- 2147483647 < real_of_int (sint w\<^sub>1)"
        assume a7:"sint (scast w\<^sub>1 + 0xFFFFFFFF80000001) = sint (scast w\<^sub>1) - 2147483647"
        from a2 a4 have h1:"r\<^sub>2 \<le> - 2147483647" by auto
        from a1 a3 h3 have h2:"r\<^sub>1 \<le> 0" 
        using dual_order.trans of_int_le_0_iff by blast
        show "r\<^sub>1 + r\<^sub>2 \<le>  (- 2147483647)"
          using h1 h2 add.right_neutral add_mono by fastforce
      qed
    obtain r'\<^sub>1 and r'\<^sub>2 where   
          geq1:"r'\<^sub>1\<ge>r\<^sub>1" and equiv1:"w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1"
      and geq2:"r'\<^sub>2\<ge>r\<^sub>2" and equiv2:"w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2"
        using up1 up2 unfolding repU_def by auto
    have leq1:"r'\<^sub>2 \<le>  (real_of_int (sint NEG_INF))" and leq2:"r'\<^sub>1 =  (real_of_int (sint w\<^sub>1))" 
      using equiv1 equiv2 unfolding repe.simps
      using neq1 eq2 neq3 by auto
    have case1a:" sint (((scast w\<^sub>1)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) =  sint ((scast w\<^sub>1)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
      by(rule signed_arith_sint(1)[OF truth])
    have neg64:"(((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001) = ((scast w\<^sub>1)::64 Word.word) + (-0x7FFFFFFF)" by auto
    have case2:"\<not>(?sum <=s scast NEG_INF) \<Longrightarrow> scast ?sum \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2"
      apply (simp add: repU_def NEG_INF_def repe.simps POS_INF_def word_sle_def up1 up2)
      apply(rule exI[where x= "r'\<^sub>1 - 0x7FFFFFFF"]) (*r\<^sub>1 + r\<^sub>2*)
      apply(rule conjI)
      subgoal using leq1 leq2 geq1 geq2 unfolding NEG_INF_def by auto
      apply(rule disjI2)
      apply(rule disjI2)
      apply(auto)
      subgoal
        proof -
        have f:"r'\<^sub>1 =  (real_of_int (sint w\<^sub>1))"
          by (simp add: leq1 leq2 )
         assume a:"\<not> sint (((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
         then have sintw2_bound:"sint (((scast w\<^sub>1)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
           unfolding g by auto 
         have "- 0x7FFFFFFF < sint w\<^sub>1 + (- 0x7FFFFFFF)"
           using sintw2_bound case1a 
           using d scast_eq3 by linarith
         then have w2bound:"0 < sint w\<^sub>1" 
           using less_add_same_cancel2 by blast
         have rightSize:"sint (((scast w\<^sub>1)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
           unfolding case1a e 
           using w2bound Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"]
           by ( auto simp add:   sints32 len32[of "TYPE(32)"] )
        have arith:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
          by auto
        have downcast:"sint ((scast (((scast w\<^sub>1)::64 Word.word) + ((- 0x7FFFFFFF))))::word) = sint (((scast w\<^sub>1)::64 Word.word) + ((- 0x7FFFFFFF)::64 Word.word)) "
          using scast_down_range[OF rightSize]
          by auto
        then have b:"sint ((scast (((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001))::word) = sint (((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001)" 
          using g by auto
        show "r'\<^sub>1 -  2147483647 =  (real_of_int (sint ((scast (((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001))::word)))"
          using a b c d e f 
          proof -
            have " (real_of_int (sint ((scast w\<^sub>1)::64 Word.word ) - 2147483647)) = r'\<^sub>1 -  (real_of_int 2147483647)"
              by (simp add: e leq2)
            then show ?thesis
              by (metis b c d diff_minus_eq_add minus_minus of_int_numeral)
          qed
        qed
      subgoal  
      proof -
        assume "\<not> sint (((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
        then have sintw2_bound:"sint (((scast w\<^sub>1)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
          unfolding neg64 by auto 
        have "- 0x7FFFFFFF < sint w\<^sub>1 + (- 0x7FFFFFFF)"
          using sintw2_bound case1a 
          using d scast_eq3 by linarith
        then have w2bound:"0 < sint w\<^sub>1" 
          using less_add_same_cancel2 by blast
        have rightSize:"sint (((scast w\<^sub>1)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
          unfolding case1a e c 
          apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"]  sints32 len32[of "TYPE(32)"])
          defer
          subgoal using Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] by ( auto simp add:   sints32 len32[of "TYPE(32)"])
          using w2bound by auto
        have arith:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
          by auto
        have downcast:"sint ((scast (((scast w\<^sub>1)::64 Word.word) + ((- 0x7FFFFFFF))))::word) = sint (((scast w\<^sub>1)::64 Word.word) + ((- 0x7FFFFFFF)::64 Word.word)) "
          using scast_down_range[OF rightSize]
          by auto
        show "sint (scast (((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001)::word) < 2147483647"
          using downcast d e c arith[of "sint w\<^sub>1", OF d2]
          by auto
      qed
      subgoal proof -
        assume notLeq:"\<not> sint (((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
        then have gr:"sint (((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001) > - 2147483647" 
          by auto
        then have sintw2_bound:"sint (((scast w\<^sub>1)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
          unfolding neg64 using notLeq by auto 
        have "- 0x7FFFFFFF < sint w\<^sub>1 + (- 0x7FFFFFFF)"
          using sintw2_bound case1a 
          using d scast_eq3 by linarith
        then have w2bound:"0 < sint w\<^sub>1" 
          using less_add_same_cancel2 by blast
        have rightSize:"sint (((scast w\<^sub>1)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
          unfolding case1a e c 
          apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"]  sints32 len32[of "TYPE(32)"])
          defer
          subgoal using Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] by ( auto simp add:   sints32 len32[of "TYPE(32)"])
          using w2bound by auto
        show "- 2147483647 < real_of_int (sint ((scast (((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001))::word))"
          using scast_down_range[OF rightSize]    gr of_int_less_iff of_int_minus of_int_numeral by auto
        qed
        done
    show "(let sum = ?sum in if sum <=s scast NEG_INF then NEG_INF else scast sum) \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2"
      by (auto simp add: Let_def case1 case2)
    qed
apply simp
proof -
 assume notinf1:"w\<^sub>1 \<noteq> POS_INF"
 assume notinf2:"w\<^sub>2 \<noteq> POS_INF"
 assume notneginf1:"w\<^sub>1 \<noteq> NEG_INF"
 assume notneginf2:"w\<^sub>2 \<noteq> NEG_INF"
 let ?sum = "((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2):: 64 Word.word)"
 have inf_case:"scast POS_INF <=s ?sum \<Longrightarrow> POS_INF \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2"
   using  repU_def repePos_simps 
   by (meson dual_order.strict_trans not_less order_refl)
 have scast_eq1:"sint((scast w\<^sub>1)::64 Word.word) = sint w\<^sub>1" 
   apply(rule Word.sint_up_scast)
   unfolding Word.is_up by auto
 have scast_eq2:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2"
   apply(rule Word.sint_up_scast)
   unfolding Word.is_up by auto
 have sints64:"sints 64 = {i. - (2 ^ 63) \<le> i \<and> i < 2 ^ 63}"
   using sints_def[of 64] Bit_Representation.range_sbintrunc[of 63] by auto 
 have sints32:"sints 32 = {i. - (2 ^ 31) \<le> i \<and> i < 2 ^ 31}"
   using sints_def[of 32] Bit_Representation.range_sbintrunc[of 31] by auto 
 have truth:" - (2 ^ (size ((scast w\<^sub>1)::64 Word.word) - 1)) \<le> sint ((scast w\<^sub>1)::64 Word.word) + sint ((scast w\<^sub>2)::64 Word.word) \<and> sint ((scast w\<^sub>1)::64 Word.word) + sint ((scast w\<^sub>2)::64 Word.word) \<le> 2 ^ (size ((scast w\<^sub>1)::64 Word.word) - 1) - 1"
   using Word.word_size[of "(scast w\<^sub>2)::64 Word.word"] Word.word_size[of "(scast w\<^sub>1)::64 Word.word"]
   using scast_eq1 scast_eq2 
   Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"]
   Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]
   Word.word_sint.Rep[of "(scast w\<^sub>1)::64 Word.word"]
   Word.word_sint.Rep[of "(scast w\<^sub>2)::64 Word.word"]
   sints64 sints32 by auto 
 have sint_eq:"sint((scast w\<^sub>1 + scast w\<^sub>2)::64 Word.word) = sint w\<^sub>1 + sint w\<^sub>2"
   using signed_arith_sint(1)[of "(scast w\<^sub>1)::64 Word.word" "(scast w\<^sub>2)::64 Word.word", OF truth]
   using scast_eq1 scast_eq2
   by auto
 have bigOne:"scast w\<^sub>1 + scast w\<^sub>2 <=s ((- 0x7FFFFFFF)::64 Word.word) \<Longrightarrow> \<exists>r'\<ge>r\<^sub>1 + r\<^sub>2. r' \<le>  (- 0x7FFFFFFF)"
   proof -
     assume "scast w\<^sub>1 + scast w\<^sub>2 <=s ((- 0x7FFFFFFF)::64 Word.word)"
     then have sum_leq:"sint w\<^sub>1 + sint w\<^sub>2 \<le> - 0x7FFFFFFF"
           and sum_leq':" (sint w\<^sub>1 + sint w\<^sub>2) \<le>  (- 2147483647)"
       using sint_eq unfolding Word.word_sle_def by auto 
     obtain r'\<^sub>1 r'\<^sub>2 ::real where 
       bound1:"r'\<^sub>1 \<ge> r\<^sub>1 \<and> (w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1)" and
       bound2:"r'\<^sub>2 \<ge> r\<^sub>2 \<and> (w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2)"
       using up1 up2 unfolding repU_def by auto
     have somethingA:"r'\<^sub>1  \<le>  sint w\<^sub>1" and somethingB:"r'\<^sub>2  \<le>  sint w\<^sub>2" 
       using bound1 bound2 unfolding repe.simps POS_INF_def NEG_INF_def apply auto
       using \<open>scast w\<^sub>1 + scast w\<^sub>2 <=s - 0x7FFFFFFF\<close>  word_sle_def notinf1 notinf2 unfolding POS_INF_def
       by auto
     have something:"r'\<^sub>1 + r'\<^sub>2 \<le>  sint w\<^sub>1 + sint w\<^sub>2"
       using somethingA somethingB add_mono by fastforce  
     show "\<exists>r'\<ge>r\<^sub>1 + r\<^sub>2. r' \<le> (- 0x7FFFFFFF)"
       apply(rule exI[where x = "r'\<^sub>1 + r'\<^sub>2"])
       using bound1 bound2 add_mono something sum_leq' order.trans 
       by auto
   qed
   have anImp:"\<And>r'.  (r'\<ge>r\<^sub>1 + r\<^sub>2 \<and> r' \<le>  (- 2147483647)) \<Longrightarrow> 
    (\<exists>r. - (2 ^ 31 - 1) = - (2 ^ 31 - 1) \<and> r' = r \<and> r \<le>  (real_of_int (sint ((- (2 ^ 31 - 1))::32 Word.word))))"
      by auto
   have anEq:"((scast ((- (2 ^ 31 - 1))::32 Word.word))::64 Word.word) =  (- 0x7FFFFFFF)"
     by auto
   have bigTwo:
   "\<not>(((scast POS_INF)::64 Word.word) <=s ?sum) \<Longrightarrow> 
    \<not>(?sum <=s ((scast NEG_INF)::64 Word.word)) \<Longrightarrow> 
    \<exists>r'\<ge>r\<^sub>1 + r\<^sub>2. r' =  (real_of_int (sint (scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word))::word))) \<and> (r' <  0x7FFFFFFF \<and>  (-0x7FFFFFFF) < r')"
   proof -
     assume "\<not>(((scast POS_INF)::64 Word.word) <=s ?sum)"
     then have sum_leq:"sint w\<^sub>1 + sint w\<^sub>2 < 0x7FFFFFFF"
       unfolding Word.word_sle_def POS_INF_def using sint_eq by auto
     then have sum_leq':" (sint w\<^sub>1 + sint w\<^sub>2) <  (2147483647)"
       by auto
     assume "\<not>(?sum <=s ((scast NEG_INF)::64 Word.word))"
     then have sum_geq:"(- 0x7FFFFFFF) < sint w\<^sub>1 + sint w\<^sub>2"
       unfolding Word.word_sle_def NEG_INF_def using sint_eq by auto 
     then have sum_geq':" (- 2147483647) <  (sint w\<^sub>1 + sint w\<^sub>2)"
       by auto
     obtain r'\<^sub>1 r'\<^sub>2 ::real where 
       bound1:"r'\<^sub>1 \<ge> r\<^sub>1 \<and> (w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1)" and
       bound2:"r'\<^sub>2 \<ge> r\<^sub>2 \<and> (w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2)"
       using up1 up2 unfolding repU_def by auto
     have somethingA:"r'\<^sub>1  \<le>  sint w\<^sub>1" and somethingB:"r'\<^sub>2  \<le>  sint w\<^sub>2" 
       using bound1 bound2 unfolding repe.simps POS_INF_def NEG_INF_def apply auto
       using  word_sle_def notinf1 notinf2  unfolding POS_INF_def
       by auto
     have something:"r'\<^sub>1 + r'\<^sub>2 \<le>  sint w\<^sub>1 + sint w\<^sub>2"
       using somethingA somethingB add_mono by fastforce  
     have "(w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1)" using bound1 by auto
     then have
           r1w1:"r'\<^sub>1 =  (real_of_int (sint w\<^sub>1))"
       and w1U:" (real_of_int (sint w\<^sub>1)) <  (real_of_int (sint POS_INF))"
       and w1L:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint w\<^sub>1))"
       unfolding repe.simps
       using notinf1 notinf2 notneginf1 notneginf2 by (auto simp add: POS_INF_def NEG_INF_def)
     have "(w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2)" using bound2 by auto
     then have
           r2w1:"r'\<^sub>2 =  (real_of_int (sint w\<^sub>2))"
       and w2U:" (real_of_int (sint w\<^sub>2)) <  (real_of_int (sint POS_INF))"
       and w2L:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint w\<^sub>2))"
       unfolding repe.simps
       using notinf1 notinf2 notneginf1 notneginf2 by (auto simp add: POS_INF_def NEG_INF_def)
     have "sint (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)) = sint ((scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)))::word)"
       apply(rule scast_down_range)
       unfolding sint_eq using sints32 sum_geq sum_leq by auto
     then have cast_eq:"(sint ((scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)))::word)) = sint w\<^sub>1 + sint w\<^sub>2"
       using  scast_down_range
       unfolding sint_eq using sints32 sum_geq sum_leq 
       using sint_eq by auto
     from something and cast_eq 
     have r12_sint_scast:"r'\<^sub>1 + r'\<^sub>2 = (sint ((scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)))::word))"
       using r1w1 w1U w1L r2w1 w2U w2L by (simp)
     show ?thesis 
       using bound1 bound2 add_mono r12_sint_scast cast_eq sum_leq sum_leq' sum_geq' 
       \<open>r'\<^sub>1 + r'\<^sub>2 =  (real_of_int (sint (scast (scast w\<^sub>1 + scast w\<^sub>2))))\<close>
       by auto
   qed
   have neg_inf_case:"?sum <=s ((scast ((NEG_INF)::word))::64 Word.word)  \<Longrightarrow> NEG_INF \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2"
   proof (unfold repU_def NEG_INF_def repe.simps)
     assume "scast w\<^sub>1 + scast w\<^sub>2 <=s ((scast ((- (2 ^ 31 - 1))::word))::64 Word.word)"
     then have "scast w\<^sub>1 + scast w\<^sub>2 <=s ((- 0x7FFFFFFF)::64 Word.word)" 
       by (metis anEq)
     then obtain r' where geq:"(r' \<ge> r\<^sub>1 + r\<^sub>2)" and leq:"(r' \<le>  (- 0x7FFFFFFF))"
      using bigOne by auto
     show "(\<exists>r'\<ge>plus r\<^sub>1  r\<^sub>2.
       (\<exists>r. uminus (minus(2 ^ 31) 1) = POS_INF \<and> r' = r \<and>  (real_of_int (sint POS_INF)) \<le> r) \<or>
       (\<exists>r. uminus (minus(2 ^ 31) 1) = uminus (minus(2 ^ 31)  1) \<and> r' = r \<and> r \<le>  (real_of_int (sint ((uminus (minus(2 ^ 31) 1))::word)))) \<or>
       (\<exists>w. uminus (minus(2 ^ 31) 1) = w \<and>
            r' =  (real_of_int (sint w)) \<and>
             (real_of_int (sint w)) <  (real_of_int (sint POS_INF)) \<and> less ( (real_of_int (sint (uminus (minus(2 ^ 31)  1)))))  ( (real_of_int (sint w)))))"
       using  leq anImp geq by auto
   qed
 have int_case:"\<not>(((scast POS_INF)::64 Word.word) <=s ?sum) \<Longrightarrow> \<not> (?sum <=s ((scast NEG_INF)::64 Word.word)) \<Longrightarrow> ((scast ?sum)::word) \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2"
   proof -
     assume bound1:"\<not> ((scast POS_INF)::64 Word.word) <=s scast w\<^sub>1 + scast w\<^sub>2"
     assume bound2:"\<not> scast w\<^sub>1 + scast w\<^sub>2 <=s ((scast NEG_INF)::64 Word.word)"
     obtain r'::real  
     where
           rDef:"r' =  (real_of_int (sint ((scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)))::word)))"
       and r12:"r'\<ge>r\<^sub>1 + r\<^sub>2" 
       and boundU:"r' <  0x7FFFFFFF" 
       and boundL:" (-0x7FFFFFFF) < r'"
       using bigTwo[OF bound1 bound2] by auto
     obtain w::word 
     where wdef:"w = (scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word))::word)"
       by auto
     then have wr:"r' = (real_of_int (sint w))"
       using r12 bound1 bound2 rDef by blast
     show ?thesis
       unfolding repU_def NEG_INF_def repe.simps POS_INF_def 
       using r12 wdef rDef boundU boundL wr  
       by auto 
   qed
 show "(let sum::64 Word.word = scast w\<^sub>1 + scast w\<^sub>2 in if scast POS_INF <=s sum then POS_INF else if sum <=s scast NEG_INF then NEG_INF else scast sum) \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2"
   apply(cases "((scast POS_INF)::64 Word.word) <=s ((?sum)::64 Word.word)")
   subgoal using inf_case Let_def int_case neg_inf_case by auto
   apply(cases "?sum <=s scast NEG_INF")
   subgoal 
     using inf_case Let_def int_case neg_inf_case 
     proof -
       assume "\<not> (scast POS_INF::64 Word.word) <=s scast w\<^sub>1 + scast w\<^sub>2"
       then have "\<not> (scast w\<^sub>1::64 Word.word) + scast w\<^sub>2 <=s scast NEG_INF \<and> \<not> (scast POS_INF::64 Word.word) <=s scast w\<^sub>1 + scast w\<^sub>2 \<and> \<not> (scast w\<^sub>1::64 Word.word) + scast w\<^sub>2 <=s scast NEG_INF \<or> ((let w = scast w\<^sub>1 + scast w\<^sub>2 in if scast POS_INF <=s (w::64 Word.word) then POS_INF else if w <=s scast NEG_INF then NEG_INF else scast w) \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2)"
         using neg_inf_case by presburger
       then show ?thesis
         using int_case by force
     qed
   subgoal using inf_case Let_def int_case neg_inf_case 
   proof -
     assume a1: "\<not> (scast POS_INF::64 Word.word) <=s scast w\<^sub>1 + scast w\<^sub>2"
     assume "\<not> (scast w\<^sub>1::64 Word.word) + scast w\<^sub>2 <=s scast NEG_INF"
     have "\<not> (scast w\<^sub>1::64 Word.word) + scast w\<^sub>2 <=s scast NEG_INF \<and> \<not> (scast POS_INF::64 Word.word) <=s scast w\<^sub>1 + scast w\<^sub>2 \<or> ((let w = scast w\<^sub>1 + scast w\<^sub>2 in if scast POS_INF <=s (w::64 Word.word) then POS_INF else if w <=s scast NEG_INF then NEG_INF else scast w) \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2)"
       using a1 neg_inf_case by presburger
     then show ?thesis
       using int_case by force
   qed
   done
qed   

fun pl :: "word \<Rightarrow> word \<Rightarrow> word"
where "pl w1 w2 = 
(if w1 = NEG_INF then NEG_INF
 else if w2 = NEG_INF then NEG_INF
 else if w1 = POS_INF then 
  (if w2 = POS_INF then POS_INF 
   else
     (let sum::64 Word.word = ((scast w2)::64 Word.word) + ((scast POS_INF)::64 Word.word) in
     if ((scast POS_INF)::64 Word.word) <=s(sum::64 Word.word) then POS_INF
     else scast sum))
 else if w2 = POS_INF then 
  (let sum::64 Word.word = ((scast w1)::64 Word.word) + ((scast POS_INF)::64 Word.word) in
   if ((scast POS_INF)::64 Word.word) <=s(sum::64 Word.word)  then POS_INF
   else scast sum)
 else 
  (let sum::64 Word.word = ((scast w1)::64 Word.word) + ((scast w2)::64 Word.word) in
   if ((scast POS_INF)::64 Word.word) <=s (sum::64 Word.word) then POS_INF
   else if (sum::64 Word.word) <=s ((scast NEG_INF)::64 Word.word) then NEG_INF
   else scast sum))
"

lemma pl_lemma:
assumes lo1:"w\<^sub>1 \<equiv>\<^sub>L (r\<^sub>1::real)"
assumes lo2:"w\<^sub>2 \<equiv>\<^sub>L (r\<^sub>2::real)"
shows "pl w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>L (r\<^sub>1 + r\<^sub>2)"
apply(cases "w\<^sub>1 = NEG_INF")
subgoal 
  apply (auto simp add: POS_INF_def repL_def repe.simps NEG_INF_def)
  using linear by auto
apply(cases "w\<^sub>2 = NEG_INF")
subgoal 
  apply (auto simp add: POS_INF_def repL_def repe.simps NEG_INF_def)
  using linear by auto
apply(cases "w\<^sub>1 = POS_INF")
subgoal
  apply(cases "w\<^sub>2 = POS_INF")
  subgoal  
    using lo1 lo2 
    by (auto simp add: POS_INF_def NEG_INF_def repL_def repe.simps)
  subgoal
    apply(simp)
    proof -
    assume neq1:"w\<^sub>2 \<noteq> POS_INF"
    assume eq2:"w\<^sub>1 = POS_INF"
    assume neq3:"w\<^sub>2 \<noteq> NEG_INF"
    let ?sum = "(scast w\<^sub>2 + scast POS_INF)::64 Word.word"
    have scast_eq1:"sint((scast w\<^sub>1)::64 Word.word) = sint w\<^sub>1" 
      apply(rule Word.sint_up_scast)
      unfolding Word.is_up by auto
    have scast_eq3:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2"
      apply(rule Word.sint_up_scast)
      unfolding Word.is_up by auto
    have scast_eq2:"sint((scast (0x80000001::word))::64 Word.word) = sint ((0x80000001::32 Word.word))"
      by auto
    have sints64:"sints 64 = {i. - (2 ^ 63) \<le> i \<and> i < 2 ^ 63}"
      using sints_def[of 64] Bit_Representation.range_sbintrunc[of 63] by auto 
    have sints32:"sints 32 = {i. - (2 ^ 31) \<le> i \<and> i < 2 ^ 31}"
      using sints_def[of 32] Bit_Representation.range_sbintrunc[of 31] by auto 
    have thing1:"0 \<le> 9223372034707292161 + ((-(2 ^ 31))::real)" by auto
    have "sint (( w\<^sub>2)) \<ge> (-(2 ^ 31))"
      using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] sints32 
      Word.word_size[of "(scast w\<^sub>2)::64 Word.word"] scast_eq1 scast_eq2 scast_eq3 len32 mem_Collect_eq
      by auto
    then have thing4:"sint ((scast w\<^sub>2)::64 Word.word) \<ge> (-(2 ^ 31))" 
      using  scast_down_range sint_ge sints_num
      using scast_eq3 by linarith
    have aLeq2:"(-(2 ^ 31)::int) \<ge> -9223372039002259455" by auto 
    then have thing2:" (0::int) \<le> 9223372039002259455 + sint ((scast w\<^sub>2)::64 Word.word)"
      using thing4 aLeq2 
      by (metis ab_group_add_class.ab_left_minus add.commute add_mono neg_le_iff_le)
    have aLeq:"2 ^ 31 \<le> (9223372039002259455::int)" by auto
    have bLeq:"sint ((scast w\<^sub>2)::64 Word.word) \<le> 2 ^ 31"
      apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] sints32 
          scast_eq3 len32)
      using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] len32[of "TYPE(32)"] sints32 by auto
    have thing3:" sint ((scast w\<^sub>2)::64 Word.word) \<le> 9223372034707292160 "
      using aLeq bLeq by auto
    have truth:" - (2 ^ (size ((scast w\<^sub>2)::64 Word.word) - 1)) \<le> sint ((scast w\<^sub>2)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word) \<and> sint ((scast w\<^sub>2)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word) \<le> 2 ^ (size ((scast w\<^sub>2)::64 Word.word) - 1) - 1"
      by(auto simp add:
      Word.word_size[of "(scast w\<^sub>2)::64 Word.word"] Word.word_size[of "(scast (0x7FFFFFFF))::64 Word.word"]
      scast_eq1 scast_eq2 
      Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]
      Word.word_sint.Rep[of "-0x80000001::32 Word.word"]
      Word.word_sint.Rep[of "(scast w\<^sub>2)::64 Word.word"]
      Word.word_sint.Rep[of "0x7FFFFFFF::64 Word.word"]
      sints64 sints32 thing2 thing1 thing3)
    have case1a:" sint (((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF::64 Word.word)) =  sint ((scast w\<^sub>2)::64 Word.word) + sint (0x7FFFFFFF::64 Word.word)"
      by(rule signed_arith_sint(1)[OF truth])
    have case1b:"sint ((0xFFFFFFFF80000001)::64 Word.word) < 0"
      by auto
    have case1:" (((scast POS_INF)::64 Word.word) <=s ?sum) \<Longrightarrow> POS_INF \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2"
      using lo1 lo2 apply (simp add: repL_def NEG_INF_def repe.simps POS_INF_def word_sle_def)
      apply(rule exI[where x= "r\<^sub>1 + r\<^sub>2"])
      apply(auto)
      using case1a case1b 
      apply (auto simp add: NEG_INF_def POS_INF_def neq1 eq2 neq3 repINT repL_def repe.simps repeInt_simps lo2 word_sless_alt) 
      using repINT repL_def repe.simps repeInt_simps lo2 word_sless_alt
          NEG_INF_def POS_INF_def neq1 eq2 neq3 repINT repL_def repe.simps repeInt_simps lo2 word_sless_alt 
      apply (auto simp add: NEG_INF_def POS_INF_def)
     proof -
        fix r'
        assume a1:"0 \<le> sint (((scast w\<^sub>2)::64 Word.word))"
        from a1 have h3:"2147483647 \<le> sint w\<^sub>2  + 0x7FFFFFFF " using scast_eq3
          by auto
        assume a2:"r' \<le> r\<^sub>1"
        assume a3:" (real_of_int (sint w\<^sub>2)) \<le> r\<^sub>2 "
        assume a4:" ( 2147483647) \<le> r'"
        assume a5:"sint w\<^sub>2 < 2147483647"
        assume a6:"- 2147483647 < real_of_int (sint w\<^sub>2)"
        assume a7:"sint (scast w\<^sub>2 + 0x7FFFFFFF) = sint (scast w\<^sub>2) + 2147483647"
        from a2 a4 have h1:"2147483647 \<le> r\<^sub>1" by auto
        from a1 a3 h3 have h2:"0 \<le> r\<^sub>2" 
          using dual_order.trans of_int_le_0_iff le_add_same_cancel2 by fastforce
        show " (2147483647) \<le> r\<^sub>1 + r\<^sub>2 "
          using h1 h2 h3 add.right_neutral add_mono  
          by fastforce
        qed
    obtain r'\<^sub>1 and r'\<^sub>2 where   
              geq1:"r'\<^sub>1\<le>r\<^sub>1" and equiv1:"w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1"
          and geq2:"r'\<^sub>2\<le>r\<^sub>2" and equiv2:"w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2"
            using lo1 lo2 unfolding repL_def by auto
    have leq1:"r'\<^sub>1 \<ge>  (real_of_int (sint POS_INF))" 
      using equiv1 unfolding repe.simps
      using neq1 eq2 neq3 apply auto
        subgoal unfolding NEG_INF_def POS_INF_def by auto
        done
    have leq2:"r'\<^sub>2 = (real_of_int (sint w\<^sub>2))"
      using equiv2 unfolding repe.simps
      using neq1 eq2 neq3 by auto      
    have case2:"\<not>(scast POS_INF <=s ?sum) \<Longrightarrow> scast ?sum \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2"
      apply (simp add: repL_def NEG_INF_def repe.simps POS_INF_def word_sle_def lo1 lo2)
      apply(rule exI[where x= "r'\<^sub>2 + 0x7FFFFFFF"]) (*r\<^sub>1 + r\<^sub>2*)
      apply(rule conjI)
      subgoal 
        proof -
          assume " \<not> 2147483647 \<le> sint (scast w\<^sub>2 + 0x7FFFFFFF)"
          have bound1:"2147483647 \<le> r\<^sub>1"
            using leq1 geq1 by (auto simp add: POS_INF_def)
          have bound2:"r'\<^sub>2 \<le> r\<^sub>2 "
            using leq2 geq2 by auto        
          show "r'\<^sub>2 + 2147483647 \<le> r\<^sub>1 + r\<^sub>2"
            using bound1 bound2
            by linarith
        qed
      apply(rule disjI2)
      apply(rule disjI2)
      apply(auto)
      subgoal
        proof -
         assume a:"\<not> 2147483647 \<le> sint (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF)"
         then have sintw2_bound:"2147483647 > sint (((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF))"
           by auto 
         have case1a:" sint (((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF::64 Word.word)) =  sint ((scast w\<^sub>2)::64 Word.word) + sint (0x7FFFFFFF::64 Word.word)"
           by(rule signed_arith_sint(1)[OF truth])
         have a1:"sint (((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF)) = sint((scast w\<^sub>2)::64 Word.word) + sint((0x7FFFFFFF)::64 Word.word)" using case1a by auto
         have b1:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2" 
           apply(rule Word.sint_up_scast)
           unfolding Word.is_up by auto
         have c1:"sint((0x7FFFFFFF)::64 Word.word) = 0x7FFFFFFF" 
           by auto
         have "sint w\<^sub>2 + ( 0x7FFFFFFF) <  0x7FFFFFFF"
           using sintw2_bound case1a 
           using c1 scast_eq3 by linarith
         then have w2bound:"sint w\<^sub>2 < 0" 
           using add_less_same_cancel2 by blast
         have rightSize:"sint (((scast w\<^sub>2)::64 Word.word) +  0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
           unfolding case1a b1 c1 
           apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]  sints32 len32[of "TYPE(32)"])
           using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]   sints32 len32[of "TYPE(32)"]
           using w2bound by auto
        have arith:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
          by auto
        have downcast:"sint ((scast (((scast w\<^sub>2)::64 Word.word) + (( 0x7FFFFFFF))))::word) = sint (((scast w\<^sub>2)::64 Word.word) + (( 0x7FFFFFFF)::64 Word.word)) "
          using scast_down_range[OF rightSize]
          by auto
        then have b:"sint ((scast (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF))::word) = sint (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF)" 
          by auto
        have c:"sint (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF) = sint ((scast w\<^sub>2)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word)"
          using case1a by auto
        have d:"sint ((0x7FFFFFFF)::64 Word.word) = (0x7FFFFFFF)" by auto 
        have e:"sint ((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2" 
          using scast_eq3 by blast
        have f:"r'\<^sub>2 =  (real_of_int (sint w\<^sub>2))"
          by (simp add: leq2)
        show "r'\<^sub>2 +  2147483647 =  (real_of_int (sint ((scast (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF))::word)))"
          using a b c d e f 
          proof -
            have " (real_of_int (sint ((scast w\<^sub>2)::64 Word.word ) + 2147483647)) = r'\<^sub>2 +  (real_of_int 2147483647)"
              using  e leq2 by auto
            then show ?thesis
              by (metis b c d of_int_numeral)
          qed
        qed
      subgoal  
      proof -
        have truth2a:" - (2 ^ (size ((scast w\<^sub>2)::64 Word.word) - 1)) \<le> sint ((scast w\<^sub>2)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word) \<and> sint ((scast w\<^sub>2)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word) \<le> 2 ^ (size ((scast w\<^sub>2)::64 Word.word) - 1) - 1"
          apply(auto simp add:
          Word.word_size[of "(scast w\<^sub>2)::64 Word.word"] Word.word_size[of "(scast (0x7FFFFFFF))::64 Word.word"]
          scast_eq1 scast_eq2 
          Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]
          Word.word_sint.Rep[of "-0x80000001::32 Word.word"]
          Word.word_sint.Rep[of "(scast w\<^sub>2)::64 Word.word"]
          Word.word_sint.Rep[of "0x7FFFFFFF::64 Word.word"]
          sints64 sints32 thing2)
          using thing1 thing2 thing3 by auto
        have case2a:" sint (((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF::64 Word.word)) =  sint ((scast w\<^sub>2)::64 Word.word) + sint (0x7FFFFFFF::64 Word.word)"
          by(rule signed_arith_sint(1)[OF truth2a])
        have min_cast:"(0x7FFFFFFF::64 Word.word) =((scast (0x7FFFFFFF::word))::64 Word.word)"
          by auto
        have neg64:"(((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF) = ((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF)" by auto
        assume "\<not> 2147483647 \<le> sint (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF)"
        then have sintw2_bound:"2147483647 > sint (((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF))"
          using neg64 by auto
        have a:"sint (((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF)) = sint((scast w\<^sub>2)::64 Word.word) + sint((0x7FFFFFFF)::64 Word.word)" using case2a by auto
        have b:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2" 
          apply(rule Word.sint_up_scast)
          unfolding Word.is_up by auto
        have c:"sint((0x7FFFFFFF)::64 Word.word) = 0x7FFFFFFF" 
          by auto
        have " 0x7FFFFFFF > sint w\<^sub>2 + ( 0x7FFFFFFF)"
          using sintw2_bound case2a 
          using c scast_eq3 by linarith
        then have w2bound:" sint w\<^sub>2 < 0" 
          by simp
        have rightSize:"sint (((scast w\<^sub>2)::64 Word.word) +  0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
          unfolding case2a b c 
          apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]  sints32 len32[of "TYPE(32)"])
          using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]   sints32 len32[of "TYPE(32)"]
          using w2bound by auto
        have arith:"\<And>x::int. x < 0 \<Longrightarrow> x + ( 2147483647) < 2147483647"
          by auto
        have downcast:"sint ((scast (((scast w\<^sub>2)::64 Word.word) + (( 0x7FFFFFFF))))::word) = sint (((scast w\<^sub>2)::64 Word.word) + (( 0x7FFFFFFF)::64 Word.word)) "
          using scast_down_range[OF rightSize]
          by auto
        have "sint (scast (((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF))::word) < 2147483647"
          unfolding downcast a b c
          using arith[of "sint w\<^sub>2", OF w2bound]
          by auto
        then show "sint (scast (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF)::word) < 2147483647"
          by auto
      qed
      subgoal proof -
        assume notLeq:"\<not> 2147483647 \<le> sint (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF)"
        then have gr:"sint (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF) <  2147483647" 
          by auto
        have case2a:" sint (((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF::64 Word.word)) =  sint ((scast w\<^sub>2)::64 Word.word) + sint (0x7FFFFFFF::64 Word.word)"
          by(rule signed_arith_sint(1)[OF truth])
        have min_cast:"(0x7FFFFFFF::64 Word.word) =((scast (0x7FFFFFFF::word))::64 Word.word)"
          by auto
        have neg64:"(((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF) = ((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF)" by auto
        then have sintw2_bound:"sint (((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF)) < 2147483647"
          using neg64 using notLeq by auto 
        have a:"sint (((scast w\<^sub>2)::64 Word.word) + (0x7FFFFFFF)) = sint((scast w\<^sub>2)::64 Word.word) + sint((0x7FFFFFFF)::64 Word.word)" using case2a by auto
        have b:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2" 
          apply(rule Word.sint_up_scast)
          unfolding Word.is_up by auto
        have c:"sint((0x7FFFFFFF)::64 Word.word) = 0x7FFFFFFF" 
          by auto
        have "- 2147483647 \<noteq> w\<^sub>2" using neq3 unfolding NEG_INF_def by auto
        then have "sint((- 2147483647)::word) \<noteq> sint w\<^sub>2"
          using word_sint.Rep_inject by blast
        then have n1:"- 2147483647 \<noteq> sint w\<^sub>2"
          by auto
        have "- 2147483648 \<noteq> w\<^sub>2"
          apply(rule repe.cases[OF equiv2] )
          subgoal unfolding POS_INF_def by auto
          subgoal unfolding NEG_INF_def by auto
          using int_not_undef[of w\<^sub>2] unfolding NEG_INF_def 
          by simp
        then have "sint(- 2147483648::word) \<noteq> sint w\<^sub>2"
        using word_sint.Rep_inject by blast
        then have n2:"- 2147483648 \<noteq> sint w\<^sub>2" 
          by auto
        then have d:"sint w\<^sub>2 > - 2147483647"
          using Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] 
          using  sints32 len32[of "TYPE(32)"]
          using neq3 unfolding NEG_INF_def apply (clarsimp)
          using n1 n2 
          by linarith
        then have " - 2147483647 < sint w\<^sub>2"
          by blast
        have w2bound:" - 2147483647 < sint w\<^sub>2 + ( 0x7FFFFFFF)"
          using sintw2_bound case2a 
          using c scast_eq3  
          using d by linarith
        have rightSize:"sint (((scast w\<^sub>2)::64 Word.word) +  0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
          unfolding case2a b c 
          apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]  sints32 len32[of "TYPE(32)"])
          using sints32 len32[of "TYPE(32)"] w2bound Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"] 
          apply linarith
          using c case2a scast_eq3 sintw2_bound by linarith
        have downcast:"sint ((scast (((scast w\<^sub>2)::64 Word.word) + (( 0x7FFFFFFF))))::word) = sint (((scast w\<^sub>2)::64 Word.word) + (( 0x7FFFFFFF)::64 Word.word)) "
          using scast_down_range[OF rightSize]
          by auto
        have sintEq:" sint ((scast (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF))::word) =
            sint (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF) "
            using downcast by auto
        show "- 2147483647 < real_of_int (sint ((scast (((scast w\<^sub>2)::64 Word.word) + 0x7FFFFFFF))::word))"
          unfolding sintEq  
          using gr of_int_less_iff of_int_minus of_int_numeral
          using c case2a scast_eq3 w2bound by linarith
        qed
        done
    show "(let sum = ?sum in if scast POS_INF <=s sum then POS_INF else scast sum) \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2"
      by (auto simp add: Let_def case1 case2)
    qed
  done
apply(cases "w\<^sub>2 = POS_INF")
subgoal
    apply(simp)
    proof -
    assume neq3:"w\<^sub>1 \<noteq> NEG_INF"
    assume neq1:"w\<^sub>1 \<noteq> POS_INF"
    assume eq2:"w\<^sub>2 = POS_INF"
    let ?sum = "(scast w\<^sub>1 + scast POS_INF)::64 Word.word"
    have scast_eq1:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2" 
       apply(rule Word.sint_up_scast)
       unfolding Word.is_up by auto
    have scast_eq3:"sint((scast w\<^sub>1)::64 Word.word) = sint w\<^sub>1"
      apply(rule Word.sint_up_scast)
       unfolding Word.is_up by auto
    have scast_eq2:"sint((scast (0x80000001::word))::64 Word.word) = sint ((0x80000001::32 Word.word))"
       by auto
    have sints64:"sints 64 = {i. - (2 ^ 63) \<le> i \<and> i < 2 ^ 63}"
      using sints_def[of 64] Bit_Representation.range_sbintrunc[of 63] by auto 
    have sints32:"sints 32 = {i. - (2 ^ 31) \<le> i \<and> i < 2 ^ 31}"
      using sints_def[of 32] Bit_Representation.range_sbintrunc[of 31] by auto 
    have thing1:"0 \<le> 9223372034707292161 + ((-(2 ^ 31))::real)" by auto
    have "sint (( w\<^sub>1)) \<ge> (-(2 ^ 31))"
      using Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] sints32 
      Word.word_size[of "(scast w\<^sub>1)::64 Word.word"] scast_eq1 scast_eq2 scast_eq3 len32 mem_Collect_eq
      by auto
    then have thing4:"sint ((scast w\<^sub>1)::64 Word.word) \<ge> (-(2 ^ 31))" 
      using  scast_down_range sint_ge sints_num
      using scast_eq3 
      using scast_eq1 by linarith
    have aLeq2:"(-(2 ^ 31)::int) \<ge> -9223372039002259455" by auto 
    then have thing2:" (0::int) \<le> 9223372039002259455 + sint ((scast w\<^sub>1)::64 Word.word)"
      using thing4 aLeq2 
      by (metis ab_group_add_class.ab_left_minus add.commute add_mono neg_le_iff_le)
    have aLeq:"2 ^ 31 \<le> (9223372039002259455::int)" by auto
    have bLeq:"sint ((scast w\<^sub>1)::64 Word.word) \<le> 2 ^ 31"
      apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] sints32 
          scast_eq3 len32)
      using Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] len32[of "TYPE(32)"] sints32
      by clarsimp
    have thing3:" sint ((scast w\<^sub>1)::64 Word.word) \<le> 9223372034707292160 "
      using aLeq bLeq by auto
    have truth:" - (2 ^ (size ((scast w\<^sub>1)::64 Word.word) - 1)) \<le> sint ((scast w\<^sub>1)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word)
                 \<and> sint ((scast w\<^sub>1)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word) \<le> 2 ^ (size ((scast w\<^sub>1)::64 Word.word) - 1) - 1"
      by(auto simp add:
      Word.word_size[of "(scast w\<^sub>1)::64 Word.word"] Word.word_size[of "(scast (0x7FFFFFFF))::64 Word.word"]
      scast_eq1 scast_eq2 
      Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"]
      Word.word_sint.Rep[of "-0x80000001::32 Word.word"]
      Word.word_sint.Rep[of "(scast w\<^sub>1)::64 Word.word"]
      Word.word_sint.Rep[of "0x7FFFFFFF::64 Word.word"]
      sints64 sints32 thing2 thing1 thing3)
    have case1a:" sint (((scast w\<^sub>1)::64 Word.word) + (0x7FFFFFFF::64 Word.word)) =  sint ((scast w\<^sub>1)::64 Word.word) + sint (0x7FFFFFFF::64 Word.word)"
      by(rule signed_arith_sint(1)[OF truth])
    have case1b:"sint ((0xFFFFFFFF80000001)::64 Word.word) < 0"
      by auto
    have g:"(0x7FFFFFFF::64 Word.word) = 0x7FFFFFFF" by auto
    have c:"sint (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF) = sint ((scast w\<^sub>1)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word)"
      using g case1a 
      by blast
    have d:"sint ((0x7FFFFFFF)::64 Word.word) = (0x7FFFFFFF)" by auto 
    have e:"sint ((scast w\<^sub>1)::64 Word.word) = sint w\<^sub>1" 
      using scast_eq3 by blast
    have d2:"sint w\<^sub>1 \<le> 2^31 - 1"
      using Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] 
      by ( auto simp add:  sints32 len32[of "TYPE(32)"])
    have case1:"scast POS_INF <=s ?sum \<Longrightarrow> POS_INF \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2"
      using lo1 lo2 apply (simp add: repL_def NEG_INF_def repe.simps POS_INF_def word_sle_def)
      apply(rule exI[where x= "r\<^sub>1 + r\<^sub>2"])
      apply(auto)
      using case1a case1b 
      apply (auto simp add: NEG_INF_def POS_INF_def neq1 eq2 neq3 repINT repL_def repe.simps repeInt_simps lo2 word_sless_alt) 
      using repINT repU_def repe.simps repeInt_simps lo2 word_sless_alt
     proof -
        fix r'
        have h3:"sint (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF) = sint (((scast w\<^sub>1)::64 Word.word)) + sint(0x7FFFFFFF::64 Word.word)" 
          using case1a by auto 
        have h4:"sint(0x7FFFFFFF::64 Word.word) = 2147483647" by auto
        assume a1:"0 \<le> sint ((scast w\<^sub>1)::64 Word.word)"(*2147483647 \<le> sint (((scast w\<^sub>1)::64 Word.word) + (0x7FFFFFFF::64 Word.word))"*)
        then have h3:"sint w\<^sub>1 \<ge> 0" using scast_eq3 h3 h4 using  scast_eq3 h3 h4 by auto 
        assume a3:" (real_of_int (sint w\<^sub>1)) \<le> r\<^sub>1"
        assume a2:"r' \<le> r\<^sub>2"
        assume a4:" ( 2147483647) \<le> r'"
        assume a5:"sint w\<^sub>1 < 2147483647"
        assume a6:"- 2147483647 < real_of_int (sint w\<^sub>1)"
        from a2 a4 have h1:"r\<^sub>2 \<ge>  2147483647" by auto
        from a1 a3 h3 have h2:"r\<^sub>1 \<ge> 0" 
          using dual_order.trans of_int_0_le_iff by fastforce
        show " 2147483647 \<le> r\<^sub>1 + r\<^sub>2"
          using h1 h2 add.right_neutral add_mono by fastforce
        qed
    obtain r'\<^sub>1 and r'\<^sub>2 where   
          geq1:"r'\<^sub>1\<le>r\<^sub>1" and equiv1:"w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1"
      and geq2:"r'\<^sub>2\<le>r\<^sub>2" and equiv2:"w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2"
        using lo1 lo2 unfolding repL_def by auto
    have leq1:"r'\<^sub>2 \<ge>  (real_of_int (sint POS_INF))" and leq2:"r'\<^sub>1 =  (real_of_int (sint w\<^sub>1))" 
      using equiv1 equiv2 unfolding repe.simps
      using neq1 eq2 neq3 by auto
    have neg64:"(((scast w\<^sub>1)::64 Word.word) + 0xFFFFFFFF80000001) = ((scast w\<^sub>1)::64 Word.word) + (-0x7FFFFFFF)" by auto
    have case2:"\<not>(scast POS_INF <=s ?sum) \<Longrightarrow> scast ?sum \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2"
      apply (simp add: repL_def NEG_INF_def repe.simps POS_INF_def word_sle_def lo1 lo2)
      apply(rule exI[where x= "r'\<^sub>1 + 0x7FFFFFFF"]) (*r\<^sub>1 + r\<^sub>2*)
      apply(rule conjI)
      subgoal 
        proof -
          assume " \<not> 2147483647 \<le> sint (scast w\<^sub>1 + 0x7FFFFFFF)"
          have bound1:"r\<^sub>2 \<ge>  2147483647"
            using leq1 geq2 by (auto simp add: POS_INF_def)
          have bound2:"r\<^sub>1 \<ge> r'\<^sub>1"
            using leq2 geq1 by auto        
          show "r'\<^sub>1 + 2147483647 \<le> r\<^sub>1 + r\<^sub>2"
            using bound1 bound2
            by linarith
          qed
      apply(rule disjI2)
      apply(rule disjI2)
      apply(auto)
      subgoal
        proof -
        have f:"r'\<^sub>1 =  (real_of_int (sint w\<^sub>1))"
          by (simp add: leq1 leq2 )
         assume a:"\<not> 2147483647 \<le> sint (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF)"
         then have sintw2_bound:"2147483647 > sint (((scast w\<^sub>1)::64 Word.word) + (0x7FFFFFFF))"
           by auto 
         have "0x7FFFFFFF > sint w\<^sub>1 + ( 0x7FFFFFFF)"
           using sintw2_bound case1a 
           using d scast_eq3 by linarith
         then have w2bound:"0 > sint w\<^sub>1" 
           using add_less_same_cancel2 by blast
         have rightSize:"sint (((scast w\<^sub>1)::64 Word.word) +  0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
           unfolding case1a e 
           using w2bound Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"]
           by ( auto simp add:   sints32 len32[of "TYPE(32)"] )
        have arith:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
          by auto
        have downcast:"sint ((scast (((scast w\<^sub>1)::64 Word.word) + (( 0x7FFFFFFF))))::word) = sint (((scast w\<^sub>1)::64 Word.word) + (( 0x7FFFFFFF)::64 Word.word)) "
          using scast_down_range[OF rightSize]
          by auto
        then have b:"sint ((scast (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF))::word) = sint (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF)" 
          using g by auto
        show "r'\<^sub>1 +  2147483647 =  (real_of_int (sint ((scast (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF))::word)))"
          using a b c d e f 
          proof -
            have " (real_of_int (sint ((scast w\<^sub>1)::64 Word.word ) + 2147483647)) = r'\<^sub>1 +  (real_of_int 2147483647)"
              using e leq2 by auto
            then show ?thesis
              using  b c d of_int_numeral by metis
          qed
        qed
      subgoal  
      proof -
        assume "\<not> 2147483647 \<le> sint (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF) "
        then have sintw2_bound:"sint (((scast w\<^sub>1)::64 Word.word) + (0x7FFFFFFF)) < 2147483647"
          unfolding neg64 by auto 
        have "0x7FFFFFFF > sint w\<^sub>1 + (0x7FFFFFFF)"
          using sintw2_bound case1a 
          using d scast_eq3 by linarith
        then have w2bound:"0 > sint w\<^sub>1" 
          using add_less_same_cancel2 by blast
        have rightSize:"sint (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
          unfolding case1a e c 
          apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"]  sints32 len32[of "TYPE(32)"])
          defer
          using Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] sints32 len32[of "TYPE(32)"]
          using w2bound by auto
        have arith:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
          by auto
        have downcast:"sint ((scast (((scast w\<^sub>1)::64 Word.word) + (( 0x7FFFFFFF))))::word) = sint (((scast w\<^sub>1)::64 Word.word) + (( 0x7FFFFFFF)::64 Word.word)) "
          using scast_down_range[OF rightSize]
          by auto
        show "sint (scast (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF)::word) < 2147483647"
          using downcast d e c arith[of "sint w\<^sub>1", OF d2]
          using sintw2_bound by linarith
      qed
      subgoal proof -
        assume notLeq:"\<not> 2147483647 \<le> sint (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF)"
        then have gr:"2147483647 > sint (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF)" 
          by auto
        then have sintw2_bound:"sint (((scast w\<^sub>1)::64 Word.word) + (0x7FFFFFFF)) < 2147483647"
          unfolding neg64 using notLeq by auto 
        have " 0x7FFFFFFF > sint w\<^sub>1 + ( 0x7FFFFFFF)"
          using sintw2_bound case1a 
          using d scast_eq3 by linarith
        then have useful:"0 > sint w\<^sub>1"
          using add_less_same_cancel2 by blast
        have rightSize:"sint (((scast w\<^sub>1)::64 Word.word) +  0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
          unfolding case1a e c 
          apply ( auto simp add: Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"]  sints32 len32[of "TYPE(32)"])
          using Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"]  sints32 len32[of "TYPE(32)"]
          apply clarsimp
          using useful by linarith
        have "- 2147483647 \<noteq> w\<^sub>1" using neq3 unfolding NEG_INF_def by auto
        then have "sint((- 2147483647)::word) \<noteq> sint w\<^sub>1"
          using word_sint.Rep_inject by blast
        then have n1:"- 2147483647 \<noteq> sint w\<^sub>1"
          by auto
        have "- 2147483648 \<noteq> w\<^sub>1"
          apply(rule repe.cases[OF equiv1] )
          subgoal unfolding POS_INF_def by auto
          subgoal unfolding NEG_INF_def by auto
          using int_not_undef[of w\<^sub>1] unfolding NEG_INF_def 
          by simp
        then have "sint(- 2147483648::word) \<noteq> sint w\<^sub>1"
        using word_sint.Rep_inject by blast
        then have n2:"- 2147483648 \<noteq> sint w\<^sub>1" 
          by auto
        then have d:"sint w\<^sub>1 > - 2147483647"
          using Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"] 
          using  sints32 len32[of "TYPE(32)"]
          using neq3 unfolding NEG_INF_def apply (clarsimp)
          using n1 n2 
          by linarith
        have d2:"sint (0x7FFFFFFF::64 Word.word) > 0"
          by auto
        from d d2 have d3:"- 2147483647 < sint w\<^sub>1 + sint (0x7FFFFFFF::64 Word.word)"
          by auto
        have d4:"sint ((scast (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF))::word) = sint w\<^sub>1 + sint (0x7FFFFFFF::64 Word.word)"
          using case1a rightSize scast_down_range scast_eq3 by fastforce  
        then show " - 2147483647 < real_of_int (sint ((scast (((scast w\<^sub>1)::64 Word.word) + 0x7FFFFFFF))::word))"
          using d3 d4 by auto
        qed done
    show "(let sum = ?sum in if scast POS_INF <=s sum then POS_INF else scast sum) \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2"
      by (auto simp add: Let_def case1 case2)
    qed
apply simp
proof -
 assume notinf1:"w\<^sub>1 \<noteq> POS_INF"
 assume notinf2:"w\<^sub>2 \<noteq> POS_INF"
 assume notneginf1:"w\<^sub>1 \<noteq> NEG_INF"
 assume notneginf2:"w\<^sub>2 \<noteq> NEG_INF"
 let ?sum = "((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2):: 64 Word.word)"
 have scast_eq1:"sint((scast w\<^sub>1)::64 Word.word) = sint w\<^sub>1" 
   apply(rule Word.sint_up_scast)
   unfolding Word.is_up by auto
 have scast_eq2:"sint((scast w\<^sub>2)::64 Word.word) = sint w\<^sub>2"
   apply(rule Word.sint_up_scast)
   unfolding Word.is_up by auto
 have sints64:"sints 64 = {i. - (2 ^ 63) \<le> i \<and> i < 2 ^ 63}"
   using sints_def[of 64] Bit_Representation.range_sbintrunc[of 63] by auto 
 have sints32:"sints 32 = {i. - (2 ^ 31) \<le> i \<and> i < 2 ^ 31}"
   using sints_def[of 32] Bit_Representation.range_sbintrunc[of 31] by auto 
 have truth:" - (2 ^ (size ((scast w\<^sub>1)::64 Word.word) - 1)) \<le> sint ((scast w\<^sub>1)::64 Word.word) + sint ((scast w\<^sub>2)::64 Word.word) \<and> sint ((scast w\<^sub>1)::64 Word.word) + sint ((scast w\<^sub>2)::64 Word.word) \<le> 2 ^ (size ((scast w\<^sub>1)::64 Word.word) - 1) - 1"
   using Word.word_size[of "(scast w\<^sub>2)::64 Word.word"] Word.word_size[of "(scast w\<^sub>1)::64 Word.word"]
   using scast_eq1 scast_eq2 
   Word.word_sint.Rep[of "(w\<^sub>1)::32 Word.word"]
   Word.word_sint.Rep[of "(w\<^sub>2)::32 Word.word"]
   Word.word_sint.Rep[of "(scast w\<^sub>1)::64 Word.word"]
   Word.word_sint.Rep[of "(scast w\<^sub>2)::64 Word.word"]
   sints64 sints32 by auto 
 have sint_eq:"sint((scast w\<^sub>1 + scast w\<^sub>2)::64 Word.word) = sint w\<^sub>1 + sint w\<^sub>2"
   using signed_arith_sint(1)[of "(scast w\<^sub>1)::64 Word.word" "(scast w\<^sub>2)::64 Word.word", OF truth]
   using scast_eq1 scast_eq2
   by auto
 have bigOne:"scast w\<^sub>1 + scast w\<^sub>2 <=s ((- 0x7FFFFFFF)::64 Word.word) \<Longrightarrow> \<exists>r'\<le>r\<^sub>1 + r\<^sub>2. r' \<le>  (- 0x7FFFFFFF)"
   proof -
     assume "scast w\<^sub>1 + scast w\<^sub>2 <=s ((- 0x7FFFFFFF)::64 Word.word)"
     then have sum_leq:"sint w\<^sub>1 + sint w\<^sub>2 \<le> - 0x7FFFFFFF"
           and sum_leq':" (sint w\<^sub>1 + sint w\<^sub>2) \<le>  (- 2147483647)"
       using sint_eq unfolding Word.word_sle_def by auto 
     obtain r'\<^sub>1 r'\<^sub>2 ::real where 
       bound1:"r'\<^sub>1 \<le> r\<^sub>1 \<and> (w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1)" and
       bound2:"r'\<^sub>2 \<le> r\<^sub>2 \<and> (w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2)"
       using lo1 lo2 unfolding repL_def by auto
     have somethingA:"r'\<^sub>1  \<le>  sint w\<^sub>1" and somethingB:"r'\<^sub>2  \<le>  sint w\<^sub>2" 
       using bound1 bound2 unfolding repe.simps POS_INF_def NEG_INF_def apply auto
       using \<open>scast w\<^sub>1 + scast w\<^sub>2 <=s - 0x7FFFFFFF\<close>  word_sle_def notinf1 notinf2 unfolding POS_INF_def
       by auto
     have something:"r'\<^sub>1 + r'\<^sub>2 \<le>  sint w\<^sub>1 + sint w\<^sub>2"
       using somethingA somethingB add_mono 
       by fastforce  
     show "\<exists>r'\<le>r\<^sub>1 + r\<^sub>2. r' \<le>  (- 0x7FFFFFFF)"
       apply(rule exI[where x = "r'\<^sub>1 + r'\<^sub>2"])
       using bound1 bound2 add_mono something sum_leq' order.trans by auto
   qed
   have anImp:"\<And>r'.  (r'\<ge>r\<^sub>1 + r\<^sub>2 \<and> r' \<le>  (- 2147483647)) \<Longrightarrow> 
    (\<exists>r. - (2 ^ 31 - 1) = - (2 ^ 31 - 1) \<and> r' = r \<and> r \<le>  (real_of_int (sint ((- (2 ^ 31 - 1))::32 Word.word))))"
      by auto
   have anEq:"((scast ((- (2 ^ 31 - 1))::32 Word.word))::64 Word.word) =  (- 0x7FFFFFFF)"
     by auto
   have bigTwo:
   "\<not>(((scast POS_INF)::64 Word.word) <=s ?sum) \<Longrightarrow> 
    \<not>(?sum <=s ((scast NEG_INF)::64 Word.word)) \<Longrightarrow> 
    \<exists>r'\<le>r\<^sub>1 + r\<^sub>2. r' =  (real_of_int (sint (scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word))::word))) \<and> (r' <  0x7FFFFFFF \<and>  (-0x7FFFFFFF) < r')"
   proof -
     assume "\<not>(((scast POS_INF)::64 Word.word) <=s ?sum)"
     then have sum_leq:"sint w\<^sub>1 + sint w\<^sub>2 < 0x7FFFFFFF"
       unfolding Word.word_sle_def POS_INF_def using sint_eq by auto
     then have sum_leq':" (sint w\<^sub>1 + sint w\<^sub>2) <  (2147483647)"
       by auto
     assume "\<not>(?sum <=s ((scast NEG_INF)::64 Word.word))"
     then have sum_geq:"(- 0x7FFFFFFF) < sint w\<^sub>1 + sint w\<^sub>2"
       unfolding Word.word_sle_def NEG_INF_def using sint_eq by auto 
     then have sum_geq':" (- 2147483647) <  (sint w\<^sub>1 + sint w\<^sub>2)"
       by auto
     obtain r'\<^sub>1 r'\<^sub>2 ::real where 
       bound1:"r'\<^sub>1 \<le> r\<^sub>1 \<and> (w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1)" and
       bound2:"r'\<^sub>2 \<le> r\<^sub>2 \<and> (w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2)"
       using lo1 lo2 unfolding repL_def by auto
     have somethingA:"r'\<^sub>1  \<le>  sint w\<^sub>1" and somethingB:"r'\<^sub>2  \<le>  sint w\<^sub>2" 
       using bound1 bound2 unfolding repe.simps POS_INF_def NEG_INF_def apply auto
       using  word_sle_def notinf1 notinf2  unfolding POS_INF_def
       by auto
     have something:"r'\<^sub>1 + r'\<^sub>2 \<le>  sint w\<^sub>1 + sint w\<^sub>2"
       using somethingA somethingB add_mono 
       by fastforce  
     have "(w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1)" using bound1 by auto
     then have
           r1w1:"r'\<^sub>1 =  (real_of_int (sint w\<^sub>1))"
       and w1U:" (real_of_int (sint w\<^sub>1)) <  (real_of_int (sint POS_INF))"
       and w1L:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint w\<^sub>1))"
       unfolding repe.simps
       using notinf1 notinf2 notneginf1 notneginf2 by (auto simp add: POS_INF_def NEG_INF_def)
     have "(w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2)" using bound2 by auto
     then have
           r2w1:"r'\<^sub>2 =  (real_of_int (sint w\<^sub>2))"
       and w2U:" (real_of_int (sint w\<^sub>2)) <  (real_of_int (sint POS_INF))"
       and w2L:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint w\<^sub>2))"
       unfolding repe.simps
       using notinf1 notinf2 notneginf1 notneginf2 by (auto simp add: POS_INF_def NEG_INF_def)
     have "sint (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)) = sint ((scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)))::word)"
       apply(rule scast_down_range)
       unfolding sint_eq using sints32 sum_geq sum_leq by auto
     then have cast_eq:"(sint ((scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)))::word)) = sint w\<^sub>1 + sint w\<^sub>2"
       using  scast_down_range
       unfolding sint_eq using sints32 sum_geq sum_leq 
       using sint_eq by auto
     from something and cast_eq 
     have r12_sint_scast:"r'\<^sub>1 + r'\<^sub>2 = (sint ((scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)))::word))"
       using r1w1 w1U w1L r2w1 w2U w2L 
       by (simp)
     have leq_ref:"\<And>x y ::real. x = y ==> x \<le> y" by auto
     show ?thesis
       apply(rule exI[where x="r'\<^sub>1 + r'\<^sub>2"])
       apply(rule conjI)
       subgoal using r12_sint_scast cast_eq leq_ref r2w1  r1w1 add_mono[of r'\<^sub>1 r\<^sub>1 r'\<^sub>2 r\<^sub>2] bound1 bound2 by auto
       using bound1 bound2 add_mono r12_sint_scast cast_eq sum_leq sum_leq' sum_geq' sum_geq
       \<open>r'\<^sub>1 + r'\<^sub>2 =  (real_of_int (sint (scast (scast w\<^sub>1 + scast w\<^sub>2))))\<close> 
       by auto
   qed
   have neg_inf_case:"?sum <=s ((scast ((NEG_INF)::word))::64 Word.word)  \<Longrightarrow> NEG_INF \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2"
   proof (unfold repL_def NEG_INF_def repe.simps)
     assume "scast w\<^sub>1 + scast w\<^sub>2 <=s ((scast ((- (2 ^ 31 - 1))::word))::64 Word.word)"
     then have "scast w\<^sub>1 + scast w\<^sub>2 <=s ((- 0x7FFFFFFF)::64 Word.word)" 
       by (metis anEq)
     then obtain r' where geq:"(r' \<le> r\<^sub>1 + r\<^sub>2)" and leq:"(r' \<le>  (- 0x7FFFFFFF))"
      using bigOne by auto
     show "(\<exists>r'\<le>plus r\<^sub>1  r\<^sub>2.
       (\<exists>r. uminus (minus(2 ^ 31) 1) = POS_INF \<and> r' = r \<and>  (real_of_int (sint POS_INF)) \<le> r) \<or>
       (\<exists>r. uminus (minus(2 ^ 31) 1) = uminus (minus(2 ^ 31)  1) \<and> r' = r \<and> r \<le>  (real_of_int (sint ((uminus (minus(2 ^ 31) 1))::word)))) \<or>
       (\<exists>w. uminus (minus(2 ^ 31) 1) = w \<and>
            r' =  (real_of_int (sint w)) \<and>
             (real_of_int (sint w)) <  (real_of_int (sint POS_INF)) \<and> less ( (real_of_int (sint (uminus (minus(2 ^ 31)  1)))))  ( (real_of_int (sint w)))))"
       using  leq geq by auto
   qed
   have bigThree:"0x7FFFFFFF <=s ((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word) \<Longrightarrow> \<exists>r'\<le>r\<^sub>1 + r\<^sub>2.   (2147483647) \<le> r'"
   proof -
     assume "0x7FFFFFFF <=s ((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)"
     then have sum_leq:"0x7FFFFFFF \<le> sint w\<^sub>1 + sint w\<^sub>2 "
           and sum_leq':" 2147483647 \<le>  (sint w\<^sub>1 + sint w\<^sub>2)"
       using sint_eq unfolding Word.word_sle_def by auto 
     obtain r'\<^sub>1 r'\<^sub>2 ::real where 
       bound1:"r'\<^sub>1 \<le> r\<^sub>1 \<and> (w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1)" and
       bound2:"r'\<^sub>2 \<le> r\<^sub>2 \<and> (w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2)"
       using lo1 lo2 unfolding repL_def by auto
     have somethingA:"r'\<^sub>1  \<le>  sint w\<^sub>1" and somethingB:"r'\<^sub>2  \<le>  sint w\<^sub>2" 
       using bound1 bound2 unfolding repe.simps POS_INF_def NEG_INF_def apply auto
       using \<open> 0x7FFFFFFF <=s scast w\<^sub>1 + scast w\<^sub>2 \<close>  word_sle_def notinf1 notinf2 unfolding POS_INF_def
       by auto
     have something:"r'\<^sub>1 + r'\<^sub>2 \<le>  sint w\<^sub>1 + sint w\<^sub>2"
       using somethingA somethingB add_mono of_int_add  
       by fastforce  
     show "\<exists>r'\<le> r\<^sub>1 + r\<^sub>2.  (2147483647) \<le> r'"
       apply(rule exI[where x = "r'\<^sub>1 + r'\<^sub>2"])
       using bound1 bound2 add_mono something sum_leq' order.trans
      proof -
        have f1: " (real_of_int (sint w\<^sub>2)) = r'\<^sub>2"
          by (metis bound2 notinf2 notneginf2 repe.cases)
        have " (real_of_int (sint w\<^sub>1)) = r'\<^sub>1"
          by (metis bound1 notinf1 notneginf1 repe.cases)
        then have f2: " (real_of_int 2147483647) \<le> r'\<^sub>2 + r'\<^sub>1"
          using f1 sum_leq' by force
        have "r'\<^sub>2 + r'\<^sub>1 \<le> r\<^sub>2 + r\<^sub>1"
          by (meson add_left_mono add_right_mono bound1 bound2 order.trans)
        then show "r'\<^sub>1 + r'\<^sub>2 \<le> r\<^sub>1 + r\<^sub>2 \<and>  2147483647 \<le> r'\<^sub>1 + r'\<^sub>2"
          using f2 by (simp add: add.commute)
      qed
   qed

  have inf_case:"((scast POS_INF)::64 Word.word) <=s ?sum \<Longrightarrow> POS_INF \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2"
     proof -
     assume "((scast POS_INF)::64 Word.word) <=s ((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)"
     then have "((scast ((2 ^ 31 - 1)::word))::64 Word.word) <=s ((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)"
     unfolding  repL_def POS_INF_def repe.simps by auto
     then have "(0x7FFFFFFF::64 Word.word) <=s ((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)"
       by auto
     then obtain r' where geq:"(r' \<le> r\<^sub>1 + r\<^sub>2)" and leq:"(0x7FFFFFFF \<le> r')"
      using bigThree
      by auto
     show "?thesis"
     unfolding repL_def POS_INF_def repe.simps
     using leq geq
     by auto
   qed
 have int_case:"\<not>(((scast POS_INF)::64 Word.word) <=s ?sum) \<Longrightarrow> \<not> (?sum <=s ((scast NEG_INF)::64 Word.word)) \<Longrightarrow> ((scast ?sum)::word) \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2"
   proof -
     assume bound1:"\<not> ((scast POS_INF)::64 Word.word) <=s scast w\<^sub>1 + scast w\<^sub>2"
     assume bound2:"\<not> scast w\<^sub>1 + scast w\<^sub>2 <=s ((scast NEG_INF)::64 Word.word)"
     obtain r'::real  
     where
           rDef:"r' =  (real_of_int (sint ((scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word)))::word)))"
       and r12:"r'\<le>r\<^sub>1 + r\<^sub>2" 
       and boundU:"r' <  0x7FFFFFFF" 
       and boundL:" (-0x7FFFFFFF) < r'"
       using bigTwo[OF bound1 bound2] by auto
     obtain w::word 
     where wdef:"w = (scast (((scast w\<^sub>1)::64 Word.word) + ((scast w\<^sub>2)::64 Word.word))::word)"
       by auto
     then have wr:"r' =  (real_of_int (sint w))"
       using r12 bound1 bound2 rDef by blast
     show ?thesis
       unfolding repL_def NEG_INF_def repe.simps POS_INF_def 
       using r12 wdef rDef boundU boundL wr  
       by auto 
   qed
 show "(let sum = ?sum in if scast POS_INF <=s sum then POS_INF else if sum <=s scast NEG_INF then NEG_INF else scast sum) \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2"
   apply(cases "((scast POS_INF)::64 Word.word) <=s ?sum")
   subgoal by (auto simp add: Let_def inf_case) 
   apply(cases "?sum <=s scast NEG_INF")
   subgoal using neg_inf_case by auto
   subgoal using int_case by auto 
   done
qed   

fun wmax :: "word \<Rightarrow> word \<Rightarrow> word"
where "wmax w\<^sub>1 w\<^sub>2 = (if w\<^sub>1 <s w\<^sub>2 then w\<^sub>2 else w\<^sub>1)"

lemma wmax_lemma:
  assumes eq1:"w\<^sub>1 \<equiv>\<^sub>E (r\<^sub>1::real)"
  assumes eq2:"w\<^sub>2 \<equiv>\<^sub>E (r\<^sub>2::real)"
  shows "wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E (max r\<^sub>1 r\<^sub>2)"
  apply(rule repe.cases[OF eq1])
  subgoal for r
    apply(rule repe.cases[OF eq2])
    subgoal for ra 
      proof -
        assume p1:"w\<^sub>1 = POS_INF"
        assume p2:"w\<^sub>2 = POS_INF"
        assume eq1:"r\<^sub>1 = r"
        assume eq2:"r\<^sub>2 = ra"
        assume bound1:" (real_of_int (sint POS_INF)) \<le> r"
        assume bound2:" (real_of_int (sint POS_INF)) \<le> ra"
        have eqInf:"wmax w\<^sub>1 w\<^sub>2 = POS_INF"
          using p1 p2 unfolding POS_INF_def wmax.simps by auto
        have pos_eq:"POS_INF \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2"
          apply(rule repPOS_INF)
          using bound1 bound2 unfolding POS_INF_def eq1 eq2
          by linarith
        show ?thesis
          using pos_eq eqInf by auto
      qed
    subgoal for ra
      proof -
        assume p1:"w\<^sub>1 = POS_INF"
        assume n2:"w\<^sub>2 = NEG_INF"
        assume bound1:" (real_of_int (sint POS_INF)) \<le> r"
        assume bound2:"ra \<le>  (real_of_int (sint NEG_INF))"
        assume eq1:"r\<^sub>1 = r"
        assume eq2:"r\<^sub>2 = ra"
        have eqNeg:"wmax w\<^sub>1 w\<^sub>2 = POS_INF"
          unfolding NEG_INF_def POS_INF_def eq1 eq2 wmax.simps p1 n2 word_sless_def word_sle_def
          by(auto) 
        have neg_eq:"POS_INF \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2"
          apply(rule repPOS_INF)
          using bound1 bound2 unfolding POS_INF_def NEG_INF_def using eq1 eq2 by auto
        show "?thesis"
          using eqNeg neg_eq by auto
      qed
    subgoal for ra
      proof -
        assume p1:"w\<^sub>1 = POS_INF"
        assume i2:"w\<^sub>2 = ra"
        assume eq1:"r\<^sub>1 = r"
        assume eq2:"r\<^sub>2 =  (real_of_int (sint ra))"
        assume bound1:" (real_of_int (sint POS_INF)) \<le> r"
        assume bound2a:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint ra))"
        assume bound2b:" (real_of_int (sint ra)) <  (real_of_int (sint POS_INF))"
        have eqNeg:"wmax w\<^sub>1 w\<^sub>2 = POS_INF"
          using p1 i2 bound2b p1 unfolding NEG_INF_def POS_INF_def wmax.simps word_sless_def word_sle_def
          by auto 
        have neg_eq:"POS_INF \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2"
          apply (rule repPOS_INF)
          using bound1 bound2a bound2b unfolding POS_INF_def NEG_INF_def eq1 eq2 
          using bound2b p1 i2 word_sless_alt
          using le_max_iff_disj by blast
        show "?thesis"
          using eqNeg neg_eq by auto
        qed
    done
  subgoal for r
    apply(rule repe.cases[OF eq2])
    subgoal for ra 
      proof -
        assume eq1:"r\<^sub>1 = r"
        assume eq2:"r\<^sub>2 = ra" 
        assume n1:"w\<^sub>1 = NEG_INF"
        assume p2:"w\<^sub>2 = POS_INF"
        assume bound1:"r \<le>  (real_of_int (sint NEG_INF))"
        assume bound2:" (real_of_int (sint POS_INF)) \<le> ra"
        have eqNeg:"wmax w\<^sub>1 w\<^sub>2 = POS_INF"
          unfolding NEG_INF_def POS_INF_def eq1 eq2 wmax.simps n1 p2 word_sless_def word_sle_def
          by(auto)
        have neg_eq:"POS_INF \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2"
          apply(rule repPOS_INF)
          using bound1 bound2 unfolding POS_INF_def NEG_INF_def eq1 eq2 by auto
        show "wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2"
          using eqNeg neg_eq by auto
        qed
    subgoal for ra
      proof -
        assume n1:"w\<^sub>1 = NEG_INF"
        assume n2:"w\<^sub>2 = NEG_INF"
        assume eq1:"r\<^sub>1 = r"
        assume eq2:"r\<^sub>2 = ra"
        assume bound1:"r \<le>  (real_of_int (sint NEG_INF))"
        assume bound2:"ra \<le>  (real_of_int (sint NEG_INF))"
        have eqNeg:"NEG_INF \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2"
          apply(rule repNEG_INF)
          using eq1 eq2 bound1 bound2 unfolding NEG_INF_def
          by(auto)
        have neg_eq:"wmax w\<^sub>1 w\<^sub>2 = NEG_INF"
          using n1 n2 unfolding NEG_INF_def wmax.simps by auto 
        show "wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2"
          using eqNeg neg_eq by auto
      qed
    subgoal for ra
      proof -
        assume n1:"w\<^sub>1 = NEG_INF"
        assume i2:"w\<^sub>2 = ra"
        assume eq1:"r\<^sub>1 = r"
        assume eq2:"r\<^sub>2 =  (real_of_int (sint ra))"
        assume bound2a:" (real_of_int (sint ra)) <  (real_of_int (sint POS_INF))"
        assume bound2b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint ra))"
        assume bound1:"r \<le>  (real_of_int (sint NEG_INF))"
        have eqNeg:"max r\<^sub>1 r\<^sub>2 =  (real_of_int (sint ra))"
          using n1 i2 assms(2) bound2a eq2 n1 repeInt_simps bound1 bound2a bound2b
          by (metis eq1 less_irrefl max.bounded_iff max_def not_less)
        then have extra_eq:"(wmax w\<^sub>1 w\<^sub>2) = ra"
          using assms(2) bound2a eq2 i2 n1 repeInt_simps word_sless_alt by auto
        have neg_eq:"wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E  (real_of_int (sint (wmax w\<^sub>1 w\<^sub>2)))"
          apply(rule repINT)
          using NEG_INF_def bound1 bound2a bound2b eq1 min_le_iff_disj eqNeg extra_eq 
          by blast+
        show "wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2"
          using eqNeg neg_eq extra_eq by auto
        qed
      done
  subgoal for r
    apply(rule repe.cases[OF eq2])
    subgoal for ra
      proof -
        assume i1:"w\<^sub>1 = r"
        assume p2:"w\<^sub>2 = POS_INF"
        assume eq1:"r\<^sub>1 =  (real_of_int (sint r))"
        assume eq2:"r\<^sub>2 = ra"
        assume bound1a:" (real_of_int (sint r)) <  (real_of_int (sint POS_INF))"
        assume bound1b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint r))"
        assume bound2:" (real_of_int (sint POS_INF)) \<le> ra"
        have res1:"wmax w\<^sub>1 w\<^sub>2 = POS_INF"
          using i1 p2 eq1 eq2 unfolding POS_INF_def apply auto
          using assms(1) bound1b p2 repeInt_simps word_sless_alt by auto
        have res3:"POS_INF \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2"
          using repPOS_INF
          using POS_INF_def NEG_INF_def
          using i1 p2
          using POS_INF_def bound1a res1 bound1a bound1b bound2
          using eq2 le_max_iff_disj max.commute by blast
        show "wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2" 
          using res1 res3 by auto
        qed
    subgoal for ra
      proof -
        assume i1:"w\<^sub>1 = r"
        assume n2:"w\<^sub>2 = NEG_INF"
        assume eq1:"r\<^sub>1 =  (real_of_int (sint r))"
        assume eq2:"r\<^sub>2 = ra" 
        assume bound1a:" (real_of_int (sint r)) <  (real_of_int (sint POS_INF))"
        assume bound1b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint r))"
        assume bound2:"ra \<le>  (real_of_int (sint NEG_INF))"
        have res1:"max r\<^sub>1 r\<^sub>2 =  (real_of_int (sint (wmax w\<^sub>1 w\<^sub>2)))"
          using bound1a bound1b bound2 i1 leD less_trans n2 wmax.simps NEG_INF_def of_int_less_iff word_sless_alt
          by (metis (no_types, lifting) antisym_conv2 eq1 eq2 less_imp_le max_def)
        have res2:"wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E  (real_of_int (sint (wmax w\<^sub>1 w\<^sub>2)))"
          apply(rule repINT)
          using bound1a bound1b bound2
          using i1 leD leI less_trans n2 wmax.simps apply auto[1]
          using bound1a bound1b bound2 i1 leD leI 
          by (auto simp add: NEG_INF_def word_sless_alt)
        show "wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2"
          using res1 res2 by auto
        qed
    subgoal for ra
      proof -
        assume i1:"w\<^sub>1 = r"
        assume i2:"w\<^sub>2 = ra"
        assume eq1:"r\<^sub>1 =  (real_of_int (sint r))"
        assume eq2:"r\<^sub>2 =  (real_of_int (sint ra))"
        assume bound1a:" (real_of_int (sint r)) <  (real_of_int (sint POS_INF))"
        assume bound1b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint r))"
        assume bound2a:" (real_of_int (sint ra)) <  (real_of_int (sint POS_INF))"
        assume bound2b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint ra))"
        have res1:"max r\<^sub>1 r\<^sub>2 =  (real_of_int (sint (wmax w\<^sub>1 w\<^sub>2)))"
          using eq1 eq2 bound1a bound1b bound2a bound2b i1 i2
          by (simp add: max_def word_sless_alt)
        have res2:"wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E (real_of_int (sint (wmax w\<^sub>1 w\<^sub>2)))"
          apply (rule repINT)
          using i1 i2 bound1a bound1b bound2a bound2b
          by (simp add: \<open>max r\<^sub>1 r\<^sub>2 =  (real_of_int (sint (wmax w\<^sub>1 w\<^sub>2)))\<close> eq2 min_less_iff_disj)+
        show "wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E max r\<^sub>1 r\<^sub>2"
          using res1 res2 by auto
        qed
      done
    done


fun wtimes :: "word \<Rightarrow> word \<Rightarrow> word"
where "wtimes w1 w2 =
 (if w1 = POS_INF \<and> w2 = POS_INF then POS_INF
  else if w1 = NEG_INF \<and> w2 = POS_INF then NEG_INF
  else if w1 = POS_INF \<and> w2 = NEG_INF then NEG_INF
  else if w1 = NEG_INF \<and> w2 = NEG_INF then POS_INF
  
  else if w1 = POS_INF \<and> w2 <s 0 then NEG_INF 
  else if w1 = POS_INF \<and> 0 <s w2 then POS_INF 
  else if w1 = POS_INF \<and> 0 = w2 then 0 
  else if w1 = NEG_INF \<and> w2 <s 0 then POS_INF 
  else if w1 = NEG_INF \<and> 0 <s w2 then NEG_INF 
  else if w1 = NEG_INF \<and> 0 = w2 then 0 
  
  else if w1 <s 0 \<and> w2 = POS_INF then NEG_INF 
  else if 0 <s w1 \<and> w2 = POS_INF then POS_INF 
  else if 0 = w1 \<and> w2 = POS_INF then 0
  else if w1 <s 0 \<and> w2 = NEG_INF then POS_INF 
  else if 0 <s w1 \<and> w2 = NEG_INF then NEG_INF 
  else if 0 = w1 \<and> w2 = NEG_INF then 0 
  
  else 
  (let prod::64 Word.word = (scast w1) * (scast w2) in
   if prod <=s (scast NEG_INF) then NEG_INF
   else if (scast POS_INF) <=s prod then POS_INF
   else (scast prod)))"
 
lemma times_upcast_lower:
  fixes x y::int
  assumes a1:"x \<ge> -2147483648"
  assumes a2:"y \<ge> -2147483648"
  assumes a3:"x \<le> 2147483648"
  assumes a4:"y \<le> 2147483648"
  shows "- 4611686018427387904 \<le>  x * y"
proof -
  let ?thesis = "- 4611686018427387904 \<le> x * y"
  have is_neg:"- 4611686018427387904 < (0::int)" by auto
  have case1:"x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<ge> 0" and a6:"y \<ge> 0"
      have h1:"x * y \<ge> 0"
        using a5 a6 by (simp add: zero_le_mult_iff)
      then show ?thesis using is_neg by auto
    qed
  have case2:"x \<le> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> ?thesis" 
    proof -
      assume a5:"x \<le> 0" and a6:"y \<ge> 0"
      have h1:"-2147483648 * (2147483648) \<le> x * 2147483648"
        using a1 a2 a3 a4 a5 a6 by linarith
      have h2:"-2147483648 \<le> y" using a6 by auto
      have h3:"x * 2147483648 \<le> x * y" 
        using a1 a2 a3 a4 a5 a6 h2 
        using mult_left_mono_neg by blast
      show ?thesis using h1 h2 h3 by auto
    qed
  have case3:"x \<ge> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<ge> 0" and a6:"y \<le> 0"
      have h1:"2147483648 * (-2147483648) \<le> 2147483648 * y"
        using a1 a2 a3 a4 a5 a6 by linarith
      have h2:"-2147483648 \<le> x" using a5 by auto
      have h3:"2147483648 * y \<le> x * y" 
        using a1 a2 a3 a4 a5 a6 h2 
        using mult_left_mono_neg mult_right_mono_neg by blast
      show ?thesis using h1 h2 h3 by auto
    qed
  have case4:"x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> ?thesis"
  proof -
      assume a5:"x \<le> 0" and a6:"y \<le> 0"
      have h1:"x * y \<ge> 0"
        using a5 a6 by (simp add: zero_le_mult_iff)
      then show ?thesis using is_neg by auto
    qed
  show ?thesis
    using case1 case2 case3 case4 by linarith
qed
lemma times_upcast_upper:
  fixes x y ::int
  assumes a1:"x \<ge> -2147483648"
  assumes a2:"y \<ge> -2147483648"
  assumes a3:"x \<le> 2147483648"
  assumes a4:"y \<le> 2147483648"
  shows "x * y \<le> 4611686018427387904" 
proof -
  let ?thesis = "x * y \<le> 4611686018427387904"
  have case1:"x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<ge> 0" and a6:"y \<ge> 0"
      have h1:"2147483648 * 2147483648 \<ge> x * 2147483648"
        using a1 a2 a3 a4 a5 a6 by linarith
      have h2:"x * 2147483648 \<ge> x * y" 
        using a1 a2 a3 a4 a5 a6 by (simp add: mult_mono)
      show ?thesis using h1 h2 by auto
    qed
  have case2:"x \<le> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<le> 0" and a6:"y \<ge> 0"
      have h1:"2147483648 * 2147483648 \<ge> (0::int)" by auto
      have h2:"0 \<ge> x * y"
        using a5 a6 mult_nonneg_nonpos2 by blast
      show ?thesis using h1 h2 by auto
    qed
  have case3:"x \<ge> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<ge> 0" and a6:"y \<le> 0"
      have h1:"2147483648 * 2147483648 \<ge> (0::int)" by auto
      have h2:"0 \<ge> x * y"
        using a5 a6 mult_nonneg_nonpos by blast
      show ?thesis using h1 h2 by auto
    qed
  have case4:"x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<le> 0" and a6:"y \<le> 0"
      have h1:"-2147483648 * -2147483648 \<ge> x * -2147483648"
        using a1 a2 a3 a4 a5 a6 by linarith
      have h2:"x * -2147483648 \<ge> x * y" 
        using a1 a2 a3 a4 a5 a6 
         mult_left_mono_neg by blast
      show ?thesis using h1 h2 by auto
    qed
show "x * y \<le> 4611686018427387904"
  using case1 case2 case3 case4
  by linarith
qed
   
lemma wtimes_exact:
assumes eq1:"w1 \<equiv>\<^sub>E r1"
assumes eq2:"w2 \<equiv>\<^sub>E r2"
shows "wtimes w1 w2 \<equiv>\<^sub>E r1 * r2"
apply(cases "w1 = POS_INF \<and> w2 = POS_INF")
subgoal 
  using eq1 eq2 apply (auto simp add: POS_INF_def NEG_INF_def repe.simps)
  proof -
    assume a1: " 2147483647 \<le> r1"
    assume a2: " 2147483647 \<le> r2"
    have f3: "\<And>n e::real.  1 \<le> max ( (numeral n)) e"
      by (simp add: le_max_iff_disj)
    have "\<And>n e::real. 0 \<le> max ( (numeral n)) e"
        by (simp add: le_max_iff_disj)
    then have "r1 \<le> r1 * r2"
      using f3 a2 a1 by auto
    then show " 2147483647 \<le> r1 * r2"
      using a1 by linarith
  qed
apply(cases "w1 = NEG_INF \<and> w2 = POS_INF")
  subgoal proof -
    assume thatCase:"\<not>(w1 = POS_INF \<and> w2 = POS_INF)"
    assume thisCase:"w1 = NEG_INF \<and> w2 = POS_INF"
    from thatCase thisCase have notPos:"w1 \<noteq> POS_INF" by auto
    have a1: " (-2147483647) \<ge> r1"
      using eq1 thisCase by (auto simp add: POS_INF_def NEG_INF_def repe.simps)
    have a2: " 2147483647 \<le> r2"
      using eq2 thisCase by (auto simp add: POS_INF_def NEG_INF_def repe.simps)
    have f1: "real_of_int Numeral1 = 1"
      by simp
    have f3: " (real_of_int 3) \<le> - r1"
      using a1 by auto
    have "1 \<le> r2"
      using  f1 by (metis a2 dual_order.trans numeral_le_iff of_int_numeral semiring_norm(68))
    then have f4: "0 \<le> r2"
      by auto
    have f5: "r1 \<le>  (- 1)"
      using f3 by auto
    have fact:"r1 * r2 \<le> - r2"
      using f5 f4  mult_right_mono by fastforce
    show ?thesis
      apply (clarsimp simp add: repe.simps thisCase thatCase)
      apply(rule conjI)
      subgoal by auto
      unfolding NEG_INF_def
      apply simp
      using a1 a2 fact
      by(auto)
qed  
apply(cases "w1 = POS_INF \<and> w2 = NEG_INF")
subgoal proof -
    assume thisCase:"w1 = POS_INF \<and> w2 = NEG_INF"
    have a1: " (2147483647) \<le> r1"
      using eq1 thisCase by (auto simp add: POS_INF_def NEG_INF_def repe.simps)
    then have h1:"r1 \<ge> 1"
      by (metis max.bounded_iff max_def one_le_numeral)
    have a2: " (-2147483647) \<ge> r2"
      using eq2 thisCase by (auto simp add: POS_INF_def NEG_INF_def repe.simps)
    have f1: "\<not>  (- 2147483647::real) *  (- 1) \<le> 1"
      by auto
    have f2: "\<forall>e ea::real. (e *  (- 1) \<le> ea) = (ea *  (- 1) \<le> e)" by force
    then have f3: "\<not> 1 *  (- 1::real) \<le>  (- 2147483647)"
      using f1 by blast
    have f4: "r1 *  (- 1) \<le>  (- 2147483647)"
      using f2 a1 by force
    have f5: "\<forall>e ea eb. (if (ea::real) \<le> eb then e \<le> eb else e \<le> ea) = (e \<le> ea \<or> e \<le> eb)"
      by force
    have " 0 *  (- 1::real) \<le> 1"
      by simp
    then have "r1 *  (- 1) \<le>  0"
      using f5 f4 f3 f2 by meson
    then have f6: "0 \<le> r1" by fastforce
    have "1 *  (- 1) \<le>  (- 1::real)"
      using f2 by force
    then have fact:"r2 \<le>  (- 1)"
      using f3 a2 by fastforce
    show ?thesis
      apply (clarsimp simp add: repe.simps thisCase)
      apply(rule conjI)
      subgoal by auto
      unfolding POS_INF_def NEG_INF_def
      apply simp
      using a1 a2 h1 fact using f6 f5 f4
      by (meson mult_left_mono) 
    qed
apply(cases "w1 = NEG_INF \<and> w2 = NEG_INF")
subgoal proof -
  assume thisCase:"w1 = NEG_INF \<and> w2 = NEG_INF"
  have a1: "(-2147483647) \<ge> r1"
    using eq1 thisCase by (auto simp add: POS_INF_def NEG_INF_def repe.simps)
  then have h1:"r1 \<le> -1"
    using  max.bounded_iff max_def one_le_numeral
    by auto
  have a2: " (-2147483647) \<ge> r2"
    using eq2 thisCase by (auto simp add: POS_INF_def NEG_INF_def repe.simps)
    have f1: "\<forall>e ea eb. \<not> (e::real) \<le> ea \<or> \<not> 0 \<le> eb \<or> eb * e \<le> eb * ea"
  using mult_left_mono by metis
  have f2: "-  1 =  (- 1::real)"
    by force
  have f3: " 0 \<le>  (1::real)"
    by simp
  have f4: "\<forall>e ea eb. (ea::real) \<le> e \<or> \<not> ea \<le> eb \<or> \<not> eb \<le> e"
    by (meson less_le_trans not_le)
  have f5: " 0 \<le>  (2147483647::real)"
    by simp
  have f6: "-  (- 2147483647) =  (2147483647::real)"
    by force
  then have f7: "- ( (- 2147483647) * r1) =  (2147483647 * r1)"
    by (metis mult_minus_left)
  have f8: "- ( (- 2147483647) *  (- 1)) =  2147483647 *  (- 1::real)"
    by simp
  have " 2147483647 = -  1 *  (- 2147483647::real)"
    by simp
  then have f9: "r1 \<le>  (- 1) \<longrightarrow>  2147483647 \<le> r1 *  (- 2147483647)"
    using f8 f7 f5 f2 f1 by linarith
  have f10: "-  2147483647 =  (- 2147483647::real)"
    by fastforce
  have f11: "- (r2 *  1 * (r1 *  (- 1))) = r1 * r2"
    by (simp add: mult.commute)
  have f12: "r1 *  (- 1) = - (r1 *  1)"
    by simp
  have "r1 *  1 * ( (- 2147483647) *  1) =  (- 2147483647) * r1"
    by (simp add: mult.commute)
  then have f13: "r1 *  (- 1) * ( (- 2147483647) *  1) =  2147483647 * r1"
    using f12 f6 by (metis (no_types) mult_minus_left)
  have " 1 * r1 \<le>  1 *  (- 2147483647)"
    using a1 
    by (auto simp add: a1)
  then have " 2147483647 \<le> r1 *  (- 1)" by fastforce
  then have "0 \<le> r1 *  (- 1)"
    using f5 f4 by (metis)
  then have "r1 \<le>  (- 1) \<and> - (r1 *  2147483647) \<le> - (r2 *  1 * (r1 *  (- 1)))"
    using f13 f3 f2 f1 a2 h1 mult_left_mono_neg f11 \<open>r1 * 1 * (- 2147483647 * 1) = - 2147483647 * r1\<close>
    by (smt \<open>r1 * 1 * (- 2147483647 * 1) = - 2147483647 * r1\<close> f11 mult_left_mono_neg)
  then have "r1 \<le>  (- 1) \<and> r1 *  (- 2147483647) \<le> r2 * r1"
    using f11 f10 by (metis mult_minus_left mult.commute)
  then have fact:" 2147483647 \<le> r2 * r1"
    using f9 f4 by blast
    show ?thesis
      apply (clarsimp simp add: repe.simps thisCase)
      apply(rule conjI)
      subgoal by auto
      unfolding POS_INF_def NEG_INF_def
      apply simp
      using a1 a2 h1
      using fact by (metis mult.commute)
    qed
apply(cases "w1 = POS_INF \<and> w2 <s 0") 
  subgoal proof -
    assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
    assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
    assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
    assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
    assume theCase:"w1 = POS_INF \<and> w2 <s 0"
    from neq1 neq2 neq3 neq4 theCase
    have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF" by auto
    from eq1 theCase 
    have upper:" (real_of_int (sint POS_INF)) \<le> r1 " 
    by (auto simp add: repe.simps POS_INF_def NEG_INF_def)
    have lower1:"sint w2 < 0" using theCase 
      apply (auto simp add: word_sless_def word_sle_def)   
      by (simp add: dual_order.order_iff_strict)
    then have lower2:"sint w2 \<le> -1" by auto
    from eq2 have rw2:"r2 =  (real_of_int (sint w2))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto 
      show ?thesis
    using neq1 neq2 neq3 neq4 theCase apply simp
    unfolding repe.simps
    apply(rule disjI2)
    apply(rule disjI1)
    apply(rule exI[where x="r1 * r2"])
    apply(auto)
    using upper lower1 lower2 POS_INF_def NEG_INF_def rw2 apply (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
  proof -
    assume a1: " 2147483647 \<le> r1"
    assume a2: "sint w2 \<le> - 1"
    assume a3: "r2 =  (real_of_int (sint w2))"
    have f4: "r1 *  (- 1) \<le>  (- 2147483647)"
      using a1 by auto
    have f5: "r2 \<le>  (- 1)"
      using a3 a2 by simp
    have "0 < r1"
      using a1 by (meson less_le_trans not_le not_numeral_le_zero)
    then show "r1 *  (real_of_int (sint w2)) \<le>  (- 2147483647)"
      using f5 f4 a1 a2 a3
      mult_left_mono  less_le_trans not_le
    (*TODO: Simplify*)
    proof -
      have "\<forall>r. r < - 2147483647 \<or> \<not> r < r1 * - 1"
        using f4 less_le_trans by blast
      then show ?thesis
        by (metis \<open>0 < r1\<close> dual_order.order_iff_strict f5 mult_left_mono not_le rw2)
    qed
    qed qed
apply(cases "w1 = POS_INF \<and> 0 <s w2") subgoal 
  proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
    assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
    assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
    assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
    assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
    assume theCase:"w1 = POS_INF \<and> 0 <s w2"
    from neq1 neq2 neq3 neq4 neq5 theCase
    have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF" by auto
    from eq1 theCase 
    have upper:" (real_of_int (sint POS_INF)) \<le> r1 " 
    by (auto simp add: repe.simps POS_INF_def NEG_INF_def)
    have lower1:"sint w2 > 0" using theCase 
      apply (auto simp add: word_sless_def word_sle_def)   
      by (simp add: dual_order.order_iff_strict)
    then have lower2:"sint w2 \<ge> 1" by auto
    from eq2 have rw2:"r2 =  (real_of_int (sint w2))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto 
      show ?thesis
    using neq1 neq2 neq3 neq4 neq5 theCase apply simp
    unfolding repe.simps
    apply(rule disjI1)
    apply(rule exI[where x="r1 * r2"])
    apply(auto)
    using upper lower1 lower2 POS_INF_def NEG_INF_def rw2 apply (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
    proof -
      assume a1: " 2147483647 \<le> r1"
      assume a2: "1 \<le> sint w2"
      assume a3: "r2 =  (real_of_int (sint w2))"
      have "0 \<le> r1"
        using a1 by (meson dual_order.trans zero_le_numeral)
      then have "r1 \<le> r1 * r2"
        using a3 a2 by (metis (no_types)  mult_left_mono mult.right_neutral of_int_1_le_iff)
      then show " 2147483647 \<le> r1 *  (real_of_int (sint w2))"
        using a3 a1 dual_order.trans by blast
    qed    
  qed
apply(cases "w1 = POS_INF \<and> 0 = w2") subgoal 
  proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
  assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
  assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
  assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
  assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
  assume neq6:"\<not>(w1 = POS_INF \<and> 0 <s w2)"
  assume theCase:"w1 = POS_INF \<and> 0 = w2"
  from neq1 neq2 neq3 neq4 neq5 neq6 theCase
  have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF" by auto
  from eq1 theCase 
  have upper:" (real_of_int (sint POS_INF)) \<le> r1 " 
  by (auto simp add: repe.simps POS_INF_def NEG_INF_def)
  have lower1:"sint w2 = 0" using theCase 
    by (auto simp add: word_sless_def word_sle_def)   
  from eq2 have rw2:"r2 =  (real_of_int (sint w2))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto 
  show ?thesis
    using neq1 neq2 neq3 neq4 neq5 neq6 theCase apply simp
    unfolding repe.simps
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule exI[where x="0"])
    apply(auto)
    using upper lower1  POS_INF_def NEG_INF_def rw2 by (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
  qed 
apply(cases "w1 = NEG_INF \<and> w2 <s 0") subgoal 
  proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
  assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
  assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
  assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
  assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
  assume neq6:"\<not>(w1 = POS_INF \<and> 0 <s w2)"
  assume neq7:"\<not>(w1 = POS_INF \<and> 0 = w2)"
  assume theCase:"w1 = NEG_INF \<and> w2 <s 0"
  from neq1 neq2 neq3 neq4 neq5 neq6 theCase
  have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF" by auto
  from eq1 theCase 
  have upper:" (real_of_int (sint NEG_INF)) \<ge> r1 " 
  by (auto simp add: repe.simps POS_INF_def NEG_INF_def)
  have low:"sint w2 < 0" using theCase 
    apply (auto simp add: word_sless_def word_sle_def)
    by (simp add: dual_order.order_iff_strict)
  then have lower1:"  (real_of_int (sint w2)) < 0" by auto
  then have lower2:" (real_of_int (sint w2)) \<le> -1"  using low
  by (simp add: int_le_real_less) 
  from eq1 have rw1:"r1 \<le>  (real_of_int (sint w1))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by (simp add: upper)
  from eq2 have rw2:"r2 =  (real_of_int (sint w2))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto
  have hom:"  (- 2147483647) = -(2147483647::real)" by auto
  have mylem:"\<And>x y z::real. y < 0 \<Longrightarrow>   x \<le> y \<Longrightarrow> z \<le> -1 \<Longrightarrow> -y \<le> x * z"
    proof -
    fix x y z::real
    assume a1:"y < 0"
    assume a2:"x \<le> y"
    then have h1:"-x \<ge> -y" by auto
    assume a3:"z \<le> -1"
    then have a4:"z < 0" 
      by auto
    from a4 have h2:"-z > 0"  using leD leI by auto
    from a3 have h5:"-z \<ge> 1"  by (simp add: leD leI)
    have h4:"-x * -z \<ge> -y"
      using  a1 a2 a3 a4 h1 h2 h5   dual_order.trans  mult.right_neutral
      by (metis mult.commute neg_0_less_iff_less real_mult_le_cancel_iff1)
    have h3:"-x * -z = x * z" by auto
    show "- y \<le> x * z "
      using a1 a2 a3 a4 h1 h2 h3 h4 h5 
      by simp
    qed
  have prereqs:"- 2147483647 < (0::real)" " r1 \<le> - 2147483647" " (real_of_int (sint w2)) \<le> - 1"
    apply auto
    subgoal using rw1 theCase by (auto simp add: NEG_INF_def)
    using rw2 theCase lower2 by (auto simp add: word_sless_def word_sle_def NEG_INF_def lower2)
    
  show ?thesis
    using neq1 neq2 neq3 neq4 neq5 neq6 theCase apply simp
    unfolding repe.simps
    apply(rule disjI1)
    apply(rule exI[where x="r1 * r2"])
    using upper lower1 lower2 POS_INF_def NEG_INF_def rw1 rw2 apply (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
    using mylem[of "-2147483647" "r1" " (real_of_int (sint w2))"] prereqs by auto
  qed
apply(cases "w1 = NEG_INF \<and> 0 <s w2") subgoal 
proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
  assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
  assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
  assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
  assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
  assume neq6:"\<not>(w1 = POS_INF \<and> 0 <s w2)"
  assume neq7:"\<not>(w1 = POS_INF \<and> 0 = w2)"
  assume neq8:"\<not>(w1 = NEG_INF \<and> w2 <s 0)"
  assume theCase:"w1 = NEG_INF \<and> 0 <s w2"
  from neq1 neq2 neq3 neq4 neq5 neq6 theCase
  have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF" by auto
  from eq1 theCase 
  have upper:" (real_of_int (sint NEG_INF)) \<ge> r1 " 
  by (auto simp add: repe.simps POS_INF_def NEG_INF_def)
  have low:"sint w2 > 0" using theCase 
    apply (auto simp add: word_sless_def word_sle_def)
    by (simp add: dual_order.order_iff_strict)
  then have lower1:"  (real_of_int (sint w2)) > 0" by auto
  then have lower2:" (real_of_int (sint w2)) \<ge> 1"  using low
  by (simp add: int_le_real_less) 
  from eq1 have rw1:"r1 \<le>  (real_of_int (sint w1))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by (simp add: upper)
  from eq2 have rw2:"r2 =  (real_of_int (sint w2))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto
  have mylem:"\<And>x y z::real. x \<le> -1 \<Longrightarrow> y \<ge> 1 \<Longrightarrow> z \<le> -1 \<Longrightarrow> x \<le> z \<Longrightarrow>  x * y \<le> z"
    proof -
    fix x y z::real
    assume a1:"x \<le> -1"
    assume a2:"y \<ge> 1"
    then have h1:"-1 \<ge> -y" by auto
    assume a3:"z \<le> -1"
    then have a4:"z < 0"  by auto
    from a4 have h2:"-z > 0"  using leD leI by auto
    from a3 have h5:"-z \<ge> 1"  by (simp add: leD leI)
    assume a5:"x \<le> z"
    then have h6:"-x \<ge> -z" by auto
    have h3:"-x * -z = x * z" by auto
    show "x * y \<le> z"
      using a1 a2 a3 a5 a4 h1 h2 h3 h6 h5 a5 dual_order.trans   leD  mult.right_neutral
      by (metis dual_order.order_iff_strict mult_less_cancel_left2)
    qed
  have prereqs:"r1 \<le> - 1" "1 \<le>  (real_of_int (sint w2))" " (- 2147483647::real) \<le> - 1 " "r1 \<le>  (- 2147483647)"
    subgoal using rw1 theCase by (auto simp add: NEG_INF_def word_sless_def word_sle_def) 
    subgoal using rw2 theCase apply (auto simp add: NEG_INF_def word_sless_def word_sle_def)
      using  lower2 of_int_1_le_iff by blast
    subgoal by auto
    subgoal using rw1 theCase by (auto simp add: NEG_INF_def word_sless_def word_sle_def)
    done
  show ?thesis
    using neq1 neq2 neq3 neq4 neq5 neq6 neq7 neq8 theCase apply simp
    unfolding repe.simps
    apply(rule disjI2)
    apply(rule disjI1)
    apply(rule exI[where x="r1 * r2"])
    using upper lower1 lower2 POS_INF_def NEG_INF_def rw1 rw2 apply (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
    using mylem[of  "r1" " (real_of_int (sint w2))" " (- 2147483647)"] prereqs
    by auto
  qed
apply(cases "w1 = NEG_INF \<and> 0 = w2") subgoal 
proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
  assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
  assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
  assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
  assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
  assume neq6:"\<not>(w1 = POS_INF \<and> 0 <s w2)"
  assume neq7:"\<not>(w1 = POS_INF \<and> 0 = w2)"
  assume neq8:"\<not>(w1 = NEG_INF \<and> w2 <s 0)"
  assume neq9:"\<not>(w1 = NEG_INF \<and> 0 <s w2)"
  assume theCase:"w1 = NEG_INF \<and> 0 = w2"
  from neq1 neq2 neq3 neq4 neq5 neq6 theCase
  have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF" by auto
  from eq2 theCase  have rw2:"r2 = 0" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto
  show ?thesis
    using neq1 neq2 neq3 neq4 neq5 neq6 neq7 neq8 theCase apply simp
    unfolding repe.simps
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule exI[where x="0"])
    using POS_INF_def NEG_INF_def  rw2 by (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
  qed
apply(cases "w1 <s 0 \<and> w2 = POS_INF") subgoal 
proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
  assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
  assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
  assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
  assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
  assume neq6:"\<not>(w1 = POS_INF \<and> 0 <s w2)"
  assume neq7:"\<not>(w1 = POS_INF \<and> 0 = w2)"
  assume neq8:"\<not>(w1 = NEG_INF \<and> w2 <s 0)"
  assume neq9:"\<not>(w1 = NEG_INF \<and> 0 <s w2)"
  assume neq10:"\<not>(w1 = NEG_INF \<and> 0 = w2)"
  assume theCase:"w1 <s 0 \<and> w2 = POS_INF"
  from neq1 neq2 neq3 neq4 theCase
  have w2NotPinf:"w1 \<noteq> POS_INF" and w2NotNinf:"w1 \<noteq> NEG_INF" by auto
    from eq2 theCase 
  have upper:"(real_of_int (sint POS_INF)) \<le> r2 " 
    by (auto simp add: repe.simps POS_INF_def NEG_INF_def)
  have lower1:"sint w1 < 0" using theCase 
      apply (auto simp add: word_sless_def word_sle_def)   
      by (simp add: dual_order.order_iff_strict)
    then have lower2:"sint w1 \<le> -1" by auto
  from eq1 have rw1:"r1 = (real_of_int (sint w1))" 
  using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto 
    show ?thesis
    using neq1 neq2 neq3 neq4 theCase apply simp
    unfolding repe.simps
    apply(rule disjI2)
    apply(rule disjI1)
    apply(rule exI[where x="r1 * r2"])
    apply(auto)
    using upper lower1 lower2 POS_INF_def NEG_INF_def rw1 apply (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
  proof -
    assume a1: " 2147483647 \<le> r2"
    assume a2: "sint w1 \<le> - 1"
    assume a3: "r1 =  (real_of_int (sint w1))"
    have f4: "r2 *  (- 1) \<le>  (- 2147483647)"
      using a1 by linarith
    have f5: "r1 \<le>  (- 1)"
      using a3 a2 by simp
    have "0 < r2"
      using a1 by (meson  less_le_trans not_le not_numeral_le_zero)
    then show " (real_of_int (sint w1)) * r2 \<le>  (- 2147483647)"
      using f5 f4 a3 less_le_trans not_le
      proof -
        have "r2 * r1 \<le> r2 *  (- 1)"
          by (metis dual_order.order_iff_strict \<open>0 < r2\<close> mult_right_mono f5  mult.commute)
        then have "r2 * r1 \<le>  (- 2147483647)"
          by (meson f4 less_le_trans not_le)
        then show ?thesis
          using mult.commute rw1 
          by (simp add: mult.commute)
      qed qed qed
apply(cases "0 <s w1 \<and> w2 = POS_INF")
subgoal proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
  assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
  assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
  assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
  assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
  assume neq6:"\<not>(w1 = POS_INF \<and> 0 <s w2)"
  assume neq7:"\<not>(w1 = POS_INF \<and> 0 = w2)"
  assume neq8:"\<not>(w1 = NEG_INF \<and> w2 <s 0)"
  assume neq9:"\<not>(w1 = NEG_INF \<and> 0 <s w2)"
  assume neq10:"\<not>(w1 = NEG_INF \<and> 0 = w2)"
  assume neq11:"\<not>(w1 <s 0 \<and> w2 = POS_INF)"
  assume theCase:"0 <s w1 \<and> w2 = POS_INF"
  from neq1 neq2 neq3 neq4 neq5 theCase
  have w2NotPinf:"w1 \<noteq> POS_INF" and w2NotNinf:"w1 \<noteq> NEG_INF" by auto
  from eq2 theCase 
  have upper:" (real_of_int (sint POS_INF)) \<le> r2 " 
  by (auto simp add: repe.simps POS_INF_def NEG_INF_def)
  have lower1:"sint w1 > 0" using theCase 
    apply (auto simp add: word_sless_def word_sle_def)   
    by (simp add: dual_order.order_iff_strict)
  then have lower2:"sint w1 \<ge> 1" by auto
  from eq1 have rw2:"r1 =  (real_of_int (sint w1))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto 
    show ?thesis
  using neq1 neq2 neq3 neq4 neq5 neq6 neq7 neq8 neq9 neq10 neq11 theCase apply simp
  unfolding repe.simps
  apply(rule disjI1)
  apply(rule exI[where x="r1 * r2"])
  apply(auto)
  using upper lower1 lower2 POS_INF_def NEG_INF_def rw2 apply (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
  proof -
    assume a1: " 2147483647 \<le> r2"
    assume a2: "1 \<le> sint w1"
    assume a3: "r1 =  (real_of_int (sint w1))"
    have "0 \<le> r2"
      using a1 by (meson dual_order.trans  zero_le_numeral)
    then have "r2 \<le> r2 * r1"
      using a3 a2 by (metis (no_types) mult_left_mono mult.right_neutral   of_int_1_le_iff)
    then show " 2147483647 \<le>  (real_of_int (sint w1)) * r2"
      using a3 a1 dual_order.trans mult.commute by metis
  qed qed
apply(cases "0 = w1 \<and> w2 = POS_INF") subgoal
proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
  assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
  assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
  assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
  assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
  assume neq6:"\<not>(w1 = POS_INF \<and> 0 <s w2)"
  assume neq7:"\<not>(w1 = POS_INF \<and> 0 = w2)"
  assume neq8:"\<not>(w1 = NEG_INF \<and> w2 <s 0)"
  assume neq9:"\<not>(w1 = NEG_INF \<and> 0 <s w2)"
  assume neq10:"\<not>(w1 = NEG_INF \<and> 0 = w2)"
  assume neq11:"\<not>(w1 <s 0 \<and> w2 = POS_INF)"
  assume neq12:"\<not>(0 <s w1 \<and> w2 = POS_INF)"
  assume theCase:"0 = w1 \<and> w2 = POS_INF"
from neq1 neq2 neq3 neq4 neq5 neq6 theCase
  have w2NotPinf:"w1 \<noteq> POS_INF" and w2NotNinf:"w1 \<noteq> NEG_INF" by auto
  from eq2 theCase 
  have upper:" (real_of_int (sint POS_INF)) \<le> r2 " 
  by (auto simp add: repe.simps POS_INF_def NEG_INF_def)
  have lower1:"sint w1 = 0" using theCase 
    by (auto simp add: word_sless_def word_sle_def)   
  from eq1 have rw2:"r1 =  (real_of_int (sint w1))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto 
  show ?thesis
    using neq1 neq2 neq3 neq4 neq5 neq6 theCase apply simp
    unfolding repe.simps
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule exI[where x="0"])
    apply(auto)
    using upper lower1  POS_INF_def NEG_INF_def rw2 by (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
  qed 
apply(cases "w1 <s 0 \<and> w2 = NEG_INF") subgoal
proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
  assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
  assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
  assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
  assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
  assume neq6:"\<not>(w1 = POS_INF \<and> 0 <s w2)"
  assume neq7:"\<not>(w1 = POS_INF \<and> 0 = w2)"
  assume neq8:"\<not>(w1 = NEG_INF \<and> w2 <s 0)"
  assume neq9:"\<not>(w1 = NEG_INF \<and> 0 <s w2)"
  assume neq10:"\<not>(w1 = NEG_INF \<and> 0 = w2)"
  assume neq11:"\<not>(w1 <s 0 \<and> w2 = POS_INF)"
  assume neq12:"\<not>(0 <s w1 \<and> w2 = POS_INF)"
  assume neq13:"\<not>(0 = w1 \<and> w2 = POS_INF)"
  assume theCase:"w1 <s 0 \<and> w2 = NEG_INF"
  from neq1 neq2 neq3 neq4 neq5 neq6 theCase
  have w2NotPinf:"w1 \<noteq> POS_INF" and w2NotNinf:"w1 \<noteq> NEG_INF" by auto
  from eq2 theCase 
  have upper:" (real_of_int (sint NEG_INF)) \<ge> r2 " 
  by (auto simp add: repe.simps POS_INF_def NEG_INF_def)
  have low:"sint w1 < 0" using theCase 
    apply (auto simp add: word_sless_def word_sle_def)
    by (simp add: dual_order.order_iff_strict)
  then have lower1:"  (real_of_int (sint w1)) < 0" by auto
  then have lower2:" (real_of_int (sint w1)) \<le> -1"  using low
  by (simp add:  int_le_real_less) 
  from eq1 have rw1:"r2 \<le>  (real_of_int (sint w2))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by (simp add: upper)
  from eq1 have rw2:"r1 =  (real_of_int (sint w1))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto
  have hom:"  (- 2147483647::real) = -(2147483647)" by auto
  have mylem:"\<And>x y z::real. y < 0 \<Longrightarrow>   x \<le> y \<Longrightarrow> z \<le> -1 \<Longrightarrow> -y \<le> x * z"
    proof -
    fix x y z::real
    assume a1:"y < 0"
    assume a2:"x \<le> y"
    then have h1:"-x \<ge> -y" by auto
    assume a3:"z \<le> -1"
    then have a4:"z < 0" by auto
    from a4 have h2:"-z > 0" 
      using leD leI by auto
    from a3 have h5:"-z \<ge> 1" 
      by (simp add:  leD leI)
    have h4:"-x * -z \<ge> -y"
      using  a1 a2 a3 a4 h1 h2 h5  
      using dual_order.trans mult_left_mono  mult.right_neutral
      by (metis dual_order.order_iff_strict mult.commute mult_minus_right mult_zero_right neg_le_iff_le)
    have h3:"-x * -z = x * z" by auto
    show "- y \<le> x * z "
      using a1 a2 a3 a4 h1 h2 h3 h4 h5 
      by simp
    qed
  have prereqs:"- 2147483647 < (0::real)" " r2 \<le> - 2147483647" " (real_of_int (sint w1)) \<le> - 1"
    apply auto
    subgoal using rw1 theCase by (auto simp add: NEG_INF_def)
    using rw2 theCase lower2 by (auto simp add: word_sless_def word_sle_def NEG_INF_def lower2)
    
  show ?thesis
    using neq1 neq2 neq3 neq4 neq5 neq6 theCase apply simp
    unfolding repe.simps
    apply(rule disjI1)
    apply(rule exI[where x="r1 * r2"])
    using upper lower1 lower2 POS_INF_def NEG_INF_def rw1 rw2 apply (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
    using mylem[of "-2147483647" "r2" " (real_of_int (sint w1))"] prereqs
    by (simp add: mult.commute)
  qed
apply(cases "0 <s w1 \<and> w2 = NEG_INF") subgoal 
proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
  assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
  assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
  assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
  assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
  assume neq6:"\<not>(w1 = POS_INF \<and> 0 <s w2)"
  assume neq7:"\<not>(w1 = POS_INF \<and> 0 = w2)"
  assume neq8:"\<not>(w1 = NEG_INF \<and> w2 <s 0)"
  assume neq9:"\<not>(w1 = NEG_INF \<and> 0 <s w2)"
  assume neq10:"\<not>(w1 = NEG_INF \<and> 0 = w2)"
  assume neq11:"\<not>(w1 <s 0 \<and> w2 = POS_INF)"
  assume neq12:"\<not>(0 <s w1 \<and> w2 = POS_INF)"
  assume neq13:"\<not>(0 = w1 \<and> w2 = POS_INF)"
  assume neq14:"\<not>(w1 <s 0 \<and> w2 = NEG_INF)"
  assume theCase:"0 <s w1 \<and> w2 = NEG_INF"
from neq1 neq2 neq3 neq4 neq5 neq6 theCase
  have w2NotPinf:"w1 \<noteq> POS_INF" and w2NotNinf:"w1 \<noteq> NEG_INF" by auto
  from eq2 theCase 
  have upper:" (real_of_int (sint NEG_INF)) \<ge> r2 " 
  by (auto simp add: repe.simps POS_INF_def NEG_INF_def)
  have low:"sint w1 > 0" using theCase 
    apply (auto simp add: word_sless_def word_sle_def)
    by (simp add: dual_order.order_iff_strict)
  then have lower1:"  (real_of_int (sint w1)) > 0" by auto
  then have lower2:" (real_of_int (sint w1)) \<ge> 1"  using low
  by (simp add: int_le_real_less) 
  from eq2 have rw1:"r2 \<le>  (real_of_int (sint w2))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by (simp add: upper)
  from eq1 have rw2:"r1 =  (real_of_int (sint w1))" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto
  have mylem:"\<And>x y z::real. x \<le> -1 \<Longrightarrow> y \<ge> 1 \<Longrightarrow> z \<le> -1 \<Longrightarrow> x \<le> z \<Longrightarrow>  x * y \<le> z"
    proof -
    fix x y z::real
    assume a1:"x \<le> -1"
    assume a2:"y \<ge> 1"
    then have h1:"-1 \<ge> -y" by auto
    assume a3:"z \<le> -1"
    then have a4:"z < 0" by auto
    from a4 have h2:"-z > 0" 
      using  leD leI by auto
    from a3 have h5:"-z \<ge> 1" 
      by (simp add:  leD leI)
    assume a5:"x \<le> z"
    then have h6:"-x \<ge> -z" by auto
    have h3:"-x * -z = x * z" by auto
    show "x * y \<le> z"
      using a1 a2 a3 a4 h1 h2 h3 h6 h5 a5 dual_order.trans less_eq_real_def
      by (metis mult_less_cancel_left1 not_le)
    qed
  have prereqs:"r2 \<le> - 1" "1 \<le>  (real_of_int (sint w1))" " (- 2147483647) \<le> - (1::real )" "r2 \<le>  (- 2147483647)"
    subgoal using rw1 theCase by (auto simp add: NEG_INF_def word_sless_def word_sle_def) 
    subgoal using rw2 theCase apply (auto simp add: NEG_INF_def word_sless_def word_sle_def)
      using lower2 of_int_1_le_iff by blast
    subgoal  by (simp)
    subgoal using rw1 theCase by (auto simp add: NEG_INF_def word_sless_def word_sle_def)
    done
  show ?thesis
    using neq1 neq2 neq3 neq4 neq5 neq6 neq7 neq8 neq9 neq10 neq11 neq12 neq13 neq14   theCase apply simp
    unfolding repe.simps
    apply(rule disjI2)
    apply(rule disjI1)
    apply(rule exI[where x="r1 * r2"])
    using upper lower1 lower2 POS_INF_def NEG_INF_def rw1 rw2 apply (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
    using mylem[of  "r2" " (real_of_int (sint w1))" " (- 2147483647)"]
    using prereqs
    by (auto simp add: mult.commute)
  qed 
apply(cases "0 = w1 \<and> w2 = NEG_INF") subgoal 
proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
  assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
  assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
  assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
  assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
  assume neq6:"\<not>(w1 = POS_INF \<and> 0 <s w2)"
  assume neq7:"\<not>(w1 = POS_INF \<and> 0 = w2)"
  assume neq8:"\<not>(w1 = NEG_INF \<and> w2 <s 0)"
  assume neq9:"\<not>(w1 = NEG_INF \<and> 0 <s w2)"
  assume neq10:"\<not>(w1 = NEG_INF \<and> 0 = w2)"
  assume neq11:"\<not>(w1 <s 0 \<and> w2 = POS_INF)"
  assume neq12:"\<not>(0 <s w1 \<and> w2 = POS_INF)"
  assume neq13:"\<not>(0 = w1 \<and> w2 = POS_INF)"
  assume neq14:"\<not>(w1 <s 0 \<and> w2 = NEG_INF)"
  assume neq15:"\<not>(0 <s w1 \<and> w2 = NEG_INF)"
  assume theCase:"0 = w1 \<and> w2 = NEG_INF"
    from neq1 neq2 neq3 neq4 neq5 neq6 theCase
  have w2NotPinf:"w1 \<noteq> POS_INF" and w2NotNinf:"w1 \<noteq> NEG_INF" by auto
  from eq1 theCase  have rw2:"r1 = 0" using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neq1 neq2 neq3 neq4 theCase by auto
  show ?thesis
    using neq1 neq2 neq3 neq4 neq5 neq6 neq7 neq8 theCase apply simp
    unfolding repe.simps
    apply(rule disjI2)
    apply(rule disjI2)
    apply(rule exI[where x="0"])
    using POS_INF_def NEG_INF_def  rw2 by (auto simp add: NEG_INF_def POS_INF_def word_sless_def word_sle_def)
  qed
proof -
  assume neq1:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)"
  assume neq2:"\<not> (w1 = NEG_INF \<and> w2 = POS_INF)"
  assume neq3:"\<not> (w1 = POS_INF \<and> w2 = NEG_INF)"
  assume neq4:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)"
  assume neq5:"\<not> (w1 = POS_INF \<and> w2 <s 0)"
  assume neq6:"\<not> (w1 = POS_INF \<and> 0 <s w2)"
  assume neq7:"\<not> (w1 = POS_INF \<and> 0 = w2)"
  assume neq8:"\<not>(w1 = NEG_INF \<and> w2 <s 0)"
  assume neq9:"\<not> (w1 = NEG_INF \<and> 0 <s w2)"
  assume neq10:"\<not> (w1 = NEG_INF \<and> 0 = w2)"
  assume neq12:"\<not> (w1 <s 0 \<and> w2 = POS_INF)"
  assume neq13:"\<not> (0 <s w1 \<and> w2 = POS_INF)"
  assume neq14:"\<not> (0 = w1 \<and> w2 = POS_INF)"
  assume neq15:"\<not> (w1 <s 0 \<and> w2 = NEG_INF)"
  assume neq16:"\<not> (0 <s w1 \<and> w2 = NEG_INF)"
  assume neq17:"\<not> (0 = w1 \<and> w2 = NEG_INF)"
  let ?prod = "(((scast w1)::64 Word.word) * ((scast w2)::64 Word.word))"
  have case1:"?prod <=s ((scast NEG_INF)::64 Word.word) \<Longrightarrow> NEG_INF \<equiv>\<^sub>E (r1 * r2)"
    proof -
      have h1:"sint ((scast NEG_INF)::64 Word.word) = sint NEG_INF"
        apply(rule Word.sint_up_scast)
        unfolding Word.is_up by auto
      have h2:"sint NEG_INF = -(2^31)+1" unfolding NEG_INF_def by auto
      have h3:"sint ((scast w1)::64 Word.word) = sint w1"
        apply(rule Word.sint_up_scast)
        unfolding Word.is_up by auto
      have h4:"sint ((scast w2)::64 Word.word) = sint w2"
        apply(rule Word.sint_up_scast)
        unfolding Word.is_up by auto
      have sints32:"sints 32 = {i. - (2 ^ 31) \<le> i \<and> i < 2 ^ 31}"
        using sints_def[of 32] Bit_Representation.range_sbintrunc[of 31] by auto 
      have rangew1:"sint ((scast w1)::64 Word.word) \<in> {- (2 ^ 31).. (2^31)} " 
        using Word.word_sint.Rep[of "(w1)::32 Word.word"] sints32   len32 mem_Collect_eq h1 h3 h4 
        by auto
      have rangew2:"sint ((scast w2)::64 Word.word) \<in> {- (2 ^ 31).. (2^31)} " 
        using Word.word_sint.Rep[of "(w2)::32 Word.word"] sints32 len32 mem_Collect_eq h1 h3 h4 
        by auto
      have bigLeq:"(4611686018427387904::real) \<le> 9223372036854775807" by auto
      have set_cast:"\<And>x::int. (x \<in> {-(2^31)..2^31}) = ( (real_of_int x) \<in> {-(2^31)..2^31})"
        by auto
      have eq3:"sint(((scast w1)::64 Word.word) * ((scast w2)::64 Word.word)) = 
       sint ((scast w1)::64 Word.word) * sint ((scast w2)::64 Word.word)"
       apply(rule Word_Lemmas.signed_arith_sint(4))
       using rangew1 rangew2 h1 h2 h3 h4 
       using Word.word_size[of "((scast w1)::64 Word.word)"] 
       using Word.word_size[of "((scast w2)::64 Word.word)"]
       using times_upcast_upper[of "sint w1" "sint w2"]
       using times_upcast_lower[of "sint w1" "sint w2"] 
       unfolding NEG_INF_def by auto
      assume "?prod <=s ((scast NEG_INF)::64 Word.word)"
      then have sint_leq:"sint ?prod \<le> sint ((scast NEG_INF)::64 Word.word)"
        using word_sle_def by blast
      have neqs:"w1 \<noteq> POS_INF" " w1 \<noteq> NEG_INF" "w2 \<noteq> POS_INF" "w2 \<noteq> NEG_INF"
        using neq1 neq2 neq3  neq5 neq6 neq7 neq8 neq9 neq10  neq12 neq13 neq14 neq15 neq16 neq17 
         POS_INF_def NEG_INF_def word_sless_def signed.not_less_iff_gr_or_eq by force+
      from eq1 have rw1:"r1 =  (real_of_int (sint w1))" by(auto simp add: repe.simps neqs)
      from eq2 have rw2:"r2 =  (real_of_int (sint w2))" by(auto simp add: repe.simps neqs)
      show "NEG_INF \<equiv>\<^sub>E (r1 * r2)"
        apply (simp add: repe.simps)
        apply(rule disjI2)
        using h1 h2 h3 h4 rw1 rw2 sint_leq unfolding NEG_INF_def apply auto
        by (metis (no_types, hide_lams) eq3 of_int_le_iff of_int_minus of_int_mult of_int_numeral)
    qed
  have case2:"\<not>(?prod <=s ((scast NEG_INF)::64 Word.word)) \<Longrightarrow> ((scast POS_INF)::64 Word.word) <=s ?prod \<Longrightarrow> POS_INF \<equiv>\<^sub>E (r1 * r2)"
    proof -
      let ?thesis = "POS_INF \<equiv>\<^sub>E (r1 * r2)"
      have h1:"sint ((scast POS_INF)::64 Word.word) = sint POS_INF"
        apply(rule Word.sint_up_scast)
        unfolding Word.is_up by auto
      have h2:"sint POS_INF = (2^31)-1" unfolding POS_INF_def by auto
      have h3:"sint ((scast w1)::64 Word.word) = sint w1"
        apply(rule Word.sint_up_scast)
        unfolding Word.is_up by auto
      have h4:"sint ((scast w2)::64 Word.word) = sint w2"
        apply(rule Word.sint_up_scast)
        unfolding Word.is_up by auto
      have sints32:"sints 32 = {i. - (2 ^ 31) \<le> i \<and> i < 2 ^ 31}"
        using sints_def[of 32] Bit_Representation.range_sbintrunc[of 31] by auto 
      have rangew1:"sint ((scast w1)::64 Word.word) \<in> {- (2 ^ 31).. (2^31)} " 
        using Word.word_sint.Rep[of "(w1)::32 Word.word"] sints32   len32 mem_Collect_eq h1 h3 h4 
        by auto
      have rangew2:"sint ((scast w2)::64 Word.word) \<in> {- (2 ^ 31).. (2^31)} " 
        using Word.word_sint.Rep[of "(w2)::32 Word.word"] sints32 len32 mem_Collect_eq h1 h3 h4 
        by auto
      have bigLeq:"(4611686018427387904::real) \<le> 9223372036854775807" by auto
      have set_cast:"\<And>x::int. (x \<in> {-(2^31)..2^31}) = ( (real_of_int x) \<in> {-(2^31)..2^31})"
        by auto
      have eq3:"sint(((scast w1)::64 Word.word) * ((scast w2)::64 Word.word)) = 
       sint ((scast w1)::64 Word.word) * sint ((scast w2)::64 Word.word)"
       apply(rule Word_Lemmas.signed_arith_sint(4))
       using rangew1 rangew2 h1 h2 h3 h4 
       using Word.word_size[of "((scast w1)::64 Word.word)"] 
       using Word.word_size[of "((scast w2)::64 Word.word)"]
       using times_upcast_upper[of "sint w1" "sint w2"]
       using times_upcast_lower[of "sint w1" "sint w2"] 
       unfolding NEG_INF_def by auto
      assume "((scast POS_INF)::64 Word.word) <=s ?prod"
      then have sint_leq:"sint ((scast POS_INF)::64 Word.word) \<le> sint ?prod"
        using word_sle_def by blast
      have neqs:"w1 \<noteq> POS_INF" " w1 \<noteq> NEG_INF" "w2 \<noteq> POS_INF" "w2 \<noteq> NEG_INF"
        using neq1 neq2 neq3  neq5 neq6 neq7 neq8 neq9 neq10  neq12 neq13 neq14 neq15 neq16 neq17 
         POS_INF_def NEG_INF_def word_sless_def signed.not_less_iff_gr_or_eq by force+
      from eq1 have rw1:"r1 =  (real_of_int (sint w1))"  using repe.simps neq1 neq2 neq3 neq4 NEG_INF_def POS_INF_def neqs by auto
      from eq2 have rw2:"r2 =  (real_of_int (sint w2))" by(auto simp add: repe.simps neqs)
      show "POS_INF \<equiv>\<^sub>E r1 * r2"
        apply (simp add: repe.simps)
        apply(rule disjI1)
        using h1 h2 h3 h4 rw1 rw2 sint_leq unfolding POS_INF_def apply auto
        by (metis (no_types, hide_lams) eq3 of_int_le_iff of_int_mult of_int_numeral)
      qed
  have case3:"\<not>(?prod <=s ((scast NEG_INF)::64 Word.word)) \<Longrightarrow> \<not>((scast POS_INF)::64 Word.word) <=s ?prod \<Longrightarrow> ((scast ?prod)::word) \<equiv>\<^sub>E (r1 * r2)"
    proof -
      have h1:"sint ((scast POS_INF)::64 Word.word) = sint POS_INF"
        apply(rule Word.sint_up_scast)
        unfolding Word.is_up by auto
      have h2:"sint POS_INF = (2^31)-1" unfolding POS_INF_def by auto
      have h3:"sint ((scast w1)::64 Word.word) = sint w1"
        apply(rule Word.sint_up_scast)
        unfolding Word.is_up by auto
      have h4:"sint ((scast w2)::64 Word.word) = sint w2"
        apply(rule Word.sint_up_scast)
        unfolding Word.is_up by auto
      have h5:"sint ((scast NEG_INF)::64 Word.word) = sint NEG_INF"
        apply(rule Word.sint_up_scast)
        unfolding Word.is_up by auto
      have h6:"sint NEG_INF = -(2^31)+1" unfolding NEG_INF_def by auto
      have sints32:"sints 32 = {i. - (2 ^ 31) \<le> i \<and> i < 2 ^ 31}"
        using sints_def[of 32] Bit_Representation.range_sbintrunc[of 31] by auto 
      have rangew1:"sint ((scast w1)::64 Word.word) \<in> {- (2 ^ 31).. (2^31)} " 
        using Word.word_sint.Rep[of "(w1)::32 Word.word"] sints32   len32 mem_Collect_eq h1 h3 h4 
        by auto
      have rangew2:"sint ((scast w2)::64 Word.word) \<in> {- (2 ^ 31).. (2^31)} " 
        using Word.word_sint.Rep[of "(w2)::32 Word.word"] sints32 len32 mem_Collect_eq h1 h3 h4 
        by auto
      have bigLeq:"(4611686018427387904::real) \<le> 9223372036854775807" by auto
      have set_cast:"\<And>x::int. (x \<in> {-(2^31)..2^31}) = ( (real_of_int x) \<in> {-(2^31)..2^31})"
        by auto
      have eq3:"sint(((scast w1)::64 Word.word) * ((scast w2)::64 Word.word)) = 
       sint ((scast w1)::64 Word.word) * sint ((scast w2)::64 Word.word)"
       apply(rule Word_Lemmas.signed_arith_sint(4))
       using rangew1 rangew2 h1 h2 h3 h4 
       using Word.word_size[of "((scast w1)::64 Word.word)"] 
       using Word.word_size[of "((scast w2)::64 Word.word)"]
       using times_upcast_upper[of "sint w1" "sint w2"]
       using times_upcast_lower[of "sint w1" "sint w2"] 
       unfolding NEG_INF_def by auto
      assume a1:"\<not>(?prod <=s ((scast NEG_INF)::64 Word.word))"
      then have sintGe:"sint (?prod) > sint (((scast NEG_INF)::64 Word.word))"
        using word_sle_def dual_order.order_iff_strict signed.linear 
        by fastforce
      assume a2:"\<not>((scast POS_INF)::64 Word.word) <=s ?prod"
      then have sintLe:"sint (((scast POS_INF)::64 Word.word)) > sint (?prod)"
        using word_sle_def dual_order.order_iff_strict signed.linear 
        by fastforce
      have neqs:"w1 \<noteq> POS_INF" " w1 \<noteq> NEG_INF" "w2 \<noteq> POS_INF" "w2 \<noteq> NEG_INF"
        using neq1 neq2 neq3  neq5 neq6 neq7 neq8 neq9 neq10  neq12 neq13 neq14 neq15 neq16 neq17 
        POS_INF_def NEG_INF_def word_sless_def signed.not_less_iff_gr_or_eq by force+
      from eq1 have rw1:"r1 =  (real_of_int (sint w1))" by(auto simp add: repe.simps neqs)
      from eq2 have rw2:"r2 =  (real_of_int (sint w2))" by(auto simp add: repe.simps neqs)
      from rw1 rw2 have "r1 * r2 =  (real_of_int ((sint w1) * (sint w2)))"
        by simp
      have rightSize:"sint (((scast w1)::64 Word.word) *  ((scast w2)::64 Word.word)) \<in> sints (len_of TYPE(32))"
        using sintLe sintGe sints32 by (simp add: NEG_INF_def POS_INF_def) 
      have downcast:"sint ((scast (((scast w1)::64 Word.word) * ((scast w2)::64 Word.word)))::word) = sint (((scast w1)::64 Word.word) * ((scast w2)::64 Word.word))"
        using scast_down_range[OF rightSize]
        by auto
      then have res_eq:"r1 * r2 =  (real_of_int (sint ((scast (((scast w1)::64 Word.word) * ((scast w2)::64 Word.word)))::word)))"
        using rw1 rw2 eq3 h1 h2 h3 h4 h5 downcast POS_INF_def NEG_INF_def
        using \<open>r1 * r2 =  (real_of_int (sint w1 * sint w2))\<close> 
        by (auto simp add: POS_INF_def NEG_INF_def)
      have res_up:"sint (scast (((scast w1)::64 Word.word) * ((scast w2)::64 Word.word))::word) < sint POS_INF"
        using rw1 rw2 eq3 h1 h2 h3 h4 h5 downcast
        using POS_INF_def NEG_INF_def 
        using \<open>r1 * r2 = (real_of_int (sint w1 * sint w2))\<close> 
            \<open>sint (scast w1 * scast w2) < sint (scast POS_INF)\<close> 
            of_int_eq_iff res_eq 
        by presburger
      have res_lo:"sint NEG_INF < sint (scast (((scast w1)::64 Word.word) * ((scast w2)::64 Word.word))::word)"
              using rw1 rw2 eq3 h1 h2 h3 h4 h5 downcast
        using POS_INF_def NEG_INF_def 
        using \<open>r1 * r2 =  (real_of_int (sint w1 * sint w2))\<close> 
            \<open>sint (scast NEG_INF) < sint (scast w1 * scast w2)\<close> 
             of_int_eq_iff res_eq 
        by presburger
      show "scast ?prod \<equiv>\<^sub>E (r1 * r2)"
        using res_eq res_up res_lo 
        by (auto simp add: repe.simps)
    qed

  show ?thesis
  apply(cases "?prod <=s ((scast NEG_INF)::64 Word.word)")
  subgoal using case1 neq1 neq2 neq3 neq4 neq5 neq6 neq7 neq8 neq9 neq10 neq12 neq13 neq14 neq16 neq15 neq17 unfolding wtimes.simps by presburger
  apply(cases "(((scast POS_INF)::64 Word.word) <=s ?prod)")
  subgoal using case2 neq1 neq2 neq3 neq4 neq5 neq6 neq7 neq8 neq9 neq10 neq12 neq13 neq14 neq16 neq15 neq17 unfolding wtimes.simps by presburger
  using case3 neq1 neq2 neq3 neq4 neq5 neq6 neq7 neq8 neq9 neq10 neq12 neq13 neq14 neq16 neq15 neq17 unfolding wtimes.simps by presburger
qed

fun tu :: "word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word"
where "tu w1l w1u w2l w2u = 
 wmax (wmax (wtimes w1l w2l) (wtimes w1u w2l))
      (wmax (wtimes w1l w2u) (wtimes w1u w2u))"

lemma max_repU1:
  assumes "w1 \<equiv>\<^sub>U x"
  assumes "w2 \<equiv>\<^sub>U y"
  shows "wmax w1 w2 \<equiv>\<^sub>U x "
  using wmax_lemma assms repU_def
  by (meson le_max_iff_disj)
  
lemma max_repU2:
  assumes "w1 \<equiv>\<^sub>U y"
  assumes "w2 \<equiv>\<^sub>U x"
  shows "wmax w1 w2 \<equiv>\<^sub>U x"
  using wmax_lemma assms repU_def
  by (meson le_max_iff_disj)
  
lemma ivl_zero_case:
  fixes l1 u1 l2 u2 :: real
  assumes ivl1:"l1 \<le> u1"
  assumes ivl2:"l2 \<le> u2"
  shows 
"(l1 \<le> 0 \<and> 0 \<le> u1 \<and> l2 \<le> 0 \<and> 0 \<le> u2)
\<or>(l1 \<le> 0 \<and> 0 \<le> u1 \<and> 0 \<le> l2)
\<or>(l1 \<le> 0 \<and> 0 \<le> u1 \<and> u2 \<le> 0)
\<or>(0 \<le> l1 \<and> l2 \<le> 0 \<and> 0 \<le> u2)
\<or>(u1 \<le> 0 \<and> l2 \<le> 0 \<and> 0 \<le> u2)
\<or>(u1 \<le> 0 \<and> u2 \<le> 0)
\<or>(u1 \<le> 0 \<and> 0 \<le> l2)
\<or>(0 \<le> l1 \<and> u2 \<le> 0)
\<or>(0 \<le> l1 \<and> 0 \<le> l2)"
using ivl1 ivl2 
by (metis le_cases)

lemma case_ivl_zero:
  fixes l1 u1 l2 u2 :: real
  assumes ivl1:"l1 \<le> u1"
  assumes ivl2:"l2 \<le> u2"
  shows 
  "((l1 \<le> 0 \<and> 0 \<le> u1 \<and> l2 \<le> 0 \<and> 0 \<le> u2) \<Longrightarrow> P) \<Longrightarrow>
((l1 \<le> 0 \<and> 0 \<le> u1 \<and> 0 \<le> l2) \<Longrightarrow> P) \<Longrightarrow>
((l1 \<le> 0 \<and> 0 \<le> u1 \<and> u2 \<le> 0) \<Longrightarrow> P) \<Longrightarrow>
((0 \<le> l1 \<and> l2 \<le> 0 \<and> 0 \<le> u2) \<Longrightarrow> P) \<Longrightarrow>
((u1 \<le> 0 \<and> l2 \<le> 0 \<and> 0 \<le> u2) \<Longrightarrow> P) \<Longrightarrow>
((u1 \<le> 0 \<and> u2 \<le> 0) \<Longrightarrow> P) \<Longrightarrow>
((u1 \<le> 0 \<and> 0 \<le> l2) \<Longrightarrow> P) \<Longrightarrow>
((0 \<le> l1 \<and> u2 \<le> 0) \<Longrightarrow> P) \<Longrightarrow>
((0 \<le> l1 \<and> 0 \<le> l2) \<Longrightarrow> P) \<Longrightarrow> P"
using ivl1 ivl2 
by (metis le_cases)

lemmas silly_lemma = mult_le_cancel_left
lemmas real_mult_le_mult_iff = silly_lemma

lemma tu_lemma:
  assumes u1:"u\<^sub>1 \<equiv>\<^sub>U (r\<^sub>1::real)"
  assumes u2:"u\<^sub>2 \<equiv>\<^sub>U (r\<^sub>2::real)"
  assumes l1:"l\<^sub>1 \<equiv>\<^sub>L (r\<^sub>1::real)"
  assumes l2:"l\<^sub>2 \<equiv>\<^sub>L (r\<^sub>2::real)"
  shows "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U (r\<^sub>1 * r\<^sub>2)"
proof -
  obtain rl1 rl2 ru1 ru2 :: real 
  where gru1:"ru1 \<ge> r\<^sub>1" and gru2:"ru2 \<ge> r\<^sub>2" and grl1:"rl1 \<le> r\<^sub>1" and grl2:"rl2 \<le> r\<^sub>2" 
  and eru1:"u\<^sub>1 \<equiv>\<^sub>E ru1" and eru2:"u\<^sub>2 \<equiv>\<^sub>E ru2" and erl1:"l\<^sub>1 \<equiv>\<^sub>E rl1" and erl2:"l\<^sub>2 \<equiv>\<^sub>E rl2"
  using u1 u2 l1 l2 unfolding repU_def repL_def by auto
  have timesuu:"wtimes u\<^sub>1 u\<^sub>2 \<equiv>\<^sub>E ru1 * ru2"
    using wtimes_exact[OF eru1 eru2] by auto
  have timesul:"wtimes u\<^sub>1 l\<^sub>2 \<equiv>\<^sub>E ru1 * rl2"
    using wtimes_exact[OF eru1 erl2] by auto
  have timeslu:"wtimes l\<^sub>1 u\<^sub>2 \<equiv>\<^sub>E rl1 * ru2"
    using wtimes_exact[OF erl1 eru2] by auto
  have timesll:"wtimes l\<^sub>1 l\<^sub>2 \<equiv>\<^sub>E rl1 * rl2"
    using wtimes_exact[OF erl1 erl2] by auto
  have maxt12:"wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2) \<equiv>\<^sub>E max (rl1 * rl2) (ru1 * rl2)"
    by (rule  wmax_lemma[OF timesll timesul])
  have maxt34:"wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2) \<equiv>\<^sub>E max (rl1 * ru2) (ru1 * ru2)"
    by (rule  wmax_lemma[OF timeslu timesuu])
  have bigMax:"wmax (wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2))
    \<equiv>\<^sub>E max (max (rl1 * rl2) (ru1 * rl2)) (max (rl1 * ru2) (ru1 * ru2))"
    by (rule wmax_lemma[OF maxt12 maxt34])
  obtain maxt12val :: real where maxU12:"wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2) \<equiv>\<^sub>U max (rl1 * rl2) (ru1 * rl2)"
  using maxt12 unfolding repU_def by blast
  obtain maxt34val :: real where maxU34:"wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2) \<equiv>\<^sub>U max (rl1 * ru2) (ru1 * ru2)"
  using maxt34 unfolding repU_def by blast
  obtain bigMaxU:"wmax (wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2))
    \<equiv>\<^sub>U max (max (rl1 * rl2) (ru1 * rl2)) (max (rl1 * ru2) (ru1 * ru2))"
  using bigMax unfolding repU_def by blast
        
  have ivl1:"rl1 \<le> ru1" using grl1 gru1 by auto
  have ivl2:"rl2 \<le> ru2" using grl2 gru2 by auto
  let ?thesis = "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U r\<^sub>1 * r\<^sub>2"
  show ?thesis
  apply(rule case_ivl_zero[OF ivl1 ivl2])
  proof -
    assume "rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    then have geq1:"ru1 \<ge> 0" and geq2:"ru2 \<ge> 0" by auto
    have case1:"r\<^sub>1 \<ge> 0 \<Longrightarrow> r\<^sub>2 \<ge> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r1:"r\<^sub>1 \<ge> 0"
        assume r2:"r\<^sub>2 \<ge> 0"
        have g1:"ru1 * ru2 \<ge> ru1 * r\<^sub>2" 
          using r1 geq1 geq2 grl2 gru2
          by (simp add: mult_left_mono )
        have g2:"ru1 * r\<^sub>2 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 geq1 geq2 grl1 grl2 gru1 gru2
          by (simp add: mult_right_mono)
        from g1 and g2
        have up:"ru1 * ru2 \<ge> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up
        eru1 eru2 erl1 erl2
        max_repU2[OF maxU12]
        max_repU2[OF maxU34]
        max_repU2[OF bigMaxU]
        repU_def timesuu tu.simps
         by (metis wmax.elims)
      qed
    have case2:"r\<^sub>1 \<le> 0 \<Longrightarrow> r\<^sub>2 \<ge> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r1:"r\<^sub>1 \<le> 0"
        assume r2:"r\<^sub>2 \<ge> 0"
        have g1:"ru1 * ru2 \<ge> 0" 
          using r1 geq1 geq2 grl2 gru2 by (simp)
        have g2:"0 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 by (simp add: mult_le_0_iff)
        from g1 and g2
        have up:"ru1 * ru2 \<ge> r\<^sub>1 * r\<^sub>2" by auto
        show ?thesis
        using up
          maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] repU_def tu.simps timesuu
          by (metis max.coboundedI1 max.commute maxt34)
      qed
    have case3:"r\<^sub>1 \<ge> 0 \<Longrightarrow> r\<^sub>2 \<le> 0 \<Longrightarrow> ?thesis"
      proof -
        assume r1:"r\<^sub>1 \<ge> 0"
        assume r2:"r\<^sub>2 \<le> 0"
        have g1:"ru1 * ru2 \<ge> 0" 
          using r1 geq1 geq2 grl2 gru2
          by (simp)
        have g2:"0 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 
          by (simp add: mult_le_0_iff)
        from g1 and g2
        have up:"ru1 * ru2 \<ge> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up
        maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34
        by (metis  repU_def  tu.simps)
      qed
    have case4:"r\<^sub>1 \<le> 0 \<Longrightarrow> r\<^sub>2 \<le> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r1:"r\<^sub>1 \<le> 0"
        assume r2:"r\<^sub>2 \<le> 0"
        have g1:"rl1 * rl2 \<ge> rl1 * r\<^sub>2" 
          using r1 r2 geq1 geq2 grl1 grl2 gru1 gru2
          using  \<open>rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2\<close> less_eq_real_def
          by (metis mult_left_mono_neg)
        have g2:"rl1 * r\<^sub>2 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 geq1 geq2 grl1 grl2 gru1 gru2 \<open>rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2\<close>  mult.commute 
          by (metis mult_left_mono_neg)
        from g1 and g2
        have up:"rl1 * rl2 \<ge> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up  maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU]  max.commute maxt34
        by (metis max_repU1 repU_def timesll tu.simps) 
      qed
    show "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U r\<^sub>1 * r\<^sub>2"
      using case1 case2 case3 case4 le_cases by blast
  next
    assume bounds:"rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> 0 \<le> rl2"
    have r2:"r\<^sub>2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    have case1:"r\<^sub>1 \<ge> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r1:"r\<^sub>1 \<ge> 0"
        have g1:"ru1 * ru2 \<ge> ru1 * r\<^sub>2" 
          using r1 r2 bounds grl1 grl2 gru1 gru2
          using mult_left_mono by blast
        have g2:"ru1 * r\<^sub>2 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2
          using mult_right_mono by blast
        from g1 and g2
        have up:"ru1 * ru2 \<ge> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34
        by (metis repU_def tu.simps) 
      qed
    have case2:"r\<^sub>1 \<le> 0 \<Longrightarrow> ?thesis"
      proof -
        assume r1:"r\<^sub>1 \<le> 0"
        have g1:"ru1 * ru2 \<ge> 0" 
          using r1 r2 bounds grl1 grl2 gru1 gru2
          using mult_left_mono 
          by (simp add: mult_less_0_iff less_le_trans not_less)
        have g2:"0 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2
          using mult_right_mono 
          by (simp add: mult_le_0_iff)
        from g1 and g2
        have up:"ru1 * ru2 \<ge> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34
        by (metis repU_def tu.simps) 
      qed
    show "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U r\<^sub>1 * r\<^sub>2"
      using case1 case2 le_cases by blast
  next
    assume bounds:"rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> ru2 \<le> 0"
    have r2:"r\<^sub>2 \<le> 0" using bounds dual_order.trans gru2 by blast
    have case1:"r\<^sub>1 \<ge> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r1:"r\<^sub>1 \<ge> 0"
        have g1:"rl1 * rl2 \<ge> 0" 
          using r1 r2 bounds grl1 grl2 gru1 gru2 mult_less_0_iff less_le_trans not_less
          by metis
        have g2:"0 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2
          using mult_right_mono 
          by (simp add: mult_le_0_iff)
        from g1 and g2
        have up:"rl1 * rl2 \<ge> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis 
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.commute maxt34
        by (metis  max_repU2 max_repU1 repU_def timesll tu.simps)
      qed
    have case2:"r\<^sub>1 \<le> 0 \<Longrightarrow> ?thesis"
    proof -
        assume r1:"r\<^sub>1 \<le> 0"
        have g1:"rl1 * rl2 \<ge> rl1 * r\<^sub>2" 
          using r1 r2 bounds  grl1 grl2 gru1 gru2
          by (metis mult_left_mono_neg)
        have g2:"rl1 * r\<^sub>2 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2 mult.commute
          by (metis mult_left_mono_neg)
        from g1 and g2
        have up:"rl1 * rl2 \<ge> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.commute maxt34 
        by (metis max_repU1 repU_def timesll tu.simps) 
      qed
    show "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U r\<^sub>1 * r\<^sub>2"
      using case1 case2 le_cases by blast
  next
    assume bounds:"0 \<le> rl1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    have r1:"r\<^sub>1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    have case1:"r\<^sub>2 \<ge> 0 \<Longrightarrow> ?thesis"
      proof -
        assume r2:"r\<^sub>2 \<ge> 0"
        have g1:"ru1 * ru2 \<ge> ru1 * r\<^sub>2" 
          using r1 r2 bounds grl1 grl2 gru1 gru2
          using mult_left_mono 
          using leD leI less_le_trans by metis
        have g2:"ru1 * r\<^sub>2 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2
          using mult_right_mono by blast
        from g1 and g2
        have up:"ru1 * ru2 \<ge> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34
        by (metis repU_def tu.simps) 
      qed
    have case2:"r\<^sub>2 \<le> 0 \<Longrightarrow> ?thesis"
      proof -
        assume r2:"r\<^sub>2 \<le> 0"
        have g1:"ru1 * ru2 \<ge> 0" 
          using r1 bounds grl2 gru2 gru1 leD leI less_le_trans by auto
        have g2:"0 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 
          by (simp add: mult_le_0_iff)
        from g1 and g2
        have up:"ru1 * ru2 \<ge> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34
        by (metis repU_def  tu.simps)
      qed
    show "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U r\<^sub>1 * r\<^sub>2"
      using case1 case2 le_cases by blast      
  next
    assume bounds:"ru1 \<le> 0 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    have r1:"r\<^sub>1 \<le> 0"  using bounds dual_order.trans gru1 by blast
    have case1:"r\<^sub>2 \<ge> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r2:"r\<^sub>2 \<ge> 0"
        have g1:"ru1 * rl2 \<ge> 0" 
          using r1 r2 bounds grl1 grl2 gru1 gru2 mult_less_0_iff not_less
          by metis
        have g2:"0 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2
          by (simp add: mult_le_0_iff)
        from g1 and g2
        have up:"ru1 * rl2 \<ge> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.commute maxt34
        by (metis max_repU1 repU_def timesul tu.simps) 
      qed
    have case2:"r\<^sub>2 \<le> 0 \<Longrightarrow> ?thesis"
    proof -
      assume r2:"r\<^sub>2 \<le> 0"
        have lower:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
        have g1:"rl1 * rl2 \<ge> rl1 * r\<^sub>2" 
          using r1 r2 bounds  grl1 grl2 gru1 gru2 less_eq(1) less_le_trans not_less silly_lemma
          by metis
        have g2:"rl1 * r\<^sub>2 \<ge> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2 mult.commute not_le lower silly_lemma
          by metis
        from g1 and g2
        have up:"rl1 * rl2 \<ge> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.commute maxt34
        by (metis max_repU1 repU_def timesll tu.simps)
      qed
    show "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U r\<^sub>1 * r\<^sub>2"
      using case1 case2 le_cases by blast
  next
    assume bounds:"ru1 \<le> 0 \<and> ru2 \<le> 0"
    have r1:"r\<^sub>1 \<le> 0" using bounds dual_order.trans gru1 by blast
    have r2:"r\<^sub>2 \<le> 0" using bounds dual_order.trans gru2 by blast
    have lower1:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
    have lower2:"rl2 \<le> 0" using bounds dual_order.trans grl2 r2 by blast
    have g1:"rl1 * rl2 \<ge> rl1 * r\<^sub>2" 
      using r1 r2 bounds  grl1 grl2 gru1 gru2 less_eq(1)  silly_lemma  less_le_trans not_less
      by metis
    have g2:"rl1 * r\<^sub>2 \<ge> r\<^sub>1 * r\<^sub>2"
      using r1 r2 bounds grl1 grl2 gru1 gru2 mult.commute not_le lower1 lower2 silly_lemma
      by metis
    from g1 and g2
    have up:"rl1 * rl2 \<ge> r\<^sub>1 * r\<^sub>2"
      by auto
    show ?thesis
      using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.commute maxt34 
      by (metis max_repU1 repU_def timesll tu.simps)
  next
    assume bounds:"ru1 \<le> 0 \<and> 0 \<le> rl2"
    have r1:"r\<^sub>1 \<le> 0" using bounds dual_order.trans gru1 by blast
    have r2:"r\<^sub>2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    have lower1:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
    have lower2:"rl2 \<ge> 0" using bounds by auto
    have upper1:"ru1 \<le> 0" using bounds by auto 
    have upper2:"ru2 \<ge> 0" using bounds dual_order.trans gru2 r2 by blast
    have g1:"ru1 * rl2 \<ge> ru1 * r\<^sub>2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2 not_less upper1 lower2 silly_lemma
      by metis
    have g2:"ru1 * r\<^sub>2 \<ge> r\<^sub>1 * r\<^sub>2"
      using r1 upper1 r2 mult_right_mono gru1 by metis
    from g1 and g2
    have up:"ru1 * rl2 \<ge> r\<^sub>1 * r\<^sub>2"
      by auto
    show ?thesis
    using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] maxt34 
    by (metis   max_repU1 repU_def timesul tu.simps)
  next 
    assume bounds:"0 \<le> rl1 \<and> ru2 \<le> 0"
    have r1:"r\<^sub>1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    have r2:"r\<^sub>2 \<le> 0" using bounds dual_order.trans gru2 by blast
    have lower1:"rl1 \<ge> 0" using bounds by auto
    have lower2:"rl2 \<le> 0" using dual_order.trans grl2 r2 by blast
    have upper1:"ru1 \<ge> 0" using dual_order.trans gru1 u1 r1 by blast  
    have upper2:"ru2 \<le> 0" using bounds by auto
    have g1:"rl1 * ru2 \<ge> rl1 * r\<^sub>2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2  not_less upper2 lower1 silly_lemma
      by metis
    have g2:"rl1 * r\<^sub>2 \<ge> r\<^sub>1 * r\<^sub>2"
      using r1 lower1 r2 not_less gru2 gru1 grl1 grl2
      by (metis silly_lemma mult.commute)
    from g1 and g2
    have up:"rl1 * ru2 \<ge> r\<^sub>1 * r\<^sub>2"
      by auto
    show "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U r\<^sub>1 * r\<^sub>2"
      using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34 
      by (metis repU_def tu.simps)
  next
    assume bounds:"0 \<le> rl1 \<and> 0 \<le> rl2"
    have r1:"r\<^sub>1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    have r2:"r\<^sub>2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    have lower1:"rl1 \<ge> 0" using bounds by auto
    have lower2:"rl2 \<ge> 0" using bounds by auto
    have upper1:"ru1 \<ge> 0" using dual_order.trans gru1 u1 r1 by blast  
    have upper2:"ru2 \<ge> 0" using dual_order.trans gru2 u2 r2 bounds by blast
    have g1:"ru1 * ru2 \<ge> ru1 * r\<^sub>2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2 mult_left_mono leD leI less_le_trans by metis
    have g2:"ru1 * r\<^sub>2 \<ge> r\<^sub>1 * r\<^sub>2"
      using r1 r2 bounds grl1 grl2 gru1 gru2 mult_right_mono by metis
    from g1 and g2
    have up:"ru1 * ru2 \<ge> r\<^sub>1 * r\<^sub>2"
      by auto
    show ?thesis
    using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34
      by (metis repU_def tu.simps)
  qed
  qed
  
fun wmin :: "word \<Rightarrow> word \<Rightarrow> word"
where "wmin w\<^sub>1 w\<^sub>2 = 
  (if w\<^sub>1 <s w\<^sub>2 then w\<^sub>1 else w\<^sub>2)"

lemma wmin_lemma:
  assumes eq1:"w\<^sub>1 \<equiv>\<^sub>E (r\<^sub>1::real)"
  assumes eq2:"w\<^sub>2 \<equiv>\<^sub>E (r\<^sub>2::real)"
  shows "wmin w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E (min r\<^sub>1 r\<^sub>2)"
  apply(rule repe.cases[OF eq1])
  subgoal for r
    apply(rule repe.cases[OF eq2])
    subgoal for ra 
      proof -
        assume p1:"w\<^sub>1 = POS_INF"
        assume p2:"w\<^sub>2 = POS_INF"
        assume eq1:"r\<^sub>1 = r"
        assume eq2:"r\<^sub>2 = ra"
        assume bound1:"(real_of_int (sint POS_INF)) \<le> r"
        assume bound2:"(real_of_int (sint POS_INF)) \<le> ra"
        have eqInf:"wmin w\<^sub>1 w\<^sub>2 = POS_INF"
          using p1 p2 unfolding POS_INF_def wmin.simps by auto
        have pos_eq:"POS_INF \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2"
          apply(rule repPOS_INF)
          using bound1 bound2 unfolding POS_INF_def eq1 eq2 by auto
        show ?thesis
          using pos_eq eqInf by auto
      qed
    subgoal for ra
      proof -
        assume p1:"w\<^sub>1 = POS_INF"
        assume n2:"w\<^sub>2 = NEG_INF"
        assume bound1:" (real_of_int (sint POS_INF)) \<le> r"
        assume bound2:"ra \<le>  (real_of_int (sint NEG_INF))"
        assume eq1:"r\<^sub>1 = r"
        assume eq2:"r\<^sub>2 = ra"
        have eqNeg:"wmin w\<^sub>1 w\<^sub>2 = NEG_INF"
          unfolding NEG_INF_def POS_INF_def eq1 eq2 wmin.simps p1 n2 word_sless_def word_sle_def
          by(auto) 
        have neg_eq:"NEG_INF \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2"
          apply(rule repNEG_INF)
          using bound1 bound2 unfolding POS_INF_def NEG_INF_def using eq1 eq2 by auto
        show "?thesis"
          using eqNeg neg_eq by auto
        qed
    subgoal for ra 
      proof -
        assume p1:"w\<^sub>1 = POS_INF"
        assume i2:"w\<^sub>2 = ra"
        assume eq1:"r\<^sub>1 = r"
        assume eq2:"r\<^sub>2 =  (real_of_int (sint ra))"
        assume bound1:" (real_of_int (sint POS_INF)) \<le> r"
        assume bound2a:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint ra))"
        assume bound2b:" (real_of_int (sint ra)) <  (real_of_int (sint POS_INF))"
        have eqNeg:"min r\<^sub>1 r\<^sub>2 = sint ra"
          using p1 i2 unfolding NEG_INF_def POS_INF_def wmin.simps
          by (metis  bound1 bound2b dual_order.trans eq1 eq2 min_def not_less) 
        have neg_eq:"wmin w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E  (real_of_int (sint (wmin w\<^sub>1 w\<^sub>2)))"
          apply (rule repINT)
          using bound1 bound2a bound2b unfolding POS_INF_def NEG_INF_def eq1 eq2 apply auto
          using bound2b p1 by (simp add: i2 word_sless_alt)+
        show "?thesis"
          using eqNeg neg_eq 
          by (metis bound2b i2 less_eq_real_def not_less of_int_less_iff p1 wmin.simps word_sless_alt)
        qed
        done
  subgoal for r 
    apply(rule repe.cases[OF eq2])
    subgoal for ra
      proof -
        assume eq1:"r\<^sub>1 = r"
        assume eq2:"r\<^sub>2 = ra" 
        assume n1:"w\<^sub>1 = NEG_INF"
        assume p2:"w\<^sub>2 = POS_INF"
        assume bound1:"r \<le>  (real_of_int (sint NEG_INF))"
        assume bound2:" (real_of_int (sint POS_INF)) \<le> ra"
        have eqNeg:"wmin w\<^sub>1 w\<^sub>2 = NEG_INF"
          unfolding NEG_INF_def POS_INF_def eq1 eq2 wmin.simps n1 p2 word_sless_def word_sle_def
          by(auto)
        have neg_eq:"NEG_INF \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2"
          apply(rule repNEG_INF)
          using bound1 bound2 unfolding POS_INF_def NEG_INF_def eq1 eq2 by auto
        show "wmin w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2"
          using eqNeg neg_eq by auto
        qed
    subgoal for ra
    proof -
      assume n1:"w\<^sub>1 = NEG_INF"
      assume n2:"w\<^sub>2 = NEG_INF"
      assume eq1:"r\<^sub>1 = r"
      assume eq2:"r\<^sub>2 = ra"
      assume bound1:"r \<le>  (real_of_int (sint NEG_INF))"
      assume bound2:"ra \<le>  (real_of_int (sint NEG_INF))"
      have eqNeg:"NEG_INF \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2"
        apply(rule repNEG_INF)
        using eq1 eq2 bound1 bound2 unfolding NEG_INF_def
        by (auto)
      have neg_eq:"wmin w\<^sub>1 w\<^sub>2 = NEG_INF"
        using n1 n2 unfolding NEG_INF_def wmin.simps by auto 
      show "wmin w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2"
        using eqNeg neg_eq by auto
    qed
    subgoal for w
      proof -
        assume n1:"w\<^sub>1 = NEG_INF"
        assume i2:"w\<^sub>2 = w"
        assume eq1:"r\<^sub>1 = r"
        assume eq2:"r\<^sub>2 =  (real_of_int (sint w))"
        assume bound2a:"(real_of_int (sint w)) <  (real_of_int (sint POS_INF))"
        assume bound2b:"(real_of_int (sint NEG_INF)) <  (real_of_int (sint w))"
        assume bound1:"r \<le>  (real_of_int (sint NEG_INF))"
        have eqNeg:"wmin w\<^sub>1 w\<^sub>2 = NEG_INF"
          using n1 i2 unfolding NEG_INF_def wmin.simps
          using assms(2) bound2a eq2 n1 repeInt_simps word_sless_alt 
          by auto
        have neg_eq:"NEG_INF \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2"
          apply(rule repNEG_INF)
          using NEG_INF_def bound1 bound2a bound2b
          using eq1 min_le_iff_disj by blast
        show "wmin w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2"
          using eqNeg neg_eq by auto
        qed
      done
  subgoal for r 
    apply(rule repe.cases[OF eq2])
    subgoal for ra
      proof -
        assume i1:"w\<^sub>1 = r"
        assume p2:"w\<^sub>2 = POS_INF"
        assume eq1:"r\<^sub>1 =  (real_of_int (sint r))"
        assume eq2:"r\<^sub>2 = ra"
        assume bound1a:" (real_of_int (sint r)) <  (real_of_int (sint POS_INF))"
        assume bound1b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint r))"
        assume bound2:" (real_of_int (sint POS_INF)) \<le> ra"
        have res1:"wmin w\<^sub>1 w\<^sub>2 = r"
          using i1 p2 eq1 eq2 unfolding POS_INF_def apply auto
          using assms(1) bound1b p2 repeInt_simps word_sless_alt by auto
        have res2:"min r\<^sub>1 r\<^sub>2 =  (real_of_int (sint r))"
          using eq1 eq2 bound1a bound1b bound2 
          by (auto simp add: less_imp_le less_le_trans min_def)
        have res3:"wmin w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E  (real_of_int (sint (wmin w\<^sub>1 w\<^sub>2)))"
          apply(rule repINT)
          using POS_INF_def NEG_INF_def i1 p2 POS_INF_def bound1a res1 bound1a bound1b bound2 by auto
        show "wmin w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2" 
          using res1 res2 res3 by auto
        qed
    subgoal for ra
      proof -
        assume i1:"w\<^sub>1 = r"
        assume n2:"w\<^sub>2 = NEG_INF"
        assume eq1:"r\<^sub>1 =  (real_of_int (sint r))"
        assume eq2:"r\<^sub>2 = ra" 
        assume bound1a:" (real_of_int (sint r)) <  (real_of_int (sint POS_INF))"
        assume bound1b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint r))"
        assume bound2:"ra \<le>  (real_of_int (sint NEG_INF))"
        have res1:"wmin w\<^sub>1 w\<^sub>2 = NEG_INF"
          using i1 n2 unfolding NEG_INF_def
          by (metis bound1b min.absorb_iff2 min_def n2 not_less of_int_less_iff wmin.simps word_sless_alt)
        have res2:"NEG_INF \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2"
          apply(rule repNEG_INF)
          using eq1 eq2 bound1a bound1b bound2
          using min_le_iff_disj by blast
        show "wmin w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2"
          using res1 res2 by auto
        qed
    subgoal for ra
      proof -
        assume i1:"w\<^sub>1 = r"
        assume i2:"w\<^sub>2 = ra"
        assume eq1:"r\<^sub>1 =  (real_of_int (sint r))"
        assume eq2:"r\<^sub>2 =  (real_of_int (sint ra))"
        assume bound1a:" (real_of_int (sint r)) <  (real_of_int (sint POS_INF))"
        assume bound1b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint r))"
        assume bound2a:" (real_of_int (sint ra)) <  (real_of_int (sint POS_INF))"
        assume bound2b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint ra))"
        have res1:"min r\<^sub>1 r\<^sub>2 =  (real_of_int (sint (wmin w\<^sub>1 w\<^sub>2)))"
          using eq1 eq2 bound1a bound1b bound2a bound2b i1 i2
          by (simp add: min_def word_sless_alt)
        have res2:"wmin w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E (real_of_int (sint (wmin w\<^sub>1 w\<^sub>2)))"
          apply (rule repINT)
          using i1 i2 bound1a bound1b bound2a bound2b
          by (simp add: \<open>min r\<^sub>1 r\<^sub>2 =  (real_of_int (sint (wmin w\<^sub>1 w\<^sub>2)))\<close> eq2 min_less_iff_disj)+
        show "wmin w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>E min r\<^sub>1 r\<^sub>2"
          using res1 res2 by auto
        qed
      done
    done
    
    
lemma min_repU1:
  assumes "w1 \<equiv>\<^sub>L x"
  assumes "w2 \<equiv>\<^sub>L y"
  shows "wmin w1 w2 \<equiv>\<^sub>L x "
  using wmin_lemma assms repL_def
  by (meson min_le_iff_disj)

lemma min_repU2:
  assumes "w1 \<equiv>\<^sub>L y"
  assumes "w2 \<equiv>\<^sub>L x"
  shows "wmin w1 w2 \<equiv>\<^sub>L x"
  using wmin_lemma assms repL_def
by (meson min_le_iff_disj)

fun tl :: "word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word"
where "tl w1l w1u w2l w2u =
  wmin (wmin (wtimes w1l w2l) (wtimes w1u w2l))
       (wmin (wtimes w1l w2u) (wtimes w1u w2u)) "

lemmas real_zero_le_0_iff = zero_le_mult_iff

lemma tl_lemma:
  assumes u1:"u\<^sub>1 \<equiv>\<^sub>U (r\<^sub>1::real)"
  assumes u2:"u\<^sub>2 \<equiv>\<^sub>U (r\<^sub>2::real)"
  assumes l1:"l\<^sub>1 \<equiv>\<^sub>L (r\<^sub>1::real)"
  assumes l2:"l\<^sub>2 \<equiv>\<^sub>L (r\<^sub>2::real)"
  shows "tl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L (r\<^sub>1 * r\<^sub>2)"
proof -
  obtain rl1 rl2 ru1 ru2 :: real 
  where gru1:"ru1 \<ge> r\<^sub>1" and gru2:"ru2 \<ge> r\<^sub>2" and grl1:"rl1 \<le> r\<^sub>1" and grl2:"rl2 \<le> r\<^sub>2" 
  and eru1:"u\<^sub>1 \<equiv>\<^sub>E ru1" and eru2:"u\<^sub>2 \<equiv>\<^sub>E ru2" and erl1:"l\<^sub>1 \<equiv>\<^sub>E rl1" and erl2:"l\<^sub>2 \<equiv>\<^sub>E rl2"
  using u1 u2 l1 l2 unfolding repU_def repL_def by auto
  have timesuu:"wtimes u\<^sub>1 u\<^sub>2 \<equiv>\<^sub>E ru1 * ru2"
    using wtimes_exact[OF eru1 eru2] by auto
  have timesul:"wtimes u\<^sub>1 l\<^sub>2 \<equiv>\<^sub>E ru1 * rl2"
    using wtimes_exact[OF eru1 erl2] by auto
  have timeslu:"wtimes l\<^sub>1 u\<^sub>2 \<equiv>\<^sub>E rl1 * ru2"
    using wtimes_exact[OF erl1 eru2] by auto
  have timesll:"wtimes l\<^sub>1 l\<^sub>2 \<equiv>\<^sub>E rl1 * rl2"
    using wtimes_exact[OF erl1 erl2] by auto
  have maxt12:"wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2) \<equiv>\<^sub>E min (rl1 * rl2) (ru1 * rl2)"
    by (rule  wmin_lemma[OF timesll timesul])
  have maxt34:"wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2) \<equiv>\<^sub>E min (rl1 * ru2) (ru1 * ru2)"
    by (rule  wmin_lemma[OF timeslu timesuu])
  have bigMax:"wmin (wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2))
    \<equiv>\<^sub>E min (min(rl1 * rl2) (ru1 * rl2)) (min (rl1 * ru2) (ru1 * ru2))"
    by (rule wmin_lemma[OF maxt12 maxt34])
  obtain maxt12val :: real where maxU12:"wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2) \<equiv>\<^sub>L min (rl1 * rl2) (ru1 * rl2)"
  using maxt12 unfolding repL_def by blast
  obtain maxt34val :: real where maxU34:"wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2) \<equiv>\<^sub>L min (rl1 * ru2) (ru1 * ru2)"
  using maxt34 unfolding repL_def by blast
  obtain bigMaxU:"wmin (wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2))
    \<equiv>\<^sub>L min (min (rl1 * rl2) (ru1 * rl2)) (min (rl1 * ru2) (ru1 * ru2))"
  using bigMax unfolding repL_def by blast
        
  have ivl1:"rl1 \<le> ru1" using grl1 gru1 by auto
  have ivl2:"rl2 \<le> ru2" using grl2 gru2 by auto
  let ?thesis = "tl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L r\<^sub>1 * r\<^sub>2"
  show ?thesis
  apply(rule case_ivl_zero[OF ivl1 ivl2])
  proof -
    assume "rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    then have geq1:"ru1 \<ge> 0" and geq2:"ru2 \<ge> 0" 
    and geq3:"rl1 \<le> 0" and geq4:"rl2 \<le> 0" by auto
    have case1:"r\<^sub>1 \<ge> 0 \<Longrightarrow> r\<^sub>2 \<ge> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r1:"r\<^sub>1 \<ge> 0"
        assume r2:"r\<^sub>2 \<ge> 0"
        have g1:"rl1 * ru2 \<le> 0" 
          using r1 geq1 geq2 geq3 geq4 grl2 gru2 mult_le_0_iff by blast
        have g2:"0 \<le>  r\<^sub>1 * r\<^sub>2"
          using r1 r2 geq1 geq2 grl1 grl2 gru1 gru2
          by (simp)
        from g1 and g2
        have up:"rl1 * ru2 \<le> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up eru1 eru2 erl1 erl2 min_repU1 min_repU2 repL_def repU_def timeslu tl.simps wmin.elims
        by (metis bigMax min_le_iff_disj)
      qed
    have case2:"r\<^sub>1 \<le> 0 \<Longrightarrow> r\<^sub>2 \<ge> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r1:"r\<^sub>1 \<le> 0"
        assume r2:"r\<^sub>2 \<ge> 0"
        have g1:"rl1 * ru2 \<le> rl1 * r\<^sub>2" 
          using r1 geq1 geq2 grl2 gru2
          by (metis silly_lemma  geq3 leD)
        have g2:"rl1 * r\<^sub>2 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 geq1 geq2 grl2 gru2
          by (simp add: mult_right_mono grl1)
        from g1 and g2
        have up:"rl1 * ru2 \<le> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        by (metis up maxU12 min_repU2 repL_def tl.simps min.coboundedI1 maxt34)
      qed
    have case3:"r\<^sub>1 \<ge> 0 \<Longrightarrow> r\<^sub>2 \<le> 0 \<Longrightarrow> ?thesis"
      proof -
        assume r1:"r\<^sub>1 \<ge> 0"
        assume r2:"r\<^sub>2 \<le> 0"
        have g1:"ru1 * rl2 \<le> ru1 * r\<^sub>2" 
          using r1 r2 geq1 geq2 grl2 gru2
          by (simp add: mult_left_mono)
        have g2:"ru1 * r\<^sub>2 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 geq1 geq2 grl1 grl2 gru1 gru2 mult_minus_right mult_right_mono
          by (simp add: mult_right_mono_neg)
        from g1 and g2
        have up:"ru1 * rl2 \<le> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1 maxt34 timesul
        by (metis repL_def tl.simps)
      qed
    have case4:"r\<^sub>1 \<le> 0 \<Longrightarrow> r\<^sub>2 \<le> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r1:"r\<^sub>1 \<le> 0"
        assume r2:"r\<^sub>2 \<le> 0"
        have g1:"ru1 * rl2 \<le> 0" 
          using r1 r2 geq1 geq2 grl1 grl2 gru1 gru2 \<open>rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2\<close>  mult_less_0_iff  less_eq_real_def not_less
          by auto
        have g2:"0 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 geq1 geq2 grl1 grl2 gru1 gru2
          by (metis mult_less_0_iff  not_less)
        from g1 and g2
        have up:"ru1 * rl2 \<le> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        by (metis up maxU12 maxU34 wmin.elims min_repU1 min_repU2 repL_def timesul tl.simps) 
      qed
    show "tl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L r\<^sub>1 * r\<^sub>2"
      using case1 case2 case3 case4 le_cases by blast
  next
    assume bounds:"rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> 0 \<le> rl2"
    have r2:"r\<^sub>2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    have case1:"r\<^sub>1 \<ge> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r1:"r\<^sub>1 \<ge> 0"
        have g1:"rl1 * rl2 \<le> 0" 
          using r1 r2 bounds grl1 grl2 gru1 gru2
          by (simp add: mult_le_0_iff)
        have g2:"0 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2
          by (simp)
        from g1 and g2
        have up:"rl1 * rl2 \<le> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
          by (metis repL_def timesll tl.simps up maxU12 maxU34  wmin.elims min_repU2 min_repU1) 
      qed
    have case2:"r\<^sub>1 \<le> 0 \<Longrightarrow> ?thesis"
      proof -
        assume r1:"r\<^sub>1 \<le> 0"
        have bound:"ru2 \<ge> 0"
        using r1 r2 bounds grl1 grl2 gru1 gru2
          using dual_order.trans by auto
        then have g1:"rl1 * ru2 \<le> rl1 * r\<^sub>2" 
          using r1 r2 bounds grl1 grl2 gru1 gru2
          by (smt silly_lemma)
        have g2:"rl1 * r\<^sub>2 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2 mult_le_0_iff mult_le_cancel_right by fastforce
        from g1 and g2
        have up:"rl1 * ru2 \<le> r\<^sub>1 * r\<^sub>2" by auto
        show ?thesis
         by (metis up maxU12 wmin.elims min_repU2 min.coboundedI1 maxt34 repL_def tl.simps) 
      qed
    show "tl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L r\<^sub>1 * r\<^sub>2"
      using case1 case2 le_cases by blast
  next
    assume bounds:"rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> ru2 \<le> 0"
    have r2:"r\<^sub>2 \<le> 0" using bounds dual_order.trans gru2 by blast
    have case1:"r\<^sub>1 \<ge> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r1:"r\<^sub>1 \<ge> 0"
        have bound:"rl2 \<le> 0"
          using r1 r2 bounds grl1 grl2 gru1 gru2
          using dual_order.trans by auto
        then have g1:"ru1 * rl2 \<le> ru1 * r\<^sub>2" 
          using r1 r2 bounds grl1 grl2 gru1 gru2
          by (smt silly_lemma )
        have p1:"\<And>a::real. (0 \<le> - a) = (a \<le> 0)"
          by(auto)
        have p2:"\<And>a b::real.  (- a \<le> - b) = (b \<le> a)" by auto
        have g2:"ru1 * r\<^sub>2 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2 p1 p2
          by (simp add: mult_right_mono_neg)
        from g1 and g2
        have up:"ru1 * rl2 \<le> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis 
        by (metis  up maxU12 maxU34  wmin.elims min_repU2 min_repU1 repL_def timesul tl.simps)
      qed
    have case2:"r\<^sub>1 \<le> 0 \<Longrightarrow> ?thesis"
    proof -
        assume r1:"r\<^sub>1 \<le> 0"
        have g1:"ru1 * ru2 \<le> 0" 
          using r1 r2 bounds  grl1 grl2 gru1 gru2
          using mult_le_0_iff by blast
        have g2:"0 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 real_zero_le_0_iff by blast  
        from g1 and g2
        have up:"ru1 * ru2 \<le> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1 
        min.coboundedI1 min.commute maxt34 
        by (metis repL_def tl.simps) 
      qed
    show "tl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L r\<^sub>1 * r\<^sub>2"
      using case1 case2 le_cases by blast
  next
    assume bounds:"0 \<le> rl1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    have r1:"r\<^sub>1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    have bound:"0 \<le> ru1"  using r1  bounds grl1 grl2 gru1 gru2  
      using dual_order.trans by auto
    have case1:"r\<^sub>2 \<ge> 0 \<Longrightarrow> ?thesis"
      proof -
        assume r2:"r\<^sub>2 \<ge> 0"
        have g1:"rl1 * rl2 \<le> 0" 
          using r1 r2 bounds grl1 grl2 gru1 gru2
          using mult_le_0_iff by blast
        have g2:"0 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2
          using real_zero_le_0_iff by blast
        from g1 and g2
        have up:"rl1 * rl2 \<le> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims min_repU2 min_repU1 
        min.coboundedI1 min.commute maxt12 maxt34
        using  repL_def timesll tl.simps
        by metis          
      qed
    have case2:"r\<^sub>2 \<le> 0 \<Longrightarrow> ?thesis"
      proof -
        assume r2:"r\<^sub>2 \<le> 0"
        have g1:"ru1 * rl2 \<le> ru1 * r\<^sub>2" 
          using r1 bounds bound grl1 grl2 gru1 r2 gru2
          using mult_left_mono by blast
        have g2:"ru1 * r\<^sub>2 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds bound grl1 grl2 gru1 r2 gru2
          proof -
            have "\<forall>e ea. r\<^sub>2 * ea \<le> r\<^sub>2 * e \<or> \<not> e \<le> ea" 
              using r2 by (metis mult_left_mono_neg)
            then show ?thesis
              by (metis gru1 mult.commute)
          qed
        from g1 and g2
        have up:"ru1 * rl2 \<le> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1 maxt34
        by (metis repL_def timesul tl.simps)
      qed
    show "tl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L r\<^sub>1 * r\<^sub>2"
      using case1 case2 le_cases by blast      
  next
    assume bounds:"ru1 \<le> 0 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    have r1:"r\<^sub>1 \<le> 0"  using bounds dual_order.trans gru1 by blast
    have bound:"rl1 \<le> 0" using r1  bounds grl1 grl2 gru1 gru2  
      using dual_order.trans by auto
    have case1:"r\<^sub>2 \<ge> 0 \<Longrightarrow> ?thesis" 
      proof -
        assume r2:"r\<^sub>2 \<ge> 0"
        have g1:"rl1 * ru2 \<le> rl1 * r\<^sub>2" 
          using r1 r2 bounds bound grl1 grl2 gru1 gru2
          by (metis real_mult_le_mult_iff leD)  
        have g2:"rl1 * r\<^sub>2 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2
          using mult_right_mono 
          by (simp add: mult_le_0_iff)
        from g1 and g2
        have up:"rl1 * ru2 \<le> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims min_repU2 min_repU1
        min.coboundedI1 min.commute maxt34
        by (metis  min_repU2 repL_def tl.simps) 
      qed
    have case2:"r\<^sub>2 \<le> 0 \<Longrightarrow> ?thesis"
    proof -
        assume r2:"r\<^sub>2 \<le> 0"
        have lower:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
        have g1:"ru1 * ru2 \<le> 0" 
          using r1 r2 bounds  grl1 grl2 gru1 gru2
          using mult_le_0_iff by blast
        have g2:"0 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 
          by (simp add: real_zero_le_0_iff)
        from g1 and g2
        have up:"ru1 * ru2 \<le> r\<^sub>1 * r\<^sub>2"
          by auto
        show ?thesis
        using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1 
        min.coboundedI1 min.commute maxt34
        by (metis repL_def tl.simps)
      qed
    show "tl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L r\<^sub>1 * r\<^sub>2"
      using case1 case2 le_cases by blast
  next
    assume bounds:"ru1 \<le> 0 \<and> ru2 \<le> 0"
    have r1:"r\<^sub>1 \<le> 0" using bounds dual_order.trans gru1 by blast
    have r2:"r\<^sub>2 \<le> 0" using bounds dual_order.trans gru2 by blast
    have lower1:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
    have lower2:"rl2 \<le> 0" using bounds dual_order.trans grl2 r2 by blast

    have g1:"ru1 * ru2 \<le> ru1 * r\<^sub>2" 
      using r1 r2 bounds  grl1 grl2 gru1 gru2
      using    not_less silly_lemma
      by metis
    have g2:"ru1 * r\<^sub>2 \<le> r\<^sub>1 * r\<^sub>2"
      using r1 r2 bounds grl1 grl2 gru1 gru2 real_mult_le_mult_iff  mult.commute not_le lower1 lower2
      by smt
    from g1 and g2
    have up:"ru1 * ru2 \<le> r\<^sub>1 * r\<^sub>2"
      by auto
    show ?thesis
      using up maxU12 maxU34 bigMaxU 
      wmin.elims min_repU2 min_repU1 
      min.coboundedI1 min.commute maxt34 
      by (metis repL_def tl.simps)
  next
    assume bounds:"ru1 \<le> 0 \<and> 0 \<le> rl2"
    have r1:"r\<^sub>1 \<le> 0" using bounds dual_order.trans gru1 by blast
    have r2:"r\<^sub>2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    have lower1:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
    have lower2:"rl2 \<ge> 0" using bounds by auto
    have upper1:"ru1 \<le> 0" using bounds by auto 
    have upper2:"ru2 \<ge> 0" using bounds dual_order.trans gru2 r2 by blast
    have g1:"rl1 * ru2 \<le> rl1 * r\<^sub>2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2 less_le_trans not_less upper1 lower2 real_mult_le_mult_iff
      by metis
    have g2:"rl1 * r\<^sub>2 \<le> r\<^sub>1 * r\<^sub>2"
      using r1 upper1 r2 mult_right_mono mult_le_0_iff grl1 by blast
    from g1 and g2
    have up:"rl1 * ru2 \<le> r\<^sub>1 * r\<^sub>2"
      by auto
    show ?thesis
    using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1 maxt12 maxt34 
    by (metis repL_def timeslu tl.simps)
  next 
    assume bounds:"0 \<le> rl1 \<and> ru2 \<le> 0"
    have r1:"r\<^sub>1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    have r2:"r\<^sub>2 \<le> 0" using bounds dual_order.trans gru2 by blast
    have lower1:"rl1 \<ge> 0" using bounds by auto
    have lower2:"rl2 \<le> 0" using dual_order.trans grl2 r2 by blast
    have upper1:"ru1 \<ge> 0" using dual_order.trans gru1 u1 r1 by blast  
    have upper2:"ru2 \<le> 0" using bounds by auto
    have g1:"ru1 * rl2 \<le> ru1 * r\<^sub>2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2 mult_left_mono less_le_trans not_less
      by metis
    have g2:"ru1 * r\<^sub>2 \<le> r\<^sub>1 * r\<^sub>2"
      using r1 lower1 r2 not_less gru2 gru1 grl1 grl2
      by (metis real_mult_le_mult_iff  mult.commute)
    from g1 and g2
    have up:"ru1 * rl2 \<le> r\<^sub>1 * r\<^sub>2"
      by auto
    show "tl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L r\<^sub>1 * r\<^sub>2"
      using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1
      by (metis repL_def timesul tl.simps)
  next
    assume bounds:"0 \<le> rl1 \<and> 0 \<le> rl2"
    have r1:"r\<^sub>1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    have r2:"r\<^sub>2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    have lower1:"rl1 \<ge> 0" using bounds by auto
    have lower2:"rl2 \<ge> 0" using bounds by auto
    have upper1:"ru1 \<ge> 0" using dual_order.trans gru1 u1 r1 by blast  
    have upper2:"ru2 \<ge> 0" using dual_order.trans gru2 u2 r2 bounds by blast
    have g1:"rl1 * rl2 \<le> rl1 * r\<^sub>2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2
      using mult_left_mono 
      using leD leI less_le_trans by auto
    have g2:"rl1 * r\<^sub>2 \<le> r\<^sub>1 * r\<^sub>2"
      using r1 r2 bounds grl1 grl2 gru1 gru2
      using mult_right_mono by blast
    from g1 and g2
    have up:"rl1 * rl2 \<le> r\<^sub>1 * r\<^sub>2"
      by auto
    show ?thesis
    using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1
      min.coboundedI1 min.commute maxt12 maxt34
      by (metis repL_def tl.simps)
  qed
  qed

lemma msb_succ:
  fixes w :: "32 Word.word"
  assumes neq1:"uint w \<noteq> 0xFFFFFFFF"
  assumes neq2:"uint w \<noteq> 0x7FFFFFFF"
  shows "msb (w + 1) = msb w"
  proof -
    have "w \<noteq> 0xFFFFFFFF"
      using neq1 by auto
    then have neqneg1:"w \<noteq> -1" by auto
    have "w \<noteq> 0x7FFFFFFF"
      using neq2 by auto
    then have neqneg2:"w \<noteq> (2^31)-1" by auto
    show ?thesis using neq1 neq2  unfolding msb_big
    using Word_Lemmas.word_le_make_less[of "w + 1" "0x80000000"] 
            Word_Lemmas.word_le_make_less[of "w " "0x80000000"]
            neqneg1 neqneg2
      by auto
  qed
  
lemma msb_non_min:
  fixes w :: "32 Word.word"
  assumes neq1:"uint w \<noteq> 0"
  assumes neq2:"uint w \<noteq> ((2^(len_of (TYPE(31)))))"
  shows "msb (uminus w) = HOL.Not(msb(w))"
  proof -
    have fact1:"uminus w = word_succ (~~ w)"
      by (rule twos_complement)
    have fact2:"msb (~~w) = HOL.Not(msb w)"
      using Word.word_ops_msb[of w] 
      by auto
    have neqneg1:"w \<noteq> 0" using neq1 by auto
    have not_undef:"w \<noteq> 0x80000000"
      using neq2 by auto
    then have neqneg2:"w \<noteq> (2^31)" by auto
    have "~~ 0xFFFFFFFF = (0::word)" by auto
    then have "(~~ w) \<noteq> 0xFFFFFFFF"
      using neqneg1 neqneg2 Word.word_bool_alg.double_compl[of w] 
      by metis
    then have uintNeq1:"uint (~~ w) \<noteq> 0xFFFFFFFF"
      using uint_distinct[of "~~w" "0xFFFFFFFF"] 
      by auto
    have "~~ (0x7FFFFFFF::word) = (2 ^ 31::word)" by (auto simp add: max_word_def)
    then have "(~~ w) \<noteq> 0x7FFFFFFF"
      using neqneg1 neqneg2 Word.word_bool_alg.double_compl[of w] 
      by metis
    then have uintNeq2:" uint (~~ w) \<noteq> 0x7FFFFFFF"
      using uint_distinct[of "~~w" "0x7FFFFFFF"]
      by auto
    have fact3:"msb ((~~w) + 1) = msb (~~w)"
      apply(rule msb_succ[of "~~w"])
      using neq1 neq2 uintNeq1 uintNeq2 by auto 
    show "msb (uminus w) = HOL.Not(msb(w))"
      using fact1 fact2 fact3 by (simp add: word_succ_p1)
    qed
 
lemma msb_min_neg:
  fixes w::"word"
  assumes msb1:"msb (- w)"
  assumes msb2:"msb w"
  shows "uint w = ((2^(len_of (TYPE(31)))))"
  proof -
    have neq1:"uint w \<noteq> 0" using msb2 word_msb_0 uint_0_iff by force
    show ?thesis using msb1 msb2 msb_non_min[OF neq1] 
    by auto
  qed
     
lemma msb_zero:
  fixes w::"word"
  assumes msb1:"\<not> msb (- w)"
  assumes msb2:"\<not> msb w"
  shows "uint w = 0"
  proof -
    have neq:"w \<noteq> ((2 ^ len_of TYPE(31))::word)" using msb1 msb2 by auto
    have eq:"uint ((2 ^ len_of TYPE(31))::word) = 2 ^ len_of TYPE(31)" 
      by auto
    then have neq:"uint w \<noteq> uint ((2 ^ len_of TYPE(31))::word) " using uint_distinct[of w "2^len_of TYPE(31)"] neq eq by auto
    show ?thesis
      using msb1 msb2 minus_zero msb_non_min[of w] neq by force
  qed
    
lemma msb_pos:
  fixes w::"word"
  assumes msb1:"msb (- w)"
  assumes msb2:"\<not> msb w"
  shows "uint w \<in> {1 .. (2^((len_of TYPE(32)) - 1))-1}" 
  proof -
    have main: "w \<in> {1 .. (2^((len_of TYPE(32)) - 1))-1}"
      using msb1 msb2 apply(clarsimp) 
      unfolding word_msb_sint
      apply(rule conjI)
      apply (metis neg_equal_0_iff_equal not_le word_less_1)
      proof -
        have imp:"w \<ge> 0x80000000 \<Longrightarrow> False"
          proof -
            assume geq:"w \<ge> 0x80000000"
            then have "msb w"
              using Word_Lemmas.msb_big[of w] by auto
            then show False using msb2 by auto
          qed
        have mylem:"\<And>w1 w2::word. uint w1 \<ge> uint w2 \<Longrightarrow> w1 \<ge> w2" 
          subgoal for w1 w2 
            by (simp add: word_le_def)
          done
        have mylem2:"\<And>w1 w2::word.  w1 >  w2 \<Longrightarrow> uint w1 > uint w2" 
          subgoal for w1 w2 
            by (simp add: word_less_def)
          done
        have gr_to_geq:"w > 0x7FFFFFFF \<Longrightarrow> w \<ge> 0x80000000"
          apply(rule mylem)
          using mylem2[of "0x7FFFFFFF" "w"] by auto
        have taut:"w \<le> 0x7FFFFFFF \<or> w > 0x7FFFFFFF" by auto        
        then show "w \<le> 0x7FFFFFFF"
        using imp taut gr_to_geq by auto
      qed
    have set_eq:"(uint ` (({1..(minus(2 ^ (minus(len_of TYPE(32))  1)) 1)})::word set)) = ({1..minus(2 ^ (minus (len_of TYPE(32)) 1)) 1}::int set)"
      apply(auto)
      subgoal for xa by (simp add: word_le_def)
      subgoal for xa by (simp add: word_le_def)
      subgoal for xa 
      proof -
        assume lower:"1 \<le> xa" and upper:"xa \<le> 2147483647"
        then have in_range:"xa \<in> {0 .. 2^32-1}" by auto
        then have "xa \<in> range (uint::word \<Rightarrow> int)" unfolding Word.word_uint.Rep_range Word.uints_num by auto
        then obtain w::word  where xaw:"xa = uint w" by auto
        then have "w \<in> {1..0x7FFFFFFF} " 
        using lower upper apply(clarsimp, auto)
        subgoal by (simp add: word_le_def)
        subgoal by (simp add: word_le_def)
        done
        then show ?thesis
      using uint_distinct uint_distinct main image_eqI
      using word_le_def xaw by blast
      qed
      done
    then show  "uint w \<in> {1..2 ^ (len_of TYPE(32) - 1) - 1}" 
      using uint_distinct uint_distinct main image_eqI
      by blast
    qed
    
lemma msb_neg:
  fixes w::"word"
  assumes msb1:"\<not> msb (- w)"
  assumes msb2:"msb w"
  shows "uint w \<in> {2^((len_of TYPE(32) - 1))+1 .. 2^((len_of TYPE(32)))-1}" 
  proof -
    have mylem:"\<And>w1 w2::word. uint w1 \<ge> uint w2 \<Longrightarrow> w1 \<ge> w2" 
          subgoal for w1 w2 
            by (simp add: word_le_def)
          done
        have mylem2:"\<And>w1 w2::word.  w1 >  w2 \<Longrightarrow> uint w1 > uint w2" 
          subgoal for w1 w2 
            by (simp add: word_less_def)
          done
        have gr_to_geq:"w > 0x80000000 \<Longrightarrow> w \<ge> 0x80000001"
          apply(rule mylem)
          using mylem2[of "0x80000000" "w"] by auto
        have taut:"w \<le> 0x80000000 \<or> 0x80000000 < w" by auto
        have imp:"w \<le> 0x80000000 \<Longrightarrow> False"
          proof -
            assume geq:"w \<le> 0x80000000"
            then have "(msb (-w))"
              using Word_Lemmas.msb_big[of "-w"] Word_Lemmas.msb_big[of "w"] 
              by (simp add: msb2) 
            then show False using msb1 by auto
          qed
      have main: "w \<in> {2^((len_of TYPE(32)) - 1)+1 .. 2^((len_of TYPE(32)))-1}"  
      using msb1 msb2 apply(clarsimp)
      unfolding word_msb_sint
      proof -
        show "0x80000001 \<le> w"
        using imp taut gr_to_geq by auto
      qed
    have set_eq:"(uint ` (({2^((len_of TYPE(32) - 1))+1 .. 2^((len_of TYPE(32)))-1})::word set)) 
                       = {2^((len_of TYPE(32) - 1))+1 .. 2^((len_of TYPE(32)))-1}"
      apply(auto)
      subgoal for xa by (simp add: word_le_def)
      subgoal for w using Word.word.uint[of w] by auto
      subgoal for xa
      proof -
        assume lower:"2147483649 \<le> xa" and upper:"xa \<le> 4294967295"
        then have in_range:"xa \<in> {0x80000000 .. 0xFFFFFFFF}" by auto
        then have "xa \<in> range (uint::word \<Rightarrow> int)" unfolding Word.word_uint.Rep_range Word.uints_num by auto
        then obtain w::word  where xaw:"xa = uint w" by auto
        then have the_in:"w \<in> {0x80000001 .. 0xFFFFFFFF} " 
        using lower upper apply(clarsimp, auto)
        subgoal by (simp add: word_le_def)
        subgoal by (simp add: word_le_def)
        done
        have the_eq:"(0xFFFFFFFF::word) = -1" by auto
        from the_in the_eq have "w \<in> {0x80000001 .. -1}" by auto
        then show ?thesis
      using uint_distinct uint_distinct main image_eqI 
      using  word_le_def xaw by blast
      qed
      done
    then show  "uint w \<in> {2^((len_of TYPE(32)) - 1)+1 .. 2^((len_of TYPE(32)))-1}" 
      using uint_distinct uint_distinct main image_eqI
      by blast
    qed

lemma sint_neg_hom:
  fixes w :: "32 Word.word"
  shows "uint w \<noteq> ((2^(len_of (TYPE(31))))) \<Longrightarrow> (sint(-w) = -(sint w))"
  unfolding WordBitwise.word_sint_msb_eq apply auto
  subgoal using msb_min_neg by auto 
  prefer 3 subgoal using msb_zero[of w] by (simp add: msb_zero)
  subgoal
    proof -
      assume msb1:"msb (- w)"
      assume msb2:"\<not> msb w"
      have "uint w \<in> {1 .. (2^((len_of TYPE(32)) - 1))-1}" using msb_pos[OF msb1 msb2] by auto
      then have bound:"uint w \<in> {1 .. 0x7FFFFFFF}" by auto
      have size:"size (w::32 Word.word) = 32" using Word.word_size[of w] by auto 
      have lem:"\<And>x::int. \<And>n::nat.   x \<in> {1..(2^n)-1} \<Longrightarrow> ((- x) mod (2^n)) - (2^n) = - x"
      subgoal for x n
        apply(auto)
        using Divides.zmod_zminus1_eq_if[of x  "2^n"]
        apply(cases "x mod 2^n = 0")
        subgoal apply simp done
        subgoal by (simp add: int_mod_eq')
        done
      done
      have lem_rule:"uint w \<in> {1..2 ^ 32 - 1} \<Longrightarrow> (- uint w mod  4294967296) - 4294967296 = - uint w"
        using lem[of "uint w" 32] by auto
      have almost:"- uint w mod 4294967296 - 4294967296 = - uint w"
        apply(rule lem_rule)  
        using bound by auto
      show "uint (- w) - 2 ^ size (- w) = - uint w"
      using bound
      unfolding Word.uint_word_ariths word_size_neg by (auto simp add: size almost)
    qed
  proof -
  assume neq:"uint w \<noteq> 0x80000000"
  assume msb1:"\<not> msb (- w)"
  assume msb2:"msb w"
  have bound:"uint w \<in> {0x80000001.. 0xFFFFFFFF}" using msb1 msb2 msb_neg by auto
  have size:"size (w::32 Word.word) = 32" using Word.word_size[of w] by auto
  have lem:"\<And>x::int. \<And>n::nat.   x \<in> {1..(2^n)-1} \<Longrightarrow> (-x mod (2^n)) = (2^n) - x"
      subgoal for x n
        apply(auto)
        apply(cases "x mod 2^n = 0")
        using Divides.zmod_zminus1_eq_if[of x  "2^n"]  Divides.zmod_zminus1_eq_if[of x  "2^n"] int_mod_ge by (smt int_mod_ge')+
      done
  show "uint (- w) = 2 ^ size w - uint w"
    using bound
    unfolding Word.uint_word_ariths word_size_neg apply (auto simp add: size lem)
    using Word.uint_word_ariths word_size_neg msb_non_min 
    by (smt int_mod_ge mod_add_self2 zmod_le_nonneg_dividend)
  qed

lemma sint_dist:
  fixes x y ::word
  assumes "x \<noteq> y"
  shows "sint x \<noteq> sint y"
  by (simp add: assms)

fun wneg :: "word \<Rightarrow> word"
where "wneg w = 
  (if w = NEG_INF then POS_INF else if w = POS_INF then NEG_INF else -w)"

lemma wneg_lemma:
  assumes eq:"w \<equiv>\<^sub>E (r::real)"
  shows "wneg w \<equiv>\<^sub>E -r"
  apply(rule repe.cases[OF eq])
  subgoal for ra
    apply(auto simp add: POS_INF_def)
    apply(rule repNEG_INF)
    by(auto simp add: POS_INF_def NEG_INF_def)
  subgoal for ra
    apply(auto simp add: NEG_INF_def)
    apply(rule repPOS_INF)
    by(auto simp add: POS_INF_def NEG_INF_def)
  subgoal for ra
  proof -
    assume eq:"w = ra"
    assume i:"r =  (real_of_int (sint ra))"
    assume bounda:" (real_of_int (sint ra)) <  (real_of_int (sint POS_INF))"
    assume boundb:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint ra))"
    have raNeq:"ra \<noteq> 2147483647"
      using sint_range[OF bounda boundb]
      by (auto simp add: POS_INF_def NEG_INF_def)
    have raNeqUndef:"ra \<noteq> 2147483648"
      using int_not_undef[OF bounda boundb]
      by (auto simp add: NEG_INF_def)
    have "uint ra \<noteq> uint ((2 ^ len_of TYPE(31))::word)"
      apply (rule uint_distinct)
      using raNeqUndef by auto
    then have raNeqUndefUint:"uint ra \<noteq> ((2 ^ len_of TYPE(31)))"
      by auto
    have res1:"wneg w \<equiv>\<^sub>E  (real_of_int (sint (wneg w)))"
      apply (rule repINT)
      using sint_range[OF bounda boundb]
      apply (auto simp add: POS_INF_def NEG_INF_def)
      using sint_neg_hom[of ra, OF raNeqUndefUint]
      raNeq raNeqUndefUint raNeqUndef eq 
      by(auto)
    have res2:"- r =  (real_of_int (sint (wneg w)))"
      using eq bounda boundb i sint_neg_hom[of ra, OF raNeqUndefUint] raNeq raNeqUndef eq
      by (auto simp add: NEG_INF_def POS_INF_def)
    show ?thesis
      using res1 res2 by auto
    qed
  done

fun wle :: "word \<Rightarrow> word \<Rightarrow> bool"
where "wle w\<^sub>1 w\<^sub>2 = (sint w\<^sub>1 < sint w\<^sub>2)"

lemma neg_less_contra:"\<And>x. Suc x < - (Suc x) \<Longrightarrow> False"
  by auto

lemma wle_lemma:"w\<^sub>1 \<equiv>\<^sub>U (r\<^sub>1::real) \<Longrightarrow> w\<^sub>2 \<equiv>\<^sub>L r\<^sub>2 \<Longrightarrow> wle w\<^sub>1 w\<^sub>2 \<Longrightarrow> r\<^sub>1 < r\<^sub>2"
  unfolding repU_def repL_def
  apply(auto simp add: POS_INF_def NEG_INF_def )
  subgoal for r'\<^sub>1 r'\<^sub>2 
    proof -
      assume sint_le:"sint w\<^sub>1 < sint w\<^sub>2"
      then have sless:"(w\<^sub>1 <s w\<^sub>2)" using word_sless_alt by auto
      assume r1_leq:"r\<^sub>1 \<le> r'\<^sub>1"
      assume r2_leq:"r'\<^sub>2 \<le> r\<^sub>2"
      assume wr1:"w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1"
      assume wr2:"w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2"
      have less:"r'\<^sub>1 < r'\<^sub>2" 
        using wr1 wr2 apply(auto simp add: repe.simps POS_INF_def NEG_INF_def)
        prefer 4 using sless sint_le  by (auto simp add: less_le_trans  not_le)
      show "r\<^sub>1 < r\<^sub>2"
        using r1_leq r2_leq less by auto
    qed
  done

fun wleq :: "word \<Rightarrow> word \<Rightarrow> bool"
where "wleq w\<^sub>1 w\<^sub>2 =
((\<not> ((w\<^sub>1 = NEG_INF \<and> w\<^sub>2 = NEG_INF)
  \<or>(w\<^sub>1 = POS_INF \<and> w\<^sub>2 = POS_INF))) \<and>
(sint w\<^sub>1 \<le> sint w\<^sub>2))"

lemma wleq_lemma:"w\<^sub>1 \<equiv>\<^sub>U (r\<^sub>1::real) \<Longrightarrow> w\<^sub>2 \<equiv>\<^sub>L r\<^sub>2 \<Longrightarrow> wleq w\<^sub>1 w\<^sub>2 \<Longrightarrow> r\<^sub>1 \<le> r\<^sub>2"
  unfolding wleq.simps
  subgoal 
    proof -
      assume assms:"\<not> (w\<^sub>1 = NEG_INF \<and> w\<^sub>2 = NEG_INF \<or> w\<^sub>1 = POS_INF \<and> w\<^sub>2 = POS_INF) \<and> sint w\<^sub>1 \<le> sint w\<^sub>2"
      assume a1:"w\<^sub>1 \<equiv>\<^sub>U (r\<^sub>1::real)" and a2:"w\<^sub>2 \<equiv>\<^sub>L r\<^sub>2"
      from assms have sint_le:"sint w\<^sub>1 \<le> sint w\<^sub>2" apply(auto simp add: POS_INF_def NEG_INF_def ) done
      then have sless:"(w\<^sub>1 <=s w\<^sub>2)" using word_sless_alt word_sle_def by auto
      obtain r'\<^sub>1 r'\<^sub>2 where  r1_leq:"r\<^sub>1 \<le> r'\<^sub>1" and r2_leq:"r'\<^sub>2 \<le> r\<^sub>2"
      and wr1:"w\<^sub>1 \<equiv>\<^sub>E r'\<^sub>1" and wr2:"w\<^sub>2 \<equiv>\<^sub>E r'\<^sub>2"
      using a1 a2 unfolding repU_def repL_def apply auto done
      from assms have check1:"\<not> (w\<^sub>1 = NEG_INF \<and> w\<^sub>2 = NEG_INF)" by auto
      from assms have check2:"\<not> (w\<^sub>1 = POS_INF \<and> w\<^sub>2 = POS_INF)" by auto
      have less:"r'\<^sub>1 \<le> r'\<^sub>2" 
        using sless sint_le  less_le_trans neg_numeral_less_numeral not_le of_int_less_iff of_int_numeral less_irrefl 
           less_le_trans not_le check1 check2 repe.simps wr2 wr1
        by(auto simp add: repe.simps POS_INF_def NEG_INF_def)
      show "r\<^sub>1 \<le> r\<^sub>2"
        using r1_leq r2_leq less by auto
    qed
  done

fun wtsemU :: "trm \<Rightarrow> wstate \<Rightarrow>  word * word " ("([_]<>_)" 20)
where "([r \<in> \<R>]<>\<nu>) = (Rep_bword r::word, Rep_bword r)"
| wVarU:"([x \<in> \<V>]<>\<nu>) = (\<nu> (Inl x), \<nu> (Inr x))"
| wPlusU:"([Plus \<theta>\<^sub>1 \<theta>\<^sub>2]<> \<nu>) = 
  (let (l1, u1) = [\<theta>\<^sub>1]<> \<nu> in 
   let (l2, u2) = [\<theta>\<^sub>2]<> \<nu> in
   (pl l1 l2, pu u1 u2))"
| wTimesU:"([(Times \<theta>\<^sub>1 \<theta>\<^sub>2)]<> \<nu>) = 
  (let (l1, u1) = [\<theta>\<^sub>1]<> \<nu> in 
   let (l2, u2) = [\<theta>\<^sub>2]<> \<nu> in
   (tl l1 u1 l2 u2, tu l1 u1 l2 u2))"
| wMaxU:"([(Max \<theta>\<^sub>1 \<theta>\<^sub>2)]<> \<nu>) = 
  (let (l1, u1) = [\<theta>\<^sub>1]<> \<nu> in 
   let (l2, u2) = [\<theta>\<^sub>2]<> \<nu> in
  (wmax l1 l2, wmax u1 u2))"
| wMinU:"([(Min \<theta>\<^sub>1 \<theta>\<^sub>2)]<> \<nu>) = 
  (let (l1, u1) = [\<theta>\<^sub>1]<> \<nu> in 
   let (l2, u2) = [\<theta>\<^sub>2]<> \<nu> in
  (wmin l1 l2, wmin u1 u2))"
| wNegU:"([(Neg \<theta>)]<> \<nu>) = 
  (let (l, u) = [\<theta>]<> \<nu> in
   (wneg u, wneg l))"

inductive wfsem :: " fml \<Rightarrow> wstate \<Rightarrow> bool \<Rightarrow> bool" ("([[_]]_ \<down> _)" 20)
where 
  wLeT:"wle (snd ([\<theta>\<^sub>1]<> \<nu>)) (fst ([\<theta>\<^sub>2]<>\<nu>)) \<Longrightarrow>  ([[(Le \<theta>\<^sub>1 \<theta>\<^sub>2)]]\<nu> \<down> True)"
| wLeF:"wleq (snd ([\<theta>\<^sub>2]<>\<nu>)) (fst ([\<theta>\<^sub>1]<>\<nu>)) \<Longrightarrow>  ([[(Le \<theta>\<^sub>1 \<theta>\<^sub>2)]]\<nu> \<down> False)"
| wLeqT:"wleq (snd ([\<theta>\<^sub>1]<> \<nu>)) (fst ([\<theta>\<^sub>2]<>\<nu>)) \<Longrightarrow>  ([[(Leq \<theta>\<^sub>1 \<theta>\<^sub>2)]]\<nu> \<down> True)"
| wLeqF:"wle (snd ([\<theta>\<^sub>2]<>\<nu>)) (fst ([\<theta>\<^sub>1]<>\<nu>)) \<Longrightarrow>  ([[(Leq \<theta>\<^sub>1 \<theta>\<^sub>2)]]\<nu> \<down> False)"
| wEqualsT:"\<lbrakk>(fst ([\<theta>\<^sub>2]<>\<nu>) = snd ([\<theta>\<^sub>2]<>\<nu>)); (snd ([\<theta>\<^sub>2]<>\<nu>) = snd ([\<theta>\<^sub>1]<>\<nu>)); (snd ([\<theta>\<^sub>1]<>\<nu>) = fst ([\<theta>\<^sub>1]<>\<nu>)); (fst ([\<theta>\<^sub>2]<>\<nu>) \<noteq> NEG_INF); (fst ([\<theta>\<^sub>2]<>\<nu>) \<noteq> POS_INF)\<rbrakk> \<Longrightarrow> ([[Equals \<theta>\<^sub>1 \<theta>\<^sub>2]] \<nu> \<down> True)"
| wEqualsF1:"wle (snd ([\<theta>\<^sub>1]<> \<nu>)) (fst ([\<theta>\<^sub>2]<>\<nu>)) \<Longrightarrow>  ([[Equals \<theta>\<^sub>1 \<theta>\<^sub>2]] \<nu> \<down> False)"
| wEqualsF2:"wle (snd ([\<theta>\<^sub>2]<> \<nu>)) (fst ([\<theta>\<^sub>1]<>\<nu>)) \<Longrightarrow>  ([[Equals \<theta>\<^sub>1 \<theta>\<^sub>2]] \<nu> \<down> False)"
| wAndT:"\<lbrakk>[[\<phi>]]\<nu> \<down> True; [[\<psi>]]\<nu> \<down> True\<rbrakk> \<Longrightarrow> ([[And \<phi> \<psi>]]\<nu> \<down> True)"
| wAndF1:"[[\<phi>]]\<nu> \<down> False \<Longrightarrow> ([[And \<phi> \<psi>]]\<nu> \<down> False)"
| wAndF2:"[[\<psi>]]\<nu> \<down> False \<Longrightarrow> ([[And \<phi> \<psi>]]\<nu> \<down> False)"
| wOrT1:"([[\<phi>]]\<nu> \<down> True) \<Longrightarrow> ([[Or \<phi> \<psi>]]\<nu> \<down> True)"
| wOrT2:"([[\<psi>]]\<nu> \<down> True) \<Longrightarrow> ([[Or \<phi> \<psi>]]\<nu> \<down> True)"
| wOrF:"\<lbrakk>[[\<phi>]]\<nu> \<down> False; [[\<psi>]]\<nu> \<down> False\<rbrakk> \<Longrightarrow> ([[And \<phi> \<psi>]]\<nu> \<down> False)"
| wNotT:"([[\<phi>]]\<nu> \<down> False) \<Longrightarrow> ([[Not \<phi>]]\<nu> \<down> True)"
| wNotF:"([[\<phi>]]\<nu> \<down> True) \<Longrightarrow> ([[Not \<phi>]]\<nu> \<down> False)"

inductive_simps
    wfsem_Gr_simps[simp]: "([[\<theta>\<^sub>1 < \<theta>\<^sub>2]]\<nu> \<down> b)"
and wfsem_And_simps[simp]: "([[\<phi> & \<psi>]]\<nu> \<down> b)"
and wfsem_Or_simps[simp]: "([[Or \<phi> \<psi>]]\<nu> \<down> b)"
and wfsem_Not_simps[simp]: "([[\<not>\<phi>]]\<nu> \<down> b)"
and wfsem_Equals_simps[simp]: "([[Equals \<theta>\<^sub>1 \<theta>\<^sub>2]]\<nu> \<down> b)"

inductive wpsem :: " hp \<Rightarrow> wstate \<Rightarrow> wstate \<Rightarrow> bool" ("([[_]]_ \<down> _)" 20)
where
  wTest:"([[\<phi>]]\<nu> \<down> True) \<Longrightarrow> \<nu> = \<omega> \<Longrightarrow> ([[? \<phi>]] \<nu> \<down> \<omega>)"
| wSeq:"([[\<alpha>]]\<nu> \<down> \<mu>) \<Longrightarrow> ([[\<beta>]] \<mu> \<down> \<omega>) \<Longrightarrow> ([[\<alpha>; \<beta>]] \<nu> \<down> \<omega>)"
| wAssign:"\<omega> = ((\<nu> ((Inr x) := snd([\<theta>]<>\<nu>))) ((Inl x) := fst([\<theta>]<>\<nu>))) \<Longrightarrow> ([[x <- \<theta>]] \<nu> \<down> \<omega>)"
| wChoice1[simp]:"([[\<alpha>]]\<nu> \<down> \<omega>) \<Longrightarrow> ([[Choice \<alpha> \<beta>]]\<nu> \<down> \<omega>)"
| wChoice2[simp]:"([[\<beta>]]\<nu> \<down> \<omega>) \<Longrightarrow> ([[Choice \<alpha> \<beta>]]\<nu> \<down> \<omega>)"

inductive_simps
    wpsem_Test_simps[simp]: "([[? \<phi>]]\<nu> \<down> b)"
and wpsem_Seq_simps[simp]: "([[\<alpha>; \<beta>]]\<nu> \<down> b)"
and wpsem_Assign_simps[simp]: "([[x <- \<theta>]]\<nu> \<down> b)"
and wpsem_Choice_simps[simp]: "([[Choice \<alpha> \<beta>]]\<nu> \<down> b)"

inductive represents_state::"wstate \<Rightarrow> rstate \<Rightarrow> bool" (infix "REP" 10)
where REPI:"(\<And>x. (\<nu> (Inl x) \<equiv>\<^sub>L \<nu>' x) \<and> (\<nu> (Inr x) \<equiv>\<^sub>U \<nu>' x)) \<Longrightarrow> (\<nu> REP \<nu>')"

lemmas real_max_mono =  Lattices.linorder_class.max.mono  
lemmas real_minus_le_minus = Groups.ordered_ab_group_add_class.neg_le_iff_le

inductive_simps repstate_simps:"\<nu> REP \<nu>'"

lemma trm_sound:"([\<theta>]\<nu>' \<down> r) \<Longrightarrow> (\<nu> REP \<nu>') \<Longrightarrow>   ([\<theta>]<>\<nu>) \<equiv>\<^sub>P r"
proof (induction rule: rtsem.induct)
 case 1 
   fix w r \<nu>'
   show "Rep_bword w \<equiv>\<^sub>E r \<Longrightarrow> \<nu> REP \<nu>' \<Longrightarrow> [w \<in> \<R>]<>\<nu> \<equiv>\<^sub>P r"
   using pu_lemma tu_lemma wmax_lemma wmin_lemma  wneg_lemma repU_def repL_def repP_def repe.simps rep_simps repstate_simps order_refl wtsemU.simps(1)
 represents_state.cases by auto
next
 case 2
   fix x \<nu>'
   show "\<nu> REP \<nu>' \<Longrightarrow> [x \<in> \<V>]<>\<nu> \<equiv>\<^sub>P \<nu>' x"
   using pu_lemma tu_lemma wmax_lemma wmin_lemma  wneg_lemma repU_def repL_def repP_def repe.simps rep_simps repstate_simps order_refl wtsemU.simps(1)
 represents_state.cases by auto
next
 case 3
   fix \<theta>\<^sub>1 :: trm and \<nu>' r\<^sub>1 and \<theta>\<^sub>2 :: trm and  r\<^sub>2
   assume rep:"\<nu> REP \<nu>'"
   assume eval1:"[\<theta>\<^sub>1]\<nu>' \<down> r\<^sub>1"
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r\<^sub>1)"
   then have IH1:"[\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r\<^sub>1" using rep by auto
   assume eval2:"[\<theta>\<^sub>2]\<nu>' \<down> r\<^sub>2"
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>2)"
   then have IH2:"[\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>2" using rep by auto
   obtain l1 u1 l2 u2 where 
        lu1:"(l1, u1) = ([\<theta>\<^sub>1]<> \<nu>)" 
    and lu2:"(l2, u2) = ([\<theta>\<^sub>2]<> \<nu>)"
    using IH1 IH2 repP_def by auto
   from lu1 and lu2 have
        lu1':"([\<theta>\<^sub>1]<> \<nu>) = (l1, u1)" 
    and lu2':"([\<theta>\<^sub>2]<> \<nu>) = (l2, u2)"
    by auto
  have l1:"l1 \<equiv>\<^sub>L r\<^sub>1" using IH1 lu1 unfolding repP_def by auto
  have u1:"u1 \<equiv>\<^sub>U r\<^sub>1" using IH1 lu1 unfolding repP_def by auto
  have l2:"l2 \<equiv>\<^sub>L r\<^sub>2" using IH2 lu2 unfolding repP_def by auto
  have u2:"u2 \<equiv>\<^sub>U r\<^sub>2" using IH2 lu2 unfolding repP_def by auto
  then have "([(\<theta>\<^sub>1 + \<theta>\<^sub>2)]<>\<nu>) = (pl l1 l2, pu u1 u2)"  
   using lu1' lu2' by auto
  have lBound:"(pl l1 l2 \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2)"
    using l1 l2 pl_lemma by auto
  have uBound:"(pu u1 u2 \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2)"
    using pu_lemma[OF u1 u2] by auto
  have "(pl l1 l2, pu u1 u2) \<equiv>\<^sub>P (r\<^sub>1 + r\<^sub>2)"
    unfolding repP_def Let_def using lBound uBound by auto
  then show"[\<theta>\<^sub>1 + \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>1 + r\<^sub>2"
    using lu1' lu2' by auto
next
 case 4
   fix \<theta>\<^sub>1 :: trm and \<nu>' r\<^sub>1 and \<theta>\<^sub>2 :: trm and r\<^sub>2
   assume eval1:"[\<theta>\<^sub>1]\<nu>' \<down> r\<^sub>1"
   assume eval2:"[\<theta>\<^sub>2]\<nu>' \<down> r\<^sub>2"
   assume rep:"\<nu> REP \<nu>'"
   assume "(\<nu> REP \<nu>' \<Longrightarrow> ([\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r\<^sub>1))"
   then have IH1:"[\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r\<^sub>1" using rep by auto 
   assume "(\<nu> REP \<nu>' \<Longrightarrow> ([\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>2))"
   then have IH2:"[\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>2" using rep by auto
    obtain l1 u1 l2 u2 where 
        lu1:"([\<theta>\<^sub>1]<> \<nu>) = (l1, u1) " 
    and lu2:"([\<theta>\<^sub>2]<> \<nu>) = (l2, u2)"
    using IH1 IH2 repP_def by auto
  have l1:"l1 \<equiv>\<^sub>L r\<^sub>1" using IH1 lu1 unfolding repP_def by auto
  have u1:"u1 \<equiv>\<^sub>U r\<^sub>1" using IH1 lu1 unfolding repP_def by auto
  have l2:"l2 \<equiv>\<^sub>L r\<^sub>2" using IH2 lu2 unfolding repP_def by auto
  have u2:"u2 \<equiv>\<^sub>U r\<^sub>2" using IH2 lu2 unfolding repP_def by auto
  then have "([(\<theta>\<^sub>1 * \<theta>\<^sub>2)]<>\<nu>) = (tl l1 u1 l2 u2, tu l1 u1 l2 u2)"  
   using lu1 lu2 unfolding wTimesU Let_def by auto 
  have lBound:"(tl l1 u1 l2 u2 \<equiv>\<^sub>L r\<^sub>1 * r\<^sub>2)"
    using l1 u1 l2 u2 tl_lemma by auto
  have uBound:"(tu l1 u1 l2 u2 \<equiv>\<^sub>U r\<^sub>1 * r\<^sub>2)"
    using l1 u1 l2 u2 tu_lemma by auto
  have "(tl l1 u1 l2 u2, tu l1 u1 l2 u2) \<equiv>\<^sub>P (r\<^sub>1 * r\<^sub>2)"
    unfolding repP_def Let_def using lBound uBound by auto
  then show "[\<theta>\<^sub>1 * \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>1 * r\<^sub>2"
    using lu1 lu2 by auto
next
 case 5
   fix \<theta>\<^sub>1 :: trm and \<nu>' r\<^sub>1 and \<theta>\<^sub>2 :: trm and  r\<^sub>2
   assume eval1:"([\<theta>\<^sub>1]\<nu>' \<down> r\<^sub>1)"
   assume eval2:"([\<theta>\<^sub>2]\<nu>' \<down> r\<^sub>2)"
   assume rep:"\<nu> REP \<nu>'"
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r\<^sub>1)"
   then have IH1:"[\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r\<^sub>1" using rep by auto
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>2)"
   then have IH2:"[\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>2" using rep by auto
   obtain l1 u1 l2 u2 where 
        lu1:"([\<theta>\<^sub>1]<> \<nu>) = (l1, u1)" 
    and lu2:"([\<theta>\<^sub>2]<> \<nu>) = (l2, u2)"
    using IH1 IH2 repP_def by auto
   from IH1 IH2 
   obtain ub1 ub2 lb1 lb2:: real 
   where urep1:"(ub1 \<ge> r\<^sub>1) \<and> (snd ([\<theta>\<^sub>1]<>\<nu>) \<equiv>\<^sub>E ub1)" 
   and   urep2:"(ub2 \<ge> r\<^sub>2) \<and> (snd ([\<theta>\<^sub>2]<>\<nu>) \<equiv>\<^sub>E ub2)"
   and   lrep1:"(lb1 \<le> r\<^sub>1) \<and> (fst ([\<theta>\<^sub>1]<>\<nu>) \<equiv>\<^sub>E lb1)" 
   and   lrep2:"(lb2 \<le> r\<^sub>2) \<and> (fst ([\<theta>\<^sub>2]<>\<nu>) \<equiv>\<^sub>E lb2)"
     using prod.case_eq_if repP_def  repU_def repL_def by auto
   have lbound:"wmax l1 l2 \<equiv>\<^sub>L max r\<^sub>1 r\<^sub>2"
     by (metis dual_order.trans fst_conv le_cases lrep1 lrep2 lu1 lu2 max_def repL_def wmax.elims)
   have ubound:"wmax u1 u2 \<equiv>\<^sub>U max r\<^sub>1 r\<^sub>2"     
     by (metis real_max_mono lu1 lu2 repU_def snd_conv urep1 urep2 wmax_lemma)
   have "([trm.Max \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu>) = (wmax l1 l2, wmax u1 u2)"
     using lu1 lu2 unfolding wMaxU Let_def 
     by (simp)
   then show "[trm.Max \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P max r\<^sub>1 r\<^sub>2"
    unfolding repP_def
    using lbound ubound lu1 lu2 by auto
next
  case 6
    fix \<theta>\<^sub>1 :: trm and \<nu>' r\<^sub>1 and \<theta>\<^sub>2 :: trm and  r\<^sub>2
   assume eval1:"([\<theta>\<^sub>1]\<nu>' \<down> r\<^sub>1)"
   assume eval2:"([\<theta>\<^sub>2]\<nu>' \<down> r\<^sub>2)"
   assume rep:"\<nu> REP \<nu>'"
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r\<^sub>1)"
   then have IH1:"[\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r\<^sub>1" using rep by auto
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>2)"
   then have IH2:"[\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>2" using rep by auto
   obtain l1 u1 l2 u2 where 
        lu1:"([\<theta>\<^sub>1]<> \<nu>) = (l1, u1)" 
    and lu2:"([\<theta>\<^sub>2]<> \<nu>) = (l2, u2)"
    using IH1 IH2 repP_def by auto
   from IH1 IH2 
   obtain ub1 ub2 lb1 lb2:: real 
   where urep1:"(ub1 \<ge> r\<^sub>1) \<and> (snd ([\<theta>\<^sub>1]<>\<nu>) \<equiv>\<^sub>E ub1)" 
   and   urep2:"(ub2 \<ge> r\<^sub>2) \<and> (snd ([\<theta>\<^sub>2]<>\<nu>) \<equiv>\<^sub>E ub2)"
   and   lrep1:"(lb1 \<le> r\<^sub>1) \<and> (fst ([\<theta>\<^sub>1]<>\<nu>) \<equiv>\<^sub>E lb1)" 
   and   lrep2:"(lb2 \<le> r\<^sub>2) \<and> (fst ([\<theta>\<^sub>2]<>\<nu>) \<equiv>\<^sub>E lb2)"
     using prod.case_eq_if repP_def  repU_def repL_def by auto
   have lbound:"wmin l1 l2 \<equiv>\<^sub>L min r\<^sub>1 r\<^sub>2"
     by (metis fst_conv lrep1 lrep2 lu1 lu2 min.mono repL_def wmin_lemma)
   have ubound:"wmin u1 u2 \<equiv>\<^sub>U min r\<^sub>1 r\<^sub>2"     
     using lu1 lu2 min_le_iff_disj repU_def urep1 urep2 by auto
   have "([trm.Min \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu>) = (wmin l1 l2, wmin u1 u2)"
     using lu1 lu2 unfolding wMaxU Let_def by (simp)
  then show "[trm.Min \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P min r\<^sub>1 r\<^sub>2"
    unfolding repP_def
    using lbound ubound lu1 lu2 by auto
next
  fix \<theta> :: trm and \<nu>' r
  assume eval:"[\<theta>]\<nu>' \<down> r"
  assume rep:"\<nu> REP \<nu>'"
  assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>]<>\<nu> \<equiv>\<^sub>P r)"
  then have IH:"[\<theta>]<>\<nu> \<equiv>\<^sub>P r" using rep by auto
  obtain l1 u1  where 
        lu:"([\<theta>]<> \<nu>) = (l1, u1)" 
    using IH repP_def by auto
  from IH 
  obtain ub lb:: real 
   where urep:"(ub \<ge> r) \<and> (snd ([\<theta>]<>\<nu>) \<equiv>\<^sub>E ub)" 
   and   lrep:"(lb \<le> r) \<and> (fst ([\<theta>]<>\<nu>) \<equiv>\<^sub>E lb)" 
    using prod.case_eq_if repP_def  repU_def repL_def by auto
  have ubound:"((wneg u1) \<equiv>\<^sub>L (uminus r))"
    by (metis real_minus_le_minus lu repL_def snd_conv urep wneg_lemma)
  have lbound:"((wneg l1) \<equiv>\<^sub>U (uminus r))"
    using real_minus_le_minus lu repU_def lrep wneg_lemma
    by (metis fst_conv)
  show "[- \<theta>]<>\<nu> \<equiv>\<^sub>P - r"
    unfolding repP_def Let_def using ubound lbound by (simp add:  lu)
qed

lemma word_rep:"\<And>bw::bword. \<exists>r::real. Rep_bword bw \<equiv>\<^sub>E r"
proof -
  fix bw
  obtain w where weq:"w = Rep_bword bw" by auto
  have negInfCase:"w = NEG_INF \<Longrightarrow> ?thesis bw"
   apply(rule exI[where x="-((2 ^ 31) -1)"])
    using weq by (auto simp add: repe.simps NEG_INF_def)
  have posInfCase:"w = POS_INF \<Longrightarrow> ?thesis bw"
    apply(rule exI[where x="((2 ^ 31) -1)"])
    using weq by (auto simp add: repe.simps POS_INF_def)
  have boundU:"w \<noteq> NEG_INF \<Longrightarrow> w \<noteq> POS_INF \<Longrightarrow> sint (Rep_bword bw) < sint POS_INF"
    using Rep_bword weq unfolding NEG_INF_def POS_INF_def
    by (metis (no_types, lifting) mem_Collect_eq min.absorb_iff2 min_def not_le Word.word_sint.Rep_eqD)
  have boundL:"w \<noteq> NEG_INF \<Longrightarrow> w \<noteq> POS_INF \<Longrightarrow> sint NEG_INF < sint (Rep_bword bw)"
    using Rep_bword weq unfolding NEG_INF_def POS_INF_def
    by (metis (no_types, lifting) mem_Collect_eq min.absorb_iff2 min_def not_le Word.word_sint.Rep_eqD)
  have intCase:"w \<noteq> NEG_INF \<Longrightarrow> w \<noteq> POS_INF \<Longrightarrow> ?thesis bw"
    apply(rule exI[where x=" (real_of_int (sint (Rep_bword bw)))"])
    apply(rule repINT)
    using boundU boundL by(auto)
  then show "?thesis bw"
  apply(cases "w = POS_INF")
  subgoal using posInfCase by auto
  apply(cases "w = NEG_INF")
  subgoal using negInfCase by auto
  using intCase by auto
  qed
    
lemma eval_tot:"(\<exists>r. ([\<theta>::trm]\<nu>' \<down> r))"
  by(induction "\<theta>", auto simp add: word_rep)
  
lemma fml_sound:" ([[\<phi>]]\<nu> \<down> b) \<Longrightarrow> (\<nu> REP \<nu>') \<Longrightarrow> ([\<phi>] \<nu>' \<down> b)"
apply (induction arbitrary: \<nu>' rule: wfsem.induct)
subgoal for t1 v t2 w
  proof -
  assume wle:"wle (snd ([t1]<>v)) (fst ([t2]<>v))"
  assume rep:"v REP w" 
  obtain r\<^sub>1 and r\<^sub>2 where eval1:"[t1]w \<down> r\<^sub>1" and  eval2:"[t2]w \<down> r\<^sub>2"
    using eval_tot[of t1 w] eval_tot[of t2 w] by auto
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 w r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 w r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[t1 < t2]w \<down> True"
    apply(rule rLeT[where r\<^sub>1 = r\<^sub>1, where r\<^sub>2 = r\<^sub>2]) 
    prefer 3
    apply(rule wle_lemma[where w\<^sub>1="snd([t1]<> v)", where w\<^sub>2="fst([t2]<> v)"])
    using rep1 rep2 wle repP_def repL_def repU_def  eval1 eval2 
    by ((simp add: prod.case_eq_if| blast)+)
  qed
subgoal for t2 v t1 v'
  proof -
  assume "wleq (snd ([t2]<>v)) (fst ([t1]<>v))"
  assume rep:"v REP v'"
  obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] by auto
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[t1 < t2]v' \<down> False"
  using wleq_lemma eval1 eval2 rep1 rep2 unfolding repP_def Let_def
  using  wle_lemma rLeF 
  using \<open>wleq (snd ([t2]<>v)) (fst ([t1]<>v))\<close> prod.case_eq_if by auto 
  qed
subgoal for t1 v t2 v'
proof -
  assume "wleq (snd ([t1]<>v)) (fst ([t2]<>v))"
  assume rep:"v REP v'"
  obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] by auto
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[Leq t1 t2]v' \<down> True"
  using wleq_lemma eval1 eval2 rep1 rep2 unfolding repP_def Let_def
  using  wle_lemma rLeF 
   prod.case_eq_if  \<open>wleq (snd ([t1]<>v)) (fst ([t2]<>v))\<close> rLeqT by auto
  qed
subgoal  for t2 v t1 v'
proof -
  assume "wle (snd ([t2]<>v)) (fst ([t1]<>v))"
  assume rep:"v REP v'"
  obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] by auto
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[Leq t1 t2]v' \<down> False"
  using wleq_lemma eval1 eval2 rep1 rep2 unfolding repP_def Let_def
  using  wle_lemma rLeF  prod.case_eq_if \<open>wle (snd ([t2]<>v)) (fst ([t1]<>v))\<close> rLeqF by auto
  qed
subgoal for t2 v t1 v'
proof -
let ?x = "fst ([t2]<>v)"
assume eq1:"fst ([t2]<>v) = snd ([t2]<>v)"
assume eq2:"snd ([t2]<>v) = snd ([t1]<>v)"
assume eq3:"snd ([t1]<>v) = fst ([t1]<>v)"
assume rep:"v REP v'"  
assume neq1:"?x \<noteq> NEG_INF"
assume neq2:"?x \<noteq> POS_INF"
obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] by auto
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[Equals t1 t2]v' \<down> True"
  using eq1 eq2 eq3 apply auto
  apply(rule exI[where x= "r\<^sub>1"])
  using eq1 eq2 eq3 eval1 eval2 rep1 rep2 unfolding repP_def Let_def repL_def repU_def repe.simps
  using neq1 neq2 by (auto simp add: POS_INF_def NEG_INF_def)
qed
subgoal for t1 v t2 v'
proof -
assume wle:"wle (snd ([t1]<>v)) (fst ([t2]<>v))"
assume rep:"v REP v'"
obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] by auto
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
show "[Equals t1 t2]v' \<down> False"
  using wleq_lemma eval1 eval2 rep1 rep2 unfolding repP_def Let_def
  using  wle_lemma rLeF  prod.case_eq_if wle 
  by (metis (no_types, lifting) less_irrefl rEqualsF) 
qed
subgoal for t2 v t1 v'
proof -
  assume wle:"wle (snd ([t2]<>v)) (fst ([t1]<>v))"
  assume rep:"v REP v'"
  obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] by auto
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[Equals t1 t2]v' \<down> False"
    using wleq_lemma eval1 eval2 rep1 rep2  wle_lemma rLeF  prod.case_eq_if wle
    unfolding repP_def Let_def
    by (metis (no_types, lifting) less_irrefl rEqualsF)
  qed
by auto

lemma rep_upd:"\<omega> = (\<nu>(Inr x := snd([\<theta>]<>\<nu>)))(Inl x := fst([\<theta>]<>\<nu>)) \<Longrightarrow> \<nu> REP \<nu>' \<Longrightarrow> ([\<theta>::trm]\<nu>' \<down> r) \<Longrightarrow> \<omega> REP \<nu>'(x := r)"
  apply(rule REPI)
  using trm_sound  represents_state.cases 
  by (simp add: prod.case_eq_if repP_def repstate_simps) 
  
(* TODO: Could also prove extra lemma and show that \<nu> REP \<nu>' always holds for some \<nu>' *)
theorem fixed_point_sound:
"([[\<alpha>::hp]] \<nu> \<down> \<omega>) \<Longrightarrow> \<nu> REP \<nu>' \<Longrightarrow> (\<exists>\<omega>'. (\<omega> REP \<omega>') \<and> ([\<alpha>::hp] \<nu>' \<down> \<omega>'))"
proof (induction arbitrary: \<nu>' rule: wpsem.induct)
  case (wTest \<phi> \<nu> \<omega> \<nu>') 
    assume sem:"[[\<phi>]]\<nu> \<down> True"
    and eq:"\<nu> = \<omega>"
    and rep:"\<nu> REP \<nu>'"
    show ?case 
      apply(rule exI[where x=\<nu>'])
      using sem rep by (auto simp add: eq fml_sound rep)
next
  case (wSeq \<alpha> \<nu> \<mu> \<beta> \<omega> \<nu>') then show ?case by (simp, blast)
next
  case (wAssign \<omega> \<nu> x \<theta> \<nu>') 
    assume eq:"\<omega> = \<nu>(Inr x := snd ([\<theta>]<>\<nu>), Inl x := fst ([\<theta>]<>\<nu>))"
    and rep:"\<nu> REP \<nu>'"
    obtain r::real where eval:"([\<theta>::trm]\<nu>' \<down> r)" using eval_tot by auto
    show ?case 
      apply(rule exI[where x="\<nu>'(x := r)"])
      apply(rule conjI)
      apply(rule rep_upd[OF eq rep eval])
      apply auto
      apply(rule exI[where x= r])
      by (auto simp add: eval)
next case (wChoice1 a v w b v') then show ?case by auto
next case (wChoice2 a v w b v') then show ?case by auto
qed


code_pred "wfsem".  

export_code wfsem in SML




end