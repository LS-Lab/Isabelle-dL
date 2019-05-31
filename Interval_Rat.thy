theory Interval_Rat
imports 
  Complex_Main
  "./Syntax"
begin

(*datatype num =
   POS_INF
 | NEG_INF
 | RAT rat*)
type_synonym num = rat

type_synonym rstate = "ident \<Rightarrow> real"
type_synonym nstate = "(ident + ident) \<Rightarrow> num"



named_theorems rep_simps "Simplifications for representation functions"

(* Note: 0x80000000 is never used. This way there's no awkward asymmetry but I can still use existing
 * support for 2's complement *)
(*inductive repe ::"word \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>E" 10)
where 
  repPOS_INF:"r \<ge> real_of_int (sint POS_INF) \<Longrightarrow> repe POS_INF r" 
| repNEG_INF:"r \<le> real_of_int (sint NEG_INF) \<Longrightarrow> repe NEG_INF r"
| repINT:    "(sint w) < real_of_int(sint POS_INF) \<Longrightarrow> (sint w) > real_of_int(sint NEG_INF) \<Longrightarrow> repe w (sint w)"*)
(*
inductive_simps 
    repePos_simps[rep_simps]:"repe POS_INF r"
and repeNeg_simps[rep_simps]:"repe NEG_INF r"
and repeInt_simps[rep_simps]:"repe w (sint w)"
*)
definition repU ::"num \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>U" 10)
where "repU num r \<equiv> Ratreal num \<ge> r"

lemma repU_leq:"repU num r \<Longrightarrow> r \<le> Ratreal num "
  unfolding repU_def
  using order_trans by auto

definition repL ::"word \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>L" 10)
where "repL w r \<equiv> Ratreal w  \<le> r "

lemma repL_geq:"repL w r \<Longrightarrow> r' \<ge> r \<Longrightarrow> repL w r'"
  unfolding repL_def
  using order_trans by auto

definition repP ::"word * word \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>P" 10)
where "repP w r \<equiv> let (w1, w2) = w in repL w1 r \<and> repU w2 r" 

inductive rtsem :: "trm \<Rightarrow> rstate \<Rightarrow> real  \<Rightarrow> bool"  ("([_]_ \<down> _)" 10)
  where 
  rtsem_Const:"([Const q]\<nu> \<down> Ratreal q)"
| rtsem_Var:"([Var x]\<nu> \<down> \<nu> x)"
| rtsem_Plus:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> ([Plus \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> (r\<^sub>1 + r\<^sub>2))"
| rtsem_Times:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> ([Times \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> (r\<^sub>1 * r\<^sub>2))"
| rtsem_Div:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> ([Div \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> (r\<^sub>1 / r\<^sub>2))"
| rtsem_Max:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> ([Max \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> (max r\<^sub>1 r\<^sub>2))"
| rtsem_Min:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> ([Min \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> (min r\<^sub>1 r\<^sub>2))"
| rtsem_Abs:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1)\<rbrakk> \<Longrightarrow> ([Abs \<theta>\<^sub>1]\<nu> \<down> (abs r\<^sub>1))"
| rtsem_Neg:"([\<theta>]\<nu> \<down> r) \<Longrightarrow> ([Neg \<theta>]\<nu> \<down> -r)"

inductive_simps 
    rtsem_Const_simps[simp] : "([(Const w)]\<nu> \<down> r)"
and rtsem_Var_simps[simp] : "([Var x]\<nu> \<down> r)"
and rtsem_PlusU_simps[simp] : "([Plus \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> r)"
and rtsem_TimesU_simps[simp] : "([Times \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> r)"
and rtsem_Abs_simps[simp] : "([Abs \<theta>] \<nu> \<down> r)"
and rtsem_Max_simps[simp] : "([Max \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<down> r)"
and rtsem_Min_simps[simp] : "([Min \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<down> r)"
and rtsem_Div_simps[simp] : "([Div \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<down> r)"
and rtsem_Neg_simps[simp] : "([Neg \<theta>] \<nu> \<down> r)"

definition set_less :: "real set \<Rightarrow> real set \<Rightarrow> bool" (infix "<\<^sub>S" 10)
where "set_less A B \<equiv> (\<forall> x y. x \<in> A \<and> y \<in> B \<longrightarrow> x < y)"

definition set_geq :: "real set \<Rightarrow> real set \<Rightarrow> bool" (infix "\<ge>\<^sub>S" 10)
where "set_geq A B \<equiv> (\<forall> x y. x \<in> A \<and> y \<in> B \<longrightarrow> x \<ge> y)"

inductive rfsem :: "formula \<Rightarrow> rstate \<Rightarrow> bool \<Rightarrow> bool" ("([_]_) \<downharpoonright> _" 20)
where 
  rLeT:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 < r\<^sub>2 \<Longrightarrow> ([Le \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> True)"
| rLeF:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 \<ge> r\<^sub>2 \<Longrightarrow> ([Le \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> False)"
| rLeqT:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 \<le> r\<^sub>2 \<Longrightarrow> ([Leq \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> True)"
| rLeqF:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 > r\<^sub>2 \<Longrightarrow> ([Leq \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> False)"
| rEqualsT:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 = r\<^sub>2 \<Longrightarrow> ([Equals \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> True)"
| rEqualsF:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r\<^sub>1); ([\<theta>\<^sub>2]\<nu> \<down> r\<^sub>2)\<rbrakk> \<Longrightarrow> r\<^sub>1 \<noteq> r\<^sub>2 \<Longrightarrow> ([Equals \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> False)"
| rAndT:"\<lbrakk>([\<phi>]\<nu> \<downharpoonright> True); ([\<psi>]\<nu> \<downharpoonright> True)\<rbrakk> \<Longrightarrow> ([And \<phi> \<psi>]\<nu> \<downharpoonright> True)"
| rAndF1:"([\<phi>]\<nu> \<downharpoonright> False) \<Longrightarrow> ([And \<phi> \<psi>]\<nu> \<downharpoonright> False)"
| rAndF2:"([\<psi>]\<nu> \<downharpoonright> False) \<Longrightarrow> ([And \<phi> \<psi>]\<nu> \<downharpoonright> False)"
| rOrT1:"([\<phi>]\<nu> \<downharpoonright> True) \<Longrightarrow> ([Or \<phi> \<psi>]\<nu> \<downharpoonright> True)"
| rOrT2:"([\<psi>]\<nu> \<downharpoonright> True) \<Longrightarrow> ([Or \<phi> \<psi>]\<nu> \<downharpoonright> True)"
| rOrF:"\<lbrakk>([\<phi>]\<nu> \<downharpoonright> False) ;([\<psi>]\<nu> \<downharpoonright> False)\<rbrakk> \<Longrightarrow> ([And \<phi> \<psi>]\<nu> \<downharpoonright> False)"
| rNotT:"([\<phi>]\<nu> \<downharpoonright> False) \<Longrightarrow> ([(Not \<phi>)]\<nu> \<downharpoonright> True)"
| rNotF:"([\<phi>]\<nu> \<downharpoonright> True) \<Longrightarrow> ([(Not \<phi>)]\<nu> \<downharpoonright> False)"

inductive_simps
    rfsem_Gr_simps[simp]: "([Le \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<downharpoonright> b)"
and rfsem_Leq_simps[simp]: "([Leq \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<downharpoonright> b)"
and rfsem_Equals_simps[simp]: "([Equals \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<downharpoonright> b)"
and rfsem_And_simps[simp]: "([And \<phi>  \<psi>]\<nu> \<downharpoonright> b)"
and rfsem_Or_simps[simp]: "([(Or \<phi> \<psi>)]\<nu> \<downharpoonright> b)"
and rfsem_Not_simps[simp]: "([Not \<phi>]\<nu> \<downharpoonright> b)"

inductive rpsem :: "hp \<Rightarrow> rstate \<Rightarrow>  rstate \<Rightarrow> bool" ("([_]_) \<downharpoonleft> _" 20)
where
  rTest[simp]:"\<lbrakk>([\<phi>]\<nu> \<downharpoonright> True); \<nu> = \<omega>\<rbrakk> \<Longrightarrow> ([? \<phi>]\<nu> \<downharpoonleft> \<omega>)"
| rSeq[simp]:"\<lbrakk>([\<alpha>]\<nu> \<downharpoonleft> \<mu>); ([\<beta>]\<mu> \<downharpoonleft> \<omega>)\<rbrakk> \<Longrightarrow> ([\<alpha>;; \<beta>]\<nu> \<downharpoonleft> \<omega>)"
| rAssign[simp]:"\<lbrakk>([\<theta>]\<nu> \<down> r); \<omega> = (\<nu> (x := r))\<rbrakk> \<Longrightarrow> ([Assign x \<theta>]\<nu> \<downharpoonleft> \<omega>)"
| rChoice1[simp]:"([\<alpha>]\<nu> \<downharpoonleft> \<omega>) \<Longrightarrow> ([Choice \<alpha> \<beta>]\<nu> \<downharpoonleft> \<omega>)"
| rChoice2[simp]:"([\<beta>]\<nu> \<downharpoonleft> \<omega>) \<Longrightarrow> ([Choice \<alpha> \<beta>]\<nu> \<downharpoonleft> \<omega>)"

inductive_simps
    rpsem_Test_simps[simp]: "([? \<phi>]\<nu> \<downharpoonleft> b)"
and rpsem_Seq_simps[simp]: "([\<alpha>;; \<beta>]\<nu> \<downharpoonleft> b)"
and rpsem_Assign_simps[simp]: "([Assign x \<theta>]\<nu> \<downharpoonleft> b)"
and rpsem_Choice_simps[simp]: "([Choice \<alpha> \<beta>]\<nu> \<downharpoonleft> b)"


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



fun pu :: "word \<Rightarrow> word \<Rightarrow> word"
where "pu w1 w2 = w1 + w2"

(*
quotient_type real = "nat \<Rightarrow> rat" / partial: realrel
  morphisms rep_real Real
  by (rule part_equivp_realrel)
*)
lemma pu_lemma:
  assumes up1:"w\<^sub>1 \<equiv>\<^sub>U (r\<^sub>1::real)"
  assumes up2:"w\<^sub>2 \<equiv>\<^sub>U (r\<^sub>2::real)"
  shows   "pu w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>U (r\<^sub>1 + r\<^sub>2)"
proof -
  have hom:"\<And>x y.  (real_of_rat x \<le> real_of_rat y) = (x \<le> y)"
    using real_less_eq_code by auto
  have plus:"Real.Real (\<lambda>n. rep_real r\<^sub>1 n) + Real.Real (\<lambda>n. rep_real r\<^sub>2 n)
             = Real.Real (\<lambda>n. rep_real r\<^sub>1 n + rep_real r\<^sub>2 n)"
    apply(rule add_Real)
    by (metis Quotient_real Quotient_rel_rep realrel_def)+
  then have rev:"Real.Real (\<lambda>n. rep_real r\<^sub>1 n + rep_real r\<^sub>2 n) = Real.Real (\<lambda>n. rep_real r\<^sub>1 n) + Real.Real (\<lambda>n. rep_real r\<^sub>2 n)"
    by auto
  from up1 up2 have u1:"r\<^sub>1 \<le> real_of_rat w\<^sub>1"
  and   u2:"r\<^sub>2 \<le> real_of_rat w\<^sub>2" unfolding repU_def by auto
  have cancel:"\<And>x. Real.Real (rep_real x) = x" 
      using Quotient_real Quotient_rel_rep realrel_def Quotient_abs_rep by fastforce
  show ?thesis
    apply(auto simp add: repU_def)
    apply(auto simp add: plus_real_def)
    apply(auto simp add: rev cancel)
    using u1 u2 by (simp add: add_mono_thms_linordered_semiring(1) of_rat_add) 
qed

fun pl :: "word \<Rightarrow> word \<Rightarrow> word"
where "pl w1 w2 = w1 + w2"

lemma pl_lemma:
assumes lo1:"w\<^sub>1 \<equiv>\<^sub>L (r\<^sub>1::real)"
assumes lo2:"w\<^sub>2 \<equiv>\<^sub>L (r\<^sub>2::real)"
shows "pl w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>L (r\<^sub>1 + r\<^sub>2)"
proof -
  have hom:"\<And>x y.  (real_of_rat x \<le> real_of_rat y) = (x \<le> y)"
    using real_less_eq_code by auto
  have plus:"Real.Real (\<lambda>n. rep_real r\<^sub>1 n) + Real.Real (\<lambda>n. rep_real r\<^sub>2 n)
             = Real.Real (\<lambda>n. rep_real r\<^sub>1 n + rep_real r\<^sub>2 n)"
    apply(rule add_Real)
    by (metis Quotient_real Quotient_rel_rep realrel_def)+
  then have rev:"Real.Real (\<lambda>n. rep_real r\<^sub>1 n + rep_real r\<^sub>2 n) = Real.Real (\<lambda>n. rep_real r\<^sub>1 n) + Real.Real (\<lambda>n. rep_real r\<^sub>2 n)"
    by auto
  from lo1 lo2 have l1:"real_of_rat w\<^sub>1 \<le> r\<^sub>1"
  and   l2:"real_of_rat w\<^sub>2 \<le> r\<^sub>2" unfolding repL_def by auto
  have cancel:"\<And>x. Real.Real (rep_real x) = x" 
      using Quotient_real Quotient_rel_rep realrel_def Quotient_abs_rep by fastforce
  show ?thesis
    apply(auto simp add: repU_def)
    apply(auto simp add: plus_real_def)
    apply(auto simp add: rev cancel)
    using  add_mono_thms_linordered_semiring 
    by (metis lo1 lo2 real_plus_code repL_def)
qed

fun wmax :: "word \<Rightarrow> word \<Rightarrow> word"
where "wmax w\<^sub>1 w\<^sub>2 = (if w\<^sub>1 < w\<^sub>2 then w\<^sub>2 else w\<^sub>1)"

lemma wmax_lemma:
  assumes eq1:"(Ratreal w\<^sub>1 =  r\<^sub>1)"
  assumes eq2:"(Ratreal w\<^sub>2 = r\<^sub>2)"
  shows "Ratreal (wmax w\<^sub>1 w\<^sub>2) = (max r\<^sub>1 r\<^sub>2)"
proof -
  from eq1 eq2 have e1:"real_of_rat w\<^sub>1 = r\<^sub>1"
  and   e2:"real_of_rat w\<^sub>2 = r\<^sub>2" unfolding repL_def by auto
  have leq_imp:"w\<^sub>1 < w\<^sub>2 \<Longrightarrow> real_of_rat w\<^sub>1 < real_of_rat w\<^sub>2"
    by (simp add: of_rat_less)    
  have nleq_imp:"\<not>(w\<^sub>1 < w\<^sub>2) \<Longrightarrow> \<not>(real_of_rat w\<^sub>1 < real_of_rat w\<^sub>2)" 
    by (simp add: of_rat_less)
  show ?thesis
    apply(auto)
    using e1 e2 leq_imp nleq_imp by linarith+
qed

fun wtimes :: "word \<Rightarrow> word \<Rightarrow> word"
where "wtimes w1 w2 = w1 * w2"
   
lemma wtimes_exact:
assumes eq1:"Ratreal w1 = r1"
assumes eq2:"Ratreal w2 = r2"
shows "Ratreal (wtimes w1 w2) = r1 * r2"
proof -
  from eq1 eq2 have e1:"real_of_rat w1 = r1"
  and   e2:"real_of_rat w2 = r2" unfolding repL_def by auto
  have leq_imp:"w1 < w2 \<Longrightarrow> real_of_rat w1 < real_of_rat w2"
    by (simp add: of_rat_less)    
  have nleq_imp:"\<not>(w1 < w2) \<Longrightarrow> \<not>(real_of_rat w1 < real_of_rat w2)" 
    by (simp add: of_rat_less)
  show ?thesis
    using e1 e2 apply(auto)
    by (simp add: of_rat_mult) 
qed

fun tu :: "word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word"
where "tu w1l w1u w2l w2u = 
 wmax (wmax (wtimes w1l w2l) (wtimes w1u w2l))
      (wmax (wtimes w1l w2u) (wtimes w1u w2u))"

lemma max_repU1:
  assumes up1:"w\<^sub>1 \<equiv>\<^sub>U r\<^sub>1"
  assumes up2:"w\<^sub>2 \<equiv>\<^sub>U r\<^sub>2"
  shows "wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>U r\<^sub>1"
  using wmax_lemma assms repU_def
  using le_max_iff_disj
proof -
  have hom:"\<And>x y.  (real_of_rat x \<le> real_of_rat y) = (x \<le> y)"
    using real_less_eq_code by auto
  from up1 up2 have u1:"r\<^sub>1 \<le> real_of_rat w\<^sub>1"
  and   u2:"r\<^sub>2 \<le> real_of_rat w\<^sub>2" unfolding repU_def by auto
  have cancel:"\<And>x. Real.Real (rep_real x) = x" 
      using Quotient_real Quotient_rel_rep realrel_def Quotient_abs_rep by fastforce
  show ?thesis
    apply(auto simp add: repU_def)
    by (meson less_eq_rat_def of_rat_less_eq order_trans u1)+ 
qed
  
lemma max_repU2:
  assumes up1:"w\<^sub>1 \<equiv>\<^sub>U r\<^sub>1"
  assumes up2:"w\<^sub>2 \<equiv>\<^sub>U r\<^sub>2"
  shows "wmax w\<^sub>1 w\<^sub>2 \<equiv>\<^sub>U r\<^sub>2"
proof -
  have hom:"\<And>x y.  (real_of_rat x \<le> real_of_rat y) = (x \<le> y)"
    using real_less_eq_code by auto
  from up1 up2 have u1:"r\<^sub>1 \<le> real_of_rat w\<^sub>1"
  and   u2:"r\<^sub>2 \<le> real_of_rat w\<^sub>2" unfolding repU_def by auto
  have cancel:"\<And>x. Real.Real (rep_real x) = x" 
      using Quotient_real Quotient_rel_rep realrel_def Quotient_abs_rep by fastforce
  show ?thesis
    apply(auto simp add: repU_def)
    using less_eq_rat_def of_rat_less_eq order_trans u1 u2 apply blast
    using less_eq_rat_def of_rat_less_eq order_trans u1 u2 le_cases order_trans less_eq_rat_def
    by metis
qed
  
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
  and eru1:"Ratreal u\<^sub>1 = ru1" and eru2:"Ratreal u\<^sub>2 = ru2" and erl1:"Ratreal l\<^sub>1 = rl1" and erl2:"Ratreal l\<^sub>2 = rl2"
  using u1 u2 l1 l2 unfolding repU_def repL_def by auto
  have timesuu:"(Ratreal (wtimes u\<^sub>1 u\<^sub>2)::real) = ((ru1 * ru2)::real)"
    using wtimes_exact[OF eru1 eru2] 
    by(auto simp add: of_rat_Real)
  have timesul:"Ratreal (wtimes u\<^sub>1 l\<^sub>2) = ru1 * rl2"
    using wtimes_exact[OF eru1 erl2] by auto
  have timeslu:"Ratreal (wtimes l\<^sub>1 u\<^sub>2) = rl1 * ru2"
    using wtimes_exact[OF erl1 eru2] by auto
  have timesll:"Ratreal (wtimes l\<^sub>1 l\<^sub>2) = rl1 * rl2"
    using wtimes_exact[OF erl1 erl2] by auto
  have maxt12:"Ratreal (wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) = max (rl1 * rl2) (ru1 * rl2)"
    by (rule  wmax_lemma[OF timesll timesul])
  have maxt34:"Ratreal (wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2)) = max (rl1 * ru2) (ru1 * ru2)"
    by (rule  wmax_lemma[OF timeslu timesuu])
  have bigMax:"Ratreal (wmax (wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2)))
    = max (max (rl1 * rl2) (ru1 * rl2)) (max (rl1 * ru2) (ru1 * ru2))"
    by (rule wmax_lemma[OF maxt12 maxt34])
  obtain maxt12val :: real where maxU12:"wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2) \<equiv>\<^sub>U max (rl1 * rl2) (ru1 * rl2)"
  using maxt12 unfolding repU_def by auto
  obtain maxt34val :: real where maxU34:"wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2) \<equiv>\<^sub>U max (rl1 * ru2) (ru1 * ru2)"
  using maxt34 unfolding repU_def by auto
  obtain bigMaxU:"wmax (wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2))
    \<equiv>\<^sub>U max (max (rl1 * rl2) (ru1 * rl2)) (max (rl1 * ru2) (ru1 * ru2))"
  using bigMax unfolding repU_def by linarith 
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
  (if w\<^sub>1 < w\<^sub>2 then w\<^sub>1 else w\<^sub>2)"

lemma wmin_lemma:
  assumes eq1:"Ratreal w\<^sub>1 = (r\<^sub>1::real)"
  assumes eq2:"Ratreal w\<^sub>2 = (r\<^sub>2::real)"
  shows "Ratreal (wmin w\<^sub>1 w\<^sub>2) = (min r\<^sub>1 r\<^sub>2)"
proof -
  from eq1 eq2 have e1:"real_of_rat w\<^sub>1 = r\<^sub>1"
  and   e2:"real_of_rat w\<^sub>2 = r\<^sub>2" unfolding repL_def by auto
  have leq_imp:"w\<^sub>1 < w\<^sub>2 \<Longrightarrow> real_of_rat w\<^sub>1 < real_of_rat w\<^sub>2"
    by (simp add: of_rat_less)    
  have nleq_imp:"\<not>(w\<^sub>1 < w\<^sub>2) \<Longrightarrow> \<not>(real_of_rat w\<^sub>1 < real_of_rat w\<^sub>2)" 
    by (simp add: of_rat_less)
  show ?thesis
    apply(auto)
    using e1 e2 leq_imp nleq_imp by linarith+
qed
    
lemma min_repU1:
  assumes "w1 \<equiv>\<^sub>L x"
  assumes "w2 \<equiv>\<^sub>L y"
  shows "wmin w1 w2 \<equiv>\<^sub>L x "
  using wmin_lemma assms repL_def
  by (auto simp add: min_le_iff_disj)

lemma min_repU2:
  assumes "w1 \<equiv>\<^sub>L y"
  assumes "w2 \<equiv>\<^sub>L x"
  shows "wmin w1 w2 \<equiv>\<^sub>L x"
  using wmin_lemma assms repL_def
by (auto simp add: min_le_iff_disj)


fun tl :: "word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word"
where "tl w1l w1u w2l w2u =
  wmin (wmin (wtimes w1l w2l) (wtimes w1u w2l))
       (wmin (wtimes w1l w2u) (wtimes w1u w2u))"

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
  and eru1:"Ratreal u\<^sub>1 = ru1" and eru2:"Ratreal u\<^sub>2 = ru2" and erl1:"Ratreal l\<^sub>1 = rl1" and erl2:"Ratreal l\<^sub>2 = rl2"
  using u1 u2 l1 l2 unfolding repU_def repL_def by auto
  have timesuu:"Ratreal (wtimes u\<^sub>1 u\<^sub>2) = ru1 * ru2"
    using wtimes_exact[OF eru1 eru2] by auto
  have timesul:"Ratreal (wtimes u\<^sub>1 l\<^sub>2) = ru1 * rl2"
    using wtimes_exact[OF eru1 erl2] by auto
  have timeslu:"Ratreal (wtimes l\<^sub>1 u\<^sub>2) = rl1 * ru2"
    using wtimes_exact[OF erl1 eru2] by auto
  have timesll:"Ratreal (wtimes l\<^sub>1 l\<^sub>2) = rl1 * rl2"
    using wtimes_exact[OF erl1 erl2] by auto
  have maxt12:"Ratreal (wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) = min (rl1 * rl2) (ru1 * rl2)"
    by (rule  wmin_lemma[OF timesll timesul])
  have maxt34:"Ratreal (wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2)) = min (rl1 * ru2) (ru1 * ru2)"
    by (rule  wmin_lemma[OF timeslu timesuu])
  have bigMax:"Ratreal (wmin (wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2)))
    = min (min(rl1 * rl2) (ru1 * rl2)) (min (rl1 * ru2) (ru1 * ru2))"
    by (rule wmin_lemma[OF maxt12 maxt34])
  obtain maxt12val :: real where maxU12:"wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2) \<equiv>\<^sub>L min (rl1 * rl2) (ru1 * rl2)"
  using maxt12 unfolding repL_def by auto
  obtain maxt34val :: real where maxU34:"wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2) \<equiv>\<^sub>L min (rl1 * ru2) (ru1 * ru2)"
  using maxt34 unfolding repL_def by auto
  obtain bigMaxU:"wmin (wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2))
    \<equiv>\<^sub>L min (min (rl1 * rl2) (ru1 * rl2)) (min (rl1 * ru2) (ru1 * ru2))"
  using bigMax unfolding repL_def by linarith
        
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
          using mult_left_mono_neg by blast
        have g2:"rl1 * r\<^sub>2 \<le> r\<^sub>1 * r\<^sub>2"
          using r1 r2 bounds grl1 grl2 gru1 gru2 mult_le_0_iff mult_le_cancel_right by fastforce
        from g1 and g2
        have up:"rl1 * ru2 \<le> r\<^sub>1 * r\<^sub>2" by auto
        show ?thesis
          using  Ratreal_def of_rat_less repL_def timeslu up wtimes.elims
          by (smt \<open>\<And>thesis. (wmin (wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2)) \<equiv>\<^sub>L min (min (rl1 * rl2) (ru1 * rl2)) (min (rl1 * ru2) (ru1 * ru2)) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> tl.elims)
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
          by (simp add: mult_left_mono)
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
          using bigMaxU repL_def up by auto 
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
        by (smt repL_def tl.simps) 
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
      by (metis mult_right_mono_neg)
    from g1 and g2
    have up:"ru1 * ru2 \<le> r\<^sub>1 * r\<^sub>2"
      by auto
    show ?thesis
      using up maxU12 maxU34 bigMaxU 
      wmin.elims min_repU2 min_repU1 
      min.coboundedI1 min.commute maxt34
      by (smt repL_def tl.simps) 
      
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


fun wneg :: "word \<Rightarrow> word"
where "wneg w = 
  (-w)"

lemma wneg_lemma:
  assumes eq:"Ratreal w = (r::real)"
  shows "Ratreal (wneg w) = -r"
  apply (auto simp add: eq )
  using eq of_rat_minus by auto
  

fun wle :: "word \<Rightarrow> word \<Rightarrow> bool"
where "wle w\<^sub>1 w\<^sub>2 = (w\<^sub>1 <  w\<^sub>2)"

lemma wle_lemma:"w\<^sub>1 \<equiv>\<^sub>U (r\<^sub>1::real) \<Longrightarrow> w\<^sub>2 \<equiv>\<^sub>L r\<^sub>2 \<Longrightarrow> wle w\<^sub>1 w\<^sub>2 \<Longrightarrow> r\<^sub>1 < r\<^sub>2"
  unfolding repU_def repL_def
  by (smt real_less_code wle.elims(2))
  

fun wleq :: "word \<Rightarrow> word \<Rightarrow> bool"
where "wleq w\<^sub>1 w\<^sub>2 = ( w\<^sub>1 \<le> w\<^sub>2)"

lemma wleq_lemma:"w\<^sub>1 \<equiv>\<^sub>U (r\<^sub>1::real) \<Longrightarrow> w\<^sub>2 \<equiv>\<^sub>L r\<^sub>2 \<Longrightarrow> wleq w\<^sub>1 w\<^sub>2 \<Longrightarrow> r\<^sub>1 \<le> r\<^sub>2"
  unfolding wleq.simps
  using real_less_eq_code repL_def repU_leq by force
  

(*fun wdiv:: "word \<Rightarrow> word \<Rightarrow> word"
  where "wdiv w1 w2 = 
 (undefined )
"*)

fun divfloor :: "word \<Rightarrow> word \<Rightarrow> word"
  where "divfloor w1 w2 =  w1 / w2"

(**)
fun divceil :: "word \<Rightarrow> word \<Rightarrow> word"
  where "divceil w1 w2 = w1 div w2" 

fun wabs :: "word \<Rightarrow> word"
  where "wabs l1 = (wmax l1 (wneg l1))"
(* "hopeful" table that might not work
  let x = n or +-inf, y != 0 = m or +-inf 
Then
up(x/y) =
     |  -inf  |  -   |  +  |  +inf
--------------------------------------
-inf | +inf   | +inf |min/m|  0
--------------------------------------
  -  |  1     | n/m  | n/m |  0      
--------------------------------------
  0  |  0     |  0   |  0  |  0      
--------------------------------------
  +  |  0     | n/m  | n/m |  1      
--------------------------------------
+inf |  0     |max/m |max/m|  1      

*)
fun divu :: "word \<Rightarrow> word \<Rightarrow> word"
  where "divu w1 w2 = 
(divceil w1 w2)"


(* "hopeful" table that might not work
  let x = n or +-inf, y != 0 = m or +-inf 
Then
down(x/y) =
     |  -inf  |  -    |   +   |  +inf
--------------------------------------
-inf | 0      | min/m | -inf  | -inf  
--------------------------------------
  -  | 0      | n/m   |  n/m  | -1    
--------------------------------------
  0  | 0      | 0     | 0     | 0       
--------------------------------------
  +  | -1     | n/m   | n/m   | 0       
--------------------------------------
+inf | -inf   | -inf  | max/m | 0       
*)
fun divl :: "word \<Rightarrow> word \<Rightarrow> word"
  where "divl w1 w2 = 
( divfloor w1 w2)"

lemma divl_lemma:
  assumes "Ratreal w1 = r1"
  assumes "Ratreal w2 = r2"
  assumes "r2 \<noteq> 0"
  shows "divl w1 w2 \<equiv>\<^sub>L (r1/r2)"
proof -
  show ?thesis
    using assms(1) assms(2) real_divide_code repL_def by auto 
qed

lemma divu_lemma:
  assumes "Ratreal w1 = r1"
  assumes "Ratreal w2 = r2"
  assumes "r2 \<noteq> 0"
  shows "divu w1 w2 \<equiv>\<^sub>U (r1/r2)"
proof -
  show ?thesis
    using assms(1) assms(2) real_divide_code repU_def by auto 
qed


(* "conservative" table, more likely to work
  let x = n or +-inf, y != 0 = m or +-inf 
Then
up(x/y) =
     |  -inf  |  -   |  +  |  +inf
--------------------------------------
-inf | +inf   | +inf | +inf|  +inf
--------------------------------------
  -  |  1     | n/m  | |n| |  |n|    
--------------------------------------
  0  |  0     |  0   |  0  |  0      
--------------------------------------
  +  |  0     |  0   | |n| |  |n|    
--------------------------------------
+inf | +inf   | +inf |+inf | +inf    

*)

fun divuCon :: "word \<Rightarrow> word \<Rightarrow> word"
where "divuCon w1 w2 =
 (if (w1 = POS_INF \<or> w1 = NEG_INF) then POS_INF
 else if w1 = 0 then 0
 else if wleq 0 w2  then wabs w1
 else if wleq 0 w1  then 0
 else if w2 = NEG_INF then 1
 else w1 div w2)"

(* 0/u2 *)(* 0/l2 *)
fun divU :: "word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> (word * word)"
where "divU l1 u1 l2 u2 =
  (if (wleq l2 0 \<and> wleq 0 u2) then
    (NEG_INF, POS_INF)
else if wle 0 l2  then (* top half*)
  (if wleq l1 0 \<and> wleq 0 u1 then (* top-center*)
    (wmin (divl l1 l2) 0,  
     wmax (divu u1 l2) 0)
   else if wle u1  0 then (* top-left *)
     (divl l1 l2, divu u1 u2)
   else (* top-right *)
     (divl l1 u2, divu u1 l2))
else (* bottom half *)
  (if wleq l1  0 \<and> wleq 0 u1 then (* bottom-center*)
    (wmin (divl u1 u2) 0 
    ,wmax (divu l1 u2) 0)
  else if wle u1  0 then (* bottom-left *)
    (divl u1 l2, divu l1 u2)
  else (* bottom-right*)
    (divl u1 u2, divu l1 l2)
))"
(*
lemma divU_lemma:
  assumes ul1:"(l1, u1) \<equiv>\<^sub>P r1"
  assumes ul2:"(l2, u2) \<equiv>\<^sub>P r2"
  shows "divU l1 u1 l2 u2 \<equiv>\<^sub>P (r1 / r2)"
proof -
  from ul1 ul2
  have l1:"(l1 \<equiv>\<^sub>L r1)" and u1:"(u1 \<equiv>\<^sub>U r1)"
  and  l2:"(l2 \<equiv>\<^sub>L r2)" and u2:"(u2 \<equiv>\<^sub>U r2)"
    unfolding repP_def by auto
  obtain r1l r1u r2l r2u ::real where 
      l1def:"(r1l \<le> r1)"  "(Ratreal l1 = r1l)" 
 and  u1def:"(r1u \<ge> r1)"  "(Ratreal u1 = r1u)"
 and  l2def:"(r2l \<le> r2)"  "(Ratreal l2 = r2l)"
 and  u2def:"(r2u \<ge> r2)"  "(Ratreal u2 = r2u)"
    using l1 u1 l2 u2 unfolding repL_def repU_def by auto
  have  rep0:" (0::word) \<equiv> 0"
    by(auto)
  have  rep0w:" Ratreal (0::word) = 0"
    using rep0 by auto
  then have  rep0u:"(0::word) \<equiv>\<^sub>U 0"
    using repU_def by auto
  from rep0w have rep0l:"(0::word) \<equiv>\<^sub>L 0"
    using repL_def by auto
  show ?thesis
    sorry
qed*)
(*lemma dl_lemma:
  assumes u1:"u\<^sub>1 \<equiv>\<^sub>U (r\<^sub>1::real)"
  assumes u2:"u\<^sub>2 \<equiv>\<^sub>U (r\<^sub>2::real)"
  assumes l1:"l\<^sub>1 \<equiv>\<^sub>L (r\<^sub>1::real)"
  assumes l2:"l\<^sub>2 \<equiv>\<^sub>L (r\<^sub>2::real)"
  shows "dl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L (r\<^sub>1 / r\<^sub>2)"
  sorry
lemma du_lemma:
  assumes u1:"u\<^sub>1 \<equiv>\<^sub>U (r\<^sub>1::real)"
  assumes u2:"u\<^sub>2 \<equiv>\<^sub>U (r\<^sub>2::real)"
  assumes l1:"l\<^sub>1 \<equiv>\<^sub>L (r\<^sub>1::real)"
  assumes l2:"l\<^sub>2 \<equiv>\<^sub>L (r\<^sub>2::real)"
  shows "du l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U (r\<^sub>1 / r\<^sub>2)"
  sorry

*)

fun wtsemU :: "trm \<Rightarrow> nstate \<Rightarrow>  word * word " ("([_]<>_)" 20)
where "([Const r]<>\<nu>) = (r, r)"
| wVarU:"([Var x]<>\<nu>) = (\<nu> (Inl x), \<nu> (Inr x))"
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
| wDivU:"([(Div \<theta>\<^sub>1 \<theta>\<^sub>2)]<> \<nu>) = 
  (let (l1, u1) = [\<theta>\<^sub>1]<> \<nu> in 
   let (l2, u2) = [\<theta>\<^sub>2]<> \<nu> in
  (divU l1 u1 l2 u2))"
| wNegU:"([(Neg \<theta>)]<> \<nu>) =
  (let (l, u) = [\<theta>]<> \<nu> in
   (wneg u, wneg l))"
| wAbsU:"([(Abs \<theta>\<^sub>1)]<> \<nu>) = 
  (let (l1, u1) = [\<theta>\<^sub>1]<> \<nu> in 
  (wmax l1 (wneg u1), wmax u1 (wneg l1))
 )"
(*  (wmin (wabs l1) (wabs u1), wmax (wabs l1) (wabs u1))*)

inductive wfsem :: "formula \<Rightarrow> nstate \<Rightarrow> bool \<Rightarrow> bool" ("([[_]]_ \<down> _)" 20)
where 
  wLeT:"wle (snd ([\<theta>\<^sub>1]<>\<nu>)) (fst ([\<theta>\<^sub>2]<>\<nu>)) \<Longrightarrow>  ([[(Le \<theta>\<^sub>1 \<theta>\<^sub>2)]]\<nu> \<down> True)"
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
    wfsem_Gr_simps[simp]: "([[Le \<theta>\<^sub>1 \<theta>\<^sub>2]]\<nu> \<down> b)"
and wfsem_And_simps[simp]: "([[And \<phi> \<psi>]]\<nu> \<down> b)"
and wfsem_Or_simps[simp]: "([[Or \<phi> \<psi>]]\<nu> \<down> b)"
and wfsem_Not_simps[simp]: "([[Not \<phi>]]\<nu> \<down> b)"
and wfsem_Equals_simps[simp]: "([[Equals \<theta>\<^sub>1 \<theta>\<^sub>2]]\<nu> \<down> b)"

inductive wpsem :: "hp \<Rightarrow>  nstate \<Rightarrow> nstate \<Rightarrow> bool" ("([[_]]_ \<down> _)" 20)
where
  wTest:"([[\<phi>]]\<nu> \<down> True) \<Longrightarrow> \<nu> = \<omega> \<Longrightarrow> ([[? \<phi>]] \<nu> \<down> \<omega>)"
| wSeq:"([[\<alpha>]]\<nu> \<down> \<mu>) \<Longrightarrow> ([[\<beta>]] \<mu> \<down> \<omega>) \<Longrightarrow> ([[\<alpha>;; \<beta>]] \<nu> \<down> \<omega>)"
| wAssign:"\<omega> = ((\<nu> ((Inr x) := snd([\<theta>]<>\<nu>))) ((Inl x) := fst([\<theta>]<>\<nu>))) \<Longrightarrow> ([[Assign x \<theta>]] \<nu> \<down> \<omega>)"
| wChoice1[simp]:"([[\<alpha>]]\<nu> \<down> \<omega>) \<Longrightarrow> ([[Choice \<alpha> \<beta>]]\<nu> \<down> \<omega>)"
| wChoice2[simp]:"([[\<beta>]]\<nu> \<down> \<omega>) \<Longrightarrow> ([[Choice \<alpha> \<beta>]]\<nu> \<down> \<omega>)"

inductive_simps
    wpsem_Test_simps[simp]: "([[Test \<phi>]]\<nu> \<down> b)"
and wpsem_Seq_simps[simp]: "([[\<alpha>;; \<beta>]]\<nu> \<down> b)"
and wpsem_Assign_simps[simp]: "([[Assign x \<theta>]]\<nu> \<down> b)"
and wpsem_Choice_simps[simp]: "([[Choice \<alpha> \<beta>]]\<nu> \<down> b)"

inductive represents_state::"nstate \<Rightarrow> rstate \<Rightarrow> bool" (infix "REP" 10)
where REPI:"(\<And>x. (\<nu> (Inl x) \<equiv>\<^sub>L \<nu>' x) \<and> (\<nu> (Inr x) \<equiv>\<^sub>U \<nu>' x)) \<Longrightarrow> (\<nu> REP \<nu>')"

lemmas real_max_mono =  Lattices.linorder_class.max.mono  
lemmas real_minus_le_minus = Groups.ordered_ab_group_add_class.neg_le_iff_le

inductive_simps repstate_simps:"\<nu> REP \<nu>'"

lemma trm_sound:
  fixes \<theta>::"trm"
  shows "([\<theta>]\<nu>' \<down> r) \<Longrightarrow> (\<nu> REP \<nu>') \<Longrightarrow>   ([\<theta>]<>\<nu>) \<equiv>\<^sub>P r"
proof (induction rule: rtsem.induct)
 case rtsem_Const 
   fix q \<nu>'
   show " \<nu> REP \<nu>' \<Longrightarrow> [Const q]<>\<nu> \<equiv>\<^sub>P Ratreal q"
   using pu_lemma tu_lemma wmax_lemma wmin_lemma  wneg_lemma repU_def repL_def repP_def rep_simps repstate_simps order_refl wtsemU.simps(1)
 represents_state.cases by auto
next
 case rtsem_Var
   fix x \<nu>'
   show "\<nu> REP \<nu>' \<Longrightarrow> [Var x]<>\<nu> \<equiv>\<^sub>P \<nu>' x"
     by(auto simp add: case_prod_conv pu_lemma tu_lemma wmax_lemma wmin_lemma  wneg_lemma repU_def repL_def repP_def rep_simps repstate_simps order_refl wtsemU.simps(1)
     represents_state.cases)
next
 case rtsem_Plus
   fix \<theta>\<^sub>1 :: "trm" and \<nu>':: "rstate" and r\<^sub>1 and \<theta>\<^sub>2 :: "trm" and  r\<^sub>2
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
  then have "([(Plus \<theta>\<^sub>1 \<theta>\<^sub>2)]<>\<nu>) = (pl l1 l2, pu u1 u2)"  
   using lu1' lu2' by auto
  have lBound:"(pl l1 l2 \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2)"
    using l1 l2 pl_lemma by auto
  have uBound:"(pu u1 u2 \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2)"
    using pu_lemma[OF u1 u2] by auto
  have "(pl l1 l2, pu u1 u2) \<equiv>\<^sub>P (r\<^sub>1 + r\<^sub>2)"
    unfolding repP_def Let_def using lBound uBound by auto
  then show"[Plus \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>1 + r\<^sub>2"
    using lu1' lu2' by auto
next
 case rtsem_Times
   fix \<theta>\<^sub>1 :: "trm" and \<nu>' r\<^sub>1 and \<theta>\<^sub>2 :: "trm" and r\<^sub>2
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
  then have "([(Times \<theta>\<^sub>1  \<theta>\<^sub>2)]<>\<nu>) = (tl l1 u1 l2 u2, tu l1 u1 l2 u2)"  
   using lu1 lu2 unfolding wTimesU Let_def by auto 
  have lBound:"(tl l1 u1 l2 u2 \<equiv>\<^sub>L r\<^sub>1 * r\<^sub>2)"
    using l1 u1 l2 u2 tl_lemma by auto
  have uBound:"(tu l1 u1 l2 u2 \<equiv>\<^sub>U r\<^sub>1 * r\<^sub>2)"
    using l1 u1 l2 u2 tu_lemma by auto
  have "(tl l1 u1 l2 u2, tu l1 u1 l2 u2) \<equiv>\<^sub>P (r\<^sub>1 * r\<^sub>2)"
    unfolding repP_def Let_def using lBound uBound by auto
  then show "[Times \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>1 * r\<^sub>2"
    using lu1 lu2 by auto
next
 case rtsem_Max
   fix \<theta>\<^sub>1 :: "trm" and \<nu>' r\<^sub>1 and \<theta>\<^sub>2 :: "trm" and  r\<^sub>2
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
   where urep1:"(ub1 \<ge> r\<^sub>1) \<and> Ratreal (snd ([\<theta>\<^sub>1]<>\<nu>)) = ub1" 
   and   urep2:"(ub2 \<ge> r\<^sub>2) \<and> Ratreal (snd ([\<theta>\<^sub>2]<>\<nu>)) = ub2"
   and   lrep1:"(lb1 \<le> r\<^sub>1) \<and> Ratreal (fst ([\<theta>\<^sub>1]<>\<nu>)) = lb1" 
   and   lrep2:"(lb2 \<le> r\<^sub>2) \<and> Ratreal (fst ([\<theta>\<^sub>2]<>\<nu>)) = lb2"
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
  case rtsem_Min
    fix \<theta>\<^sub>1 :: "trm" and \<nu>' r\<^sub>1 and \<theta>\<^sub>2 :: "trm" and  r\<^sub>2
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
   where urep1:"(ub1 \<ge> r\<^sub>1) \<and> Ratreal (snd ([\<theta>\<^sub>1]<>\<nu>)) = ub1" 
   and   urep2:"(ub2 \<ge> r\<^sub>2) \<and> Ratreal (snd ([\<theta>\<^sub>2]<>\<nu>)) = ub2"
   and   lrep1:"(lb1 \<le> r\<^sub>1) \<and> Ratreal (fst ([\<theta>\<^sub>1]<>\<nu>)) = lb1" 
   and   lrep2:"(lb2 \<le> r\<^sub>2) \<and> Ratreal (fst ([\<theta>\<^sub>2]<>\<nu>)) = lb2"
     using prod.case_eq_if repP_def  repU_def repL_def by auto
   have lbound:"wmin l1 l2 \<equiv>\<^sub>L min r\<^sub>1 r\<^sub>2"
     by (metis fst_conv lrep1 lrep2 lu1 lu2 min.mono repL_def wmin_lemma)
   have ubound:"wmin u1 u2 \<equiv>\<^sub>U min r\<^sub>1 r\<^sub>2"     
     using lu1 lu2 min_le_iff_disj repU_def urep1 urep2 by auto
   have "([Min \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu>) = (wmin l1 l2, wmin u1 u2)"
     using lu1 lu2 unfolding wMinU Let_def by auto
  then show "[Min \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P min r\<^sub>1 r\<^sub>2"
    unfolding repP_def
    using lbound ubound lu1 lu2 by auto
next
  case rtsem_Div
   fix \<theta>\<^sub>1 :: "trm" and \<nu>':: "rstate" and r\<^sub>1 and \<theta>\<^sub>2 :: "trm" and  r\<^sub>2
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
  then have "([(Plus \<theta>\<^sub>1 \<theta>\<^sub>2)]<>\<nu>) = (pl l1 l2, pu u1 u2)"  
   using lu1' lu2' by auto
  have lBound:"(pl l1 l2 \<equiv>\<^sub>L r\<^sub>1 + r\<^sub>2)"
    using l1 l2 pl_lemma by auto
  have uBound:"(pu u1 u2 \<equiv>\<^sub>U r\<^sub>1 + r\<^sub>2)"
    using pu_lemma[OF u1 u2] by auto
  have "divU l1 u1 l2 u2 \<equiv>\<^sub>P (r\<^sub>1 / r\<^sub>2)"
    unfolding repP_def Let_def using lBound uBound 
    using IH1 IH2  lu1' lu2' repP_def 
    sorry
  then show"[Div \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r\<^sub>1 / r\<^sub>2"
    using lu1' lu2' by auto
next
  case rtsem_Neg
  fix \<theta> :: "trm" and \<nu>' r
  assume eval:"[\<theta>]\<nu>' \<down> r"
  assume rep:"\<nu> REP \<nu>'"
  assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>]<>\<nu> \<equiv>\<^sub>P r)"
  then have IH:"[\<theta>]<>\<nu> \<equiv>\<^sub>P r" using rep by auto
  obtain l1 u1  where 
        lu:"([\<theta>]<> \<nu>) = (l1, u1)" 
    using IH repP_def by auto
(*  from IH *)
  have rF:"real_of_rat (fst ([\<theta>]<>\<nu>)) \<le> r"
   and rS:"r \<le> real_of_rat (snd ([\<theta>]<>\<nu>))"
    using IH unfolding repP_def repL_def repU_def Let_def prod.case_eq_if Ratreal_def
    by auto
  obtain ub lb:: real    
   where urep:"(ub \<ge> r) \<and> real_of_rat (snd ([\<theta>]<>\<nu>)) = ub" 
   and   lrep:"(lb \<le> r) \<and> real_of_rat (fst ([\<theta>]<>\<nu>)) = lb" 
    using rF rS by auto
  have ubound:"((wneg u1) \<equiv>\<^sub>L (uminus r))"
    using real_minus_le_minus lu repL_def snd_conv urep wneg_lemma
    using IH repP_def repU_leq by auto
  have lbound:"((wneg l1) \<equiv>\<^sub>U (uminus r))"
    using real_minus_le_minus lu repU_def snd_conv lrep wneg_lemma
    using IH repP_def repU_leq
    by (simp add: repL_def) 
  show "[Neg \<theta>]<>\<nu> \<equiv>\<^sub>P - r"
    unfolding repP_def Let_def using ubound lbound lu 
    by (auto simp add:  lu wNegU)
next
  case rtsem_Abs
  fix \<theta> :: "trm" and \<nu>' r
  assume eval:"[\<theta>]\<nu>' \<down> r"
  assume rep:"\<nu> REP \<nu>'"
  assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>]<>\<nu> \<equiv>\<^sub>P r)"
  then have IH:"[\<theta>]<>\<nu> \<equiv>\<^sub>P r" using rep by auto
  obtain l1 u1  where 
        lu:"([\<theta>]<> \<nu>) = (l1, u1)" 
    using IH repP_def by auto
  from IH 
  obtain ub lb:: real 
   where urep:"(ub \<ge> r) \<and> real_of_rat (snd ([\<theta>]<>\<nu>)) = ub" 
   and   lrep:"(lb \<le> r) \<and> real_of_rat (fst ([\<theta>]<>\<nu>)) = lb" 
    using prod.case_eq_if repP_def  repU_def repL_def
    by auto
  have lbound:"wmax l1 (wneg u1) \<equiv>\<^sub>L (abs r)"
    apply(simp only: repL_def)
    using lrep lu repL_def snd_conv   wmax_lemma real_minus_le_minus lu repL_def snd_conv urep wneg_lemma
    using IH repP_def repU_leq by fastforce
  have ubound:"(wmax u1 (wneg l1) \<equiv>\<^sub>U (abs r))"
    apply(simp only: repU_def)
    using lrep lu repL_def snd_conv wmax_lemma real_minus_le_minus lu repL_def snd_conv urep wneg_lemma
    using IH fst_conv repP_def repU_leq by fastforce
  show "[Abs \<theta>]<>\<nu> \<equiv>\<^sub>P abs r"
    using repP_def Let_def ubound lbound lu lu wAbsU 
      by auto
qed

lemma word_rep:"\<And>q::rat. \<exists>r::real. Ratreal q = r"
proof -
  fix bw
  obtain w where weq:"w = Ratreal bw" by auto
  then show "?thesis bw"
    by auto
  qed
    
lemma eval_tot:"dexec \<theta> \<Longrightarrow> (\<exists>r. ([\<theta>::trm]\<nu>' \<down> r))"
proof (induction rule: dexec.induct)
qed (auto simp add: Min_def Neg_def word_rep bword_neg_one_def, blast?)
  
lemma fml_sound:
  fixes \<phi>::"formula" and \<nu>::"nstate"
  shows "(wfsem \<phi> \<nu> b) \<Longrightarrow> fexec \<phi> \<Longrightarrow> (\<nu> REP \<nu>') \<Longrightarrow> (rfsem \<phi> \<nu>'  b)"
  apply (induction arbitrary: \<nu>' rule: wfsem.induct)
subgoal for t1 v t2 w
  proof -
  assume wle:"wle (snd ([t1]<>v)) (fst ([t2]<>v))"
  assume rep:"v REP w" 
  assume fex:"fexec (Le t1 t2)"
  obtain r\<^sub>1 and r\<^sub>2 where eval1:"[t1]w \<down> r\<^sub>1" and  eval2:"[t2]w \<down> r\<^sub>2"
    using eval_tot[of t1 w] eval_tot[of t2 w] fex apply (auto simp add: Le_def)
    by (metis Less_def fexec_And_simps fexec_Geq_simps)
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 w r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 w r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[Le t1 t2]w \<downharpoonright> True"
    apply(rule rLeT[where r\<^sub>1 = r\<^sub>1, where r\<^sub>2 = r\<^sub>2]) 
    prefer 3
    apply(rule wle_lemma[where w\<^sub>1="snd([t1]<> v)", where w\<^sub>2="fst([t2]<> v)"])
    using rep1 rep2 wle repP_def repL_def repU_def  eval1 eval2 
    by ((simp add: prod.case_eq_if| blast)+)
  qed
subgoal for t2 v t1 v'
  proof -
  assume wl:"wleq (snd ([t2]<>v)) (fst ([t1]<>v))"
  assume rep:"v REP v'"
  assume fex:"fexec (Le t1 t2)"
  obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] fex apply (auto simp add: Le_def)
    by (metis Less_def fexec_And_simps fexec_Geq_simps)
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[Le t1 t2]v' \<downharpoonright> False"
    apply(rule rLeF [of t1 v' r\<^sub>1 t2 r\<^sub>2])
    apply(rule eval1)
    apply(rule eval2)
    using wle_lemma wl rep  unfolding repP_def Let_def 
    using rep1 rep2 repP_def wleq_lemma by auto
  qed
subgoal for t1 v t2 v'
proof -
  assume "wleq (snd ([t1]<>v)) (fst ([t2]<>v))"
  assume rep:"v REP v'"
  assume fex:"fexec (Leq t1 t2)"
  obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] fex by (auto simp add: Leq_def Le_def)
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[Leq t1 t2]v' \<downharpoonright> True"
    apply(rule rLeqT)
      apply(rule eval1)
    apply(rule eval2)
  using wleq_lemma eval1 eval2 rep1 rep2 unfolding repP_def Let_def
  using  wle_lemma prod.case_eq_if  \<open>wleq (snd ([t1]<>v)) (fst ([t2]<>v))\<close>
  by auto
  qed
subgoal  for t2 v t1 v'
proof -
  assume "wle (snd ([t2]<>v)) (fst ([t1]<>v))"
  assume rep:"v REP v'"
  assume fex:"fexec (Leq t1 t2)"
  obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] fex by (auto simp add: Leq_def Le_def)
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[Leq t1 t2]v' \<downharpoonright> False"
    apply(rule rLeqF, rule eval1, rule eval2)
  using wleq_lemma eval1 eval2 rep1 rep2 unfolding repP_def Let_def
  using  wle_lemma rLeF  prod.case_eq_if \<open>wle (snd ([t2]<>v)) (fst ([t1]<>v))\<close> rLeqF by auto
  qed
subgoal for t2 v t1 v'
proof -
let ?x = "fst ([t2]<>v)"
 assume fex:"fexec (Equals t1 t2)"
assume eq1:"fst ([t2]<>v) = snd ([t2]<>v)"
assume eq2:"snd ([t2]<>v) = snd ([t1]<>v)"
assume eq3:"snd ([t1]<>v) = fst ([t1]<>v)"
assume rep:"v REP v'"  
assume neq1:"?x \<noteq> NEG_INF"
assume neq2:"?x \<noteq> POS_INF"
obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v']  fex by (auto simp add: Equals_def Leq_def Le_def)
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[Equals t1 t2]v' \<downharpoonright> True"
    apply(rule rEqualsT, rule eval1, rule eval2)
  using eq1 eq2 eq3 eval1 eval2 rep1 rep2 unfolding repP_def Let_def repL_def repU_def 
  using neq1 neq2 by (auto)
qed
subgoal for t1 v t2 v'
proof -
assume wle:"wle (snd ([t1]<>v)) (fst ([t2]<>v))"
assume rep:"v REP v'"
 assume fex:"fexec (Equals t1 t2)"
obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v']  fex by (auto simp add: Equals_def Leq_def Le_def)
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule  trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule  trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
show "[Equals t1 t2]v' \<downharpoonright> False"
    apply(rule rEqualsF, rule eval1, rule eval2)
  using wleq_lemma eval1 eval2 rep1 rep2 unfolding repP_def Let_def
  using  wle_lemma rLeF  prod.case_eq_if wle 
  by (metis (no_types, lifting) less_irrefl rEqualsF) 
qed
subgoal for t2 v t1 v'
proof -
  assume wle:"wle (snd ([t2]<>v)) (fst ([t1]<>v))"
  assume rep:"v REP v'"
 assume fex:"fexec (Equals t1 t2)"
  obtain r\<^sub>1 r\<^sub>2:: real
  where eval1:"(rtsem t1 v' r\<^sub>1)" and  
    eval2:"rtsem t2 v'  r\<^sub>2"
    using eval_tot[of t1 v'] eval_tot[of t2 v']  fex by (auto simp add: Equals_def Leq_def Le_def)
  have rep1:"[t1]<>v \<equiv>\<^sub>P r\<^sub>1" by (rule  trm_sound[of t1 v' r\<^sub>1, where \<nu>=v, OF eval1 rep])
  have rep2:"[t2]<>v \<equiv>\<^sub>P r\<^sub>2" by (rule  trm_sound[of t2 v' r\<^sub>2, where \<nu>=v, OF eval2 rep])
  show "[Equals t1 t2]v' \<downharpoonright> False"
    apply(rule rEqualsF, rule eval1, rule eval2)
    using wleq_lemma eval1 eval2 rep1 rep2  wle_lemma rLeF  prod.case_eq_if wle
    unfolding repP_def Let_def
    by (metis (no_types, lifting) less_irrefl rEqualsF)
  qed
         apply auto
  by (metis Or_def fexec_And_simps fexec_Not_simps)+

lemma rep_upd:"\<omega> = (\<nu>(Inr x := snd([\<theta>]<>\<nu>)))(Inl x := fst([\<theta>]<>\<nu>)) \<Longrightarrow> \<nu> REP \<nu>' \<Longrightarrow> ([\<theta>::trm]\<nu>' \<down> r) \<Longrightarrow> \<omega> REP \<nu>'(x := r)"
  apply(rule REPI)
  apply(rule conjI)
  apply(unfold repL_def)
  using trm_sound  prod.case_eq_if repP_def repstate_simps repL_def 
  (*apply (metis (no_types, lifting) Inl_Inr_False fun_upd_apply sum.inject(1))*)
  apply auto
  apply(unfold repU_def)
  using trm_sound  prod.case_eq_if repP_def repstate_simps repU_def
  using  Inl_Inr_False fun_upd_apply sum.inject(1) sum.inject(2) 
  apply auto
  using surjective_pairing trm_sound
  by metis+
    
(* TODO: Could also prove extra lemma and show that \<nu> REP \<nu>' always holds for some \<nu>' *)
theorem fixed_point_sound:
  fixes \<alpha>::"hp"
  shows "([[\<alpha>]] \<nu> \<down> \<omega>) \<Longrightarrow> hpexec \<alpha> \<Longrightarrow> \<nu> REP \<nu>' \<Longrightarrow> (\<exists>\<omega>'. (\<omega> REP \<omega>') \<and> ([\<alpha>] \<nu>' \<downharpoonleft> \<omega>'))"
proof (induction arbitrary: \<nu>' rule: wpsem.induct)
  case (wTest \<phi> \<nu> \<omega> \<nu>') 
    assume sem:"[[\<phi>]]\<nu> \<down> True"
    and eq:"\<nu> = \<omega>"
    and rep:"\<nu> REP \<nu>'"
    and hpexec:"hpexec (? \<phi>)"
    show ?case 
      apply(rule exI[where x=\<nu>'])
      using sem rep hpexec by (auto simp add: eq fml_sound rep)
next
  case (wSeq \<alpha> \<nu> \<mu> \<beta> \<omega> \<nu>') then show ?case by (simp, blast)
next
  case (wAssign \<omega> \<nu> x \<theta> \<nu>') 
    assume eq:"\<omega> = \<nu>(Inr x := snd ([\<theta>]<>\<nu>), Inl x := fst ([\<theta>]<>\<nu>))"
    and rep:"\<nu> REP \<nu>'"
    and hpexec:"hpexec (x := \<theta>)"
    obtain r::real where eval:"([\<theta>::trm]\<nu>' \<down> r)" using eval_tot hpexec by auto
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




end