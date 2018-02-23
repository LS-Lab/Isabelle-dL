theory "Coincidence" 
imports
  Ordinary_Differential_Equations.ODE_Analysis
  "Ids"
  "Lib"
  "Syntax"
  "Denotational_Semantics"
  "Frechet_Correctness"
  "Static_Semantics"
begin
section \<open>Coincidence Theorems and Corollaries\<close>
text \<open>This section proves coincidence: semantics of terms, odes, formulas and programs depend only
  on the free variables. This is one of the major lemmas for the correctness of uniform substitutions.
  Along the way, we also prove the equivalence between two similar, but different semantics for ODE programs:
  It does not matter whether the semantics of ODE's insist on the existence of a solution that agrees
  with the start state on all variables vs. one that agrees only on the variables that are actually
  relevant to the ODE. This is proven here by simultaneous induction with the coincidence theorem
  for the following reason:
  
  The reason for having two different semantics is that some proofs are easier with one semantics
  and other proofs are easier with the other definition. The coincidence proof is either with the
  more complicated definition, which should not be used as the main definition because it would make
  the specification for the dL semantics significantly larger, effectively increasing the size of
  the trusted core. However, that the proof of equivalence between the semantics using the coincidence
  lemma for formulas. In order to use the coincidence proof in the equivalence proof and the equivalence
  proof in the coincidence proof, they are proved by simultaneous induction.
  \<close>

context ids begin
subsection \<open>Term Coincidence Theorems\<close>               
lemma coincidence_sterm:"Vagree \<nu> \<nu>' (FVT \<theta>) \<Longrightarrow> sterm_sem I  \<theta> (fst \<nu>) = sterm_sem I \<theta> (fst \<nu>')"
  apply(induct "\<theta>") (* 7 subgoals *)
  apply(auto simp add: Vagree_def)
  by (meson rangeI)

lemma coincidence_sterm':"dfree \<theta> \<Longrightarrow>  Vagree \<nu> \<nu>' (FVT \<theta>) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>} \<Longrightarrow> sterm_sem I  \<theta> (fst \<nu>) = sterm_sem J \<theta> (fst \<nu>')"
proof (induction rule: dfree.induct)
  case (dfree_Fun args i)
    then show ?case
    proof (auto)
      from dfree_Fun.IH have free:"(\<And>i. dfree (args i))"
      and IH:"(\<And>i. Vagree \<nu> \<nu>' (FVT (args i)) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT (args i)} \<Longrightarrow> sterm_sem I (args i) (fst \<nu>) = sterm_sem J (args i) (fst \<nu>'))"
      by auto
      from dfree_Fun.prems have VA:"Vagree \<nu> \<nu>' (\<Union>i. FVT (args i))"
      and IA:"Iagree I J {Inl x |x. x = i \<or> (\<exists>xa. x \<in> SIGT (args xa))}" by auto
      from IA have IAorig:"Iagree I J {Inl x |x. x \<in> SIGT (Function i args)}" by auto
      from Iagree_Func[OF IAorig] have eqF:"Functions I i = Functions J i" by auto
      have Vsubs:"\<And>i. FVT (args i) \<subseteq> (\<Union>i. FVT (args i))" by auto
      from VA 
      have VAs:"\<And>i. Vagree \<nu> \<nu>' (FVT (args i))" 
        using agree_sub[OF Vsubs] by auto
      have Isubs:"\<And>j. {Inl x |x. x \<in> SIGT (args j)} \<subseteq> {Inl x |x. x \<in> SIGT (Function i args)}"
        by auto
      from IA
      have IAs:"\<And>i. Iagree I J {Inl x |x. x \<in> SIGT (args i)}"
        using Iagree_sub[OF Isubs] by auto
      show "Functions I i (\<chi> i. sterm_sem I (args i) (fst \<nu>)) = Functions J i (\<chi> i. sterm_sem J (args i) (fst \<nu>'))"
        using IH[OF VAs IAs] eqF by auto
    qed  
next
  case (dfree_Plus \<theta>\<^sub>1 \<theta>\<^sub>2)
  then show ?case 
  proof (auto)
    assume "dfree \<theta>\<^sub>1" "dfree \<theta>\<^sub>2"
      and IH1:"(Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<Longrightarrow> sterm_sem I \<theta>\<^sub>1 (fst \<nu>) = sterm_sem J \<theta>\<^sub>1 (fst \<nu>'))"
      and IH2:"(Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<Longrightarrow> sterm_sem I \<theta>\<^sub>2 (fst \<nu>) = sterm_sem J \<theta>\<^sub>2 (fst \<nu>'))"
      and VA:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1 \<union> FVT \<theta>\<^sub>2)"
      and IA:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1 \<or> x \<in> SIGT \<theta>\<^sub>2}"
    from VA 
    have VAs:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1)" "Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2)"
      unfolding Vagree_def by auto
    have Isubs:"{Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<subseteq> {Inl x |x. x \<in> SIGT (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)}"
      "{Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<subseteq> {Inl x |x. x \<in> SIGT (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)}"
      by auto
    from IA 
    have IAs:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1}" 
      "Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2}"
      using Iagree_sub[OF Isubs(1)] Iagree_sub[OF Isubs(2)] by auto         
    show "sterm_sem I \<theta>\<^sub>1 (fst \<nu>) + sterm_sem I \<theta>\<^sub>2 (fst \<nu>) = sterm_sem J \<theta>\<^sub>1 (fst \<nu>') + sterm_sem J \<theta>\<^sub>2 (fst \<nu>')"
      using IH1[OF VAs(1) IAs(1)] IH2[OF VAs(2) IAs(2)] by auto
  qed
next
  case (dfree_Times \<theta>\<^sub>1 \<theta>\<^sub>2)
  then show ?case 
  proof (auto)
    assume "dfree \<theta>\<^sub>1" "dfree \<theta>\<^sub>2"
      and IH1:"(Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<Longrightarrow> sterm_sem I \<theta>\<^sub>1 (fst \<nu>) = sterm_sem J \<theta>\<^sub>1 (fst \<nu>'))"
      and IH2:"(Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<Longrightarrow> sterm_sem I \<theta>\<^sub>2 (fst \<nu>) = sterm_sem J \<theta>\<^sub>2 (fst \<nu>'))"
      and VA:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1 \<union> FVT \<theta>\<^sub>2)"
      and IA:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1 \<or> x \<in> SIGT \<theta>\<^sub>2}"
    from VA 
    have VAs:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1)" "Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2)"
      unfolding Vagree_def by auto
    have Isubs:"{Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<subseteq> {Inl x |x. x \<in> SIGT (Times \<theta>\<^sub>1 \<theta>\<^sub>2)}"
      "{Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<subseteq> {Inl x |x. x \<in> SIGT (Times \<theta>\<^sub>1 \<theta>\<^sub>2)}"
      by auto
    from IA 
    have IAs:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1}" 
      "Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2}"
      using Iagree_sub[OF Isubs(1)] Iagree_sub[OF Isubs(2)] by auto         
    show "sterm_sem I \<theta>\<^sub>1 (fst \<nu>) * sterm_sem I \<theta>\<^sub>2 (fst \<nu>) = sterm_sem J \<theta>\<^sub>1 (fst \<nu>') * sterm_sem J \<theta>\<^sub>2 (fst \<nu>')"
      using IH1[OF VAs(1) IAs(1)] IH2[OF VAs(2) IAs(2)] by auto
  qed
qed (unfold Vagree_def Iagree_def, auto)

lemma sum_unique_nonzero:
  fixes i::"'sv::finite" and f::"'sv \<Rightarrow> real"
  assumes restZero:"\<And>j. j\<in>(UNIV::'sv set) \<Longrightarrow> j \<noteq> i \<Longrightarrow> f j = 0"
  shows "(\<Sum>j\<in>(UNIV::'sv set). f j) = f i"
proof -
  have "(\<Sum>j\<in>(UNIV::'sv set). f j) = (\<Sum>j\<in>{i}. f j)"
    using restZero by (intro sum.mono_neutral_cong_right) auto
  then show ?thesis
    by simp
qed

lemma  coincidence_frechet :
  fixes I :: "('a::finite, 'b::finite, 'c::finite) interp" and \<nu> :: "'c state" and \<nu>'::"'c state"
  shows "dfree \<theta> \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff \<theta>) \<Longrightarrow> frechet I  \<theta> (fst \<nu>) (snd \<nu>) = frechet I  \<theta> (fst \<nu>') (snd \<nu>')"
proof (induction rule: dfree.induct)
  case dfree_Var then show ?case
    by (auto simp: inner_prod_eq Vagree_def)
next
  case dfree_Const then show ?case
    by auto
next
  case (dfree_Fun args var)
  have free:"(\<And>i. dfree (args i))"
  and IH:"(\<And>i. Vagree \<nu> \<nu>' (FVDiff (args i)) \<Longrightarrow> frechet I (args i) (fst \<nu>) (snd \<nu>) = frechet I (args i) (fst \<nu>') (snd \<nu>'))"
  and agree:"Vagree \<nu> \<nu>' (FVDiff ($f var args))"
    using dfree_Fun.IH dfree_Fun.prems by auto
  have frees:"(\<And>i. dfree (args i))" using free by (auto simp add: rangeI)
  have agrees:"\<And>i. Vagree \<nu> \<nu>' (FVDiff (args i))" using agree agree_func by metis
  have agrees':"\<And>i. Vagree \<nu> \<nu>' (FVT (args i))"
    subgoal for i
      using agrees[of i] FVDiff_sub[of "args i"] unfolding Vagree_def by blast
    done
  have sterms:"\<And>i. sterm_sem I (args i) (fst \<nu>) = sterm_sem I (args i) (fst \<nu>')" 
    by (rule coincidence_sterm[of "\<nu>"  "\<nu>'", OF agrees'])
  have frechets:"\<And>i. frechet I (args i) (fst \<nu>) (snd \<nu>) = frechet I (args i) (fst \<nu>') (snd \<nu>')"  using IH agrees frees rangeI by blast
  show  "?case"
    using agrees sterms frechets by (auto)
next
  case (dfree_Neg t) 
  assume dfree1:"dfree t"
  assume IH1:"(Vagree \<nu> \<nu>' (FVDiff t) \<Longrightarrow> frechet I t (fst \<nu>) (snd \<nu>) = frechet I t (fst \<nu>') (snd \<nu>'))"
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Neg t))"
  have agree1:"Vagree \<nu> \<nu>' (FVDiff t)" using agree agree_neg by (blast)
  have IH1':"(frechet I t (fst \<nu>) (snd \<nu>) = frechet I t (fst \<nu>') (snd \<nu>'))"
    using IH1 agree1 by (auto)
  show "?case"
    by (metis FVT.simps(4) IH1' UnCI Vagree_def coincidence_sterm frechet.simps(3) mem_Collect_eq)
next
  case (dfree_Plus t1 t2) 
  assume dfree1:"dfree t1"
  assume IH1:"(Vagree \<nu> \<nu>' (FVDiff t1) \<Longrightarrow> frechet I t1 (fst \<nu>) (snd \<nu>) = frechet I t1 (fst \<nu>') (snd \<nu>'))"
  assume dfree2:"dfree t2"
  assume IH2:"(Vagree \<nu> \<nu>' (FVDiff t2) \<Longrightarrow> frechet I t2 (fst \<nu>) (snd \<nu>) = frechet I t2 (fst \<nu>') (snd \<nu>'))"
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Plus t1 t2))"
  have agree1:"Vagree \<nu> \<nu>' (FVDiff t1)" using agree agree_plus1 by (blast)
  have agree2:"Vagree \<nu> \<nu>' (FVDiff t2)" using agree agree_plus2 by (blast)
  have IH1':"(frechet I t1 (fst \<nu>) (snd \<nu>) = frechet I t1 (fst \<nu>') (snd \<nu>'))"
    using IH1 agree1 by (auto)
  have IH2':"(frechet I t2 (fst \<nu>) (snd \<nu>) = frechet I t2 (fst \<nu>') (snd \<nu>'))"
    using IH2 agree2 by (auto)
  show "?case"
    by(metis FVT_Plus IH1' IH2' UnCI Vagree_def coincidence_sterm Frechet_Plus mem_Collect_eq)
next
  case (dfree_Times t1 t2) 
  assume dfree1:"dfree t1"
  assume IH1:"(Vagree \<nu> \<nu>' (FVDiff t1) \<Longrightarrow> frechet I t1 (fst \<nu>) (snd \<nu>) = frechet I t1 (fst \<nu>') (snd \<nu>'))"
  assume dfree2:"dfree t2"
  assume IH2:"(Vagree \<nu> \<nu>' (FVDiff t2) \<Longrightarrow> frechet I t2 (fst \<nu>) (snd \<nu>) = frechet I t2 (fst \<nu>') (snd \<nu>'))"
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Times t1 t2))"
  have agree1:"Vagree \<nu> \<nu>' (FVDiff t1)" using agree agree_times1 by blast
  have agree2:"Vagree \<nu> \<nu>' (FVDiff t2)" using agree agree_times2 by blast
  have agree1':"Vagree \<nu> \<nu>' (FVT t1)"
    using agree1 apply(auto simp add: Vagree_def)
     using primify_contains by blast+
  have agree2':"Vagree \<nu> \<nu>' (FVT t2)"
    using agree2 apply(auto simp add: Vagree_def)
     using primify_contains by blast+
  have IH1':"(frechet I t1 (fst \<nu>) (snd \<nu>) = frechet I t1 (fst \<nu>') (snd \<nu>'))"
    using IH1 agree1 by (auto)
  have IH2':"(frechet I t2 (fst \<nu>) (snd \<nu>) = frechet I t2 (fst \<nu>') (snd \<nu>'))"
    using IH2 agree2 by (auto)
  have almost:"Vagree \<nu> \<nu>' (FVT (Times t1 t2)) \<Longrightarrow> frechet I (Times t1 t2) (fst \<nu>) (snd \<nu>) = frechet I (Times t1 t2) (fst \<nu>') (snd \<nu>')"
    by (auto simp add: UnCI Vagree_def agree IH1' IH2' coincidence_sterm[OF agree1', of I] coincidence_sterm[OF agree2', of I])
  show "?case"
    using agree FVDiff_sub almost
    by (metis agree_supset)
qed

lemma  coincidence_frechet' :
  fixes I J :: "('a::finite, 'b::finite, 'c::finite) interp" and \<nu> :: "'c state" and \<nu>'::"'c state"
  shows "dfree \<theta> \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff \<theta>) \<Longrightarrow> Iagree I J {Inl x | x. x \<in> (SIGT \<theta>)} \<Longrightarrow> frechet I  \<theta> (fst \<nu>) (snd \<nu>) = frechet J  \<theta> (fst \<nu>') (snd \<nu>')"
proof (induction rule: dfree.induct)
  case dfree_Var then show ?case
    by (auto simp: inner_prod_eq Vagree_def)
next
  case dfree_Const then show ?case
    by auto
next
  case (dfree_Fun args var)
  have free:"(\<And>i. dfree (args i))"
  and IH:"(\<And>i. Vagree \<nu> \<nu>' (FVDiff (args i)) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT (args i)} \<Longrightarrow> frechet I (args i) (fst \<nu>) (snd \<nu>) = frechet J (args i) (fst \<nu>') (snd \<nu>'))"
  and agree:"Vagree \<nu> \<nu>' (FVDiff ($f var args))"
  and IA:"Iagree I J {Inl x |x. x \<in> SIGT ($f var args)}"
    using dfree_Fun.IH dfree_Fun.prems by auto
  have frees:"(\<And>i. dfree (args i))" using free by (auto simp add: rangeI)
  have agrees:"\<And>i. Vagree \<nu> \<nu>' (FVDiff (args i))" using agree agree_func by metis
  then have agrees':"\<And>i. Vagree \<nu> \<nu>' (FVT (args i))"
    using agrees  FVDiff_sub 
    by (metis agree_sub)
  from Iagree_Func [OF IA ]have fEq:"Functions I var = Functions J var" by auto 
  have subs:"\<And>i.{Inl x |x. x \<in> SIGT (args i)} \<subseteq> {Inl x |x. x \<in> SIGT ($f var args)}"
    by auto
  from IA have IAs:"\<And>i. Iagree I J {Inl x |x. x \<in> SIGT (args i)}"
    using Iagree_sub[OF subs] by auto
  have sterms:"\<And>i. sterm_sem I (args i) (fst \<nu>) = sterm_sem J (args i) (fst \<nu>')"
    subgoal for i
      using frees agrees' coincidence_sterm'[of "args i" \<nu> \<nu>' I J] IAs 
      by (auto)  
    done
  have frechets:"\<And>i. frechet I (args i) (fst \<nu>) (snd \<nu>) = frechet J (args i) (fst \<nu>') (snd \<nu>')"  
    using IH[OF agrees IAs] agrees frees rangeI by blast
  show "?case"
    using agrees agrees' sterms frechets fEq by auto
next
  case (dfree_Neg t1) 
  assume dfree1:"dfree t1"
  assume IH1:"(Vagree \<nu> \<nu>' (FVDiff t1) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT t1} \<Longrightarrow> frechet I t1 (fst \<nu>) (snd \<nu>) = frechet J t1 (fst \<nu>') (snd \<nu>'))"
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Neg t1))"
  assume IA:"Iagree I J {Inl x |x. x \<in> SIGT (Neg t1)}"
  have subs:"{Inl x |x. x \<in> SIGT t1} \<subseteq> {Inl x |x. x \<in> SIGT (Neg t1)}" 
    by auto
  from IA 
    have IA1:"Iagree I J {Inl x |x. x \<in> SIGT t1}"
    using Iagree_sub[OF subs(1)]  by auto
  have agree1:"Vagree \<nu> \<nu>' (FVDiff t1)" using agree agree_neg by (blast)
  have agree1':"Vagree \<nu> \<nu>' (FVT t1)" using agree1 primify_contains by (auto simp add: Vagree_def, metis)
  have IH1':"(frechet I t1 (fst \<nu>) (snd \<nu>) = frechet J t1 (fst \<nu>') (snd \<nu>'))"
    using IH1 agree1 IA1 by (auto)
  show "?case"
    using coincidence_sterm[OF agree1'] coincidence_sterm[OF agree1'] 
    by (auto simp add: IH1' UnCI Vagree_def)
next
  case (dfree_Plus t1 t2) 
  assume dfree1:"dfree t1"
  assume dfree2:"dfree t2"
  assume IH1:"(Vagree \<nu> \<nu>' (FVDiff t1) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT t1} \<Longrightarrow> frechet I t1 (fst \<nu>) (snd \<nu>) = frechet J t1 (fst \<nu>') (snd \<nu>'))"
  assume IH2:"(Vagree \<nu> \<nu>' (FVDiff t2) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT t2} \<Longrightarrow>  frechet I t2 (fst \<nu>) (snd \<nu>) = frechet J t2 (fst \<nu>') (snd \<nu>'))"
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Plus t1 t2))"
  assume IA:"Iagree I J {Inl x |x. x \<in> SIGT (Plus t1 t2)}"
  have subs:"{Inl x |x. x \<in> SIGT t1} \<subseteq> {Inl x |x. x \<in> SIGT (Plus t1 t2)}" "{Inl x |x. x \<in> SIGT t2} \<subseteq> {Inl x |x. x \<in> SIGT (Plus t1 t2)}"
    by auto
  from IA 
    have IA1:"Iagree I J {Inl x |x. x \<in> SIGT t1}"
    and  IA2:"Iagree I J {Inl x |x. x \<in> SIGT t2}"
    using Iagree_sub[OF subs(1)] Iagree_sub[OF subs(2)] by auto
  have agree1:"Vagree \<nu> \<nu>' (FVDiff t1)" using agree agree_plus1 by (blast)
  have agree2:"Vagree \<nu> \<nu>' (FVDiff t2)" using agree agree_plus2 by (blast)
  have agree1':"Vagree \<nu> \<nu>' (FVT t1)" using agree1 primify_contains by (auto simp add: Vagree_def, metis)
  have agree2':"Vagree \<nu> \<nu>' (FVT t2)" using agree2 primify_contains by (auto simp add: Vagree_def, metis)
  have IH1':"(frechet I t1 (fst \<nu>) (snd \<nu>) = frechet J t1 (fst \<nu>') (snd \<nu>'))"
    using IH1 agree1 IA1 by (auto)
  have IH2':"(frechet I t2 (fst \<nu>) (snd \<nu>) = frechet J t2 (fst \<nu>') (snd \<nu>'))"
    using IH2 agree2 IA2 by (auto)
  show "?case"
    using coincidence_sterm[OF agree1'] coincidence_sterm[OF agree1'] coincidence_sterm[OF agree2']
    by (auto simp add: IH1' IH2' UnCI Vagree_def)

next
  case (dfree_Times t1 t2) 
  assume dfree1:"dfree t1"
  assume dfree2:"dfree t2"
  assume IH1:"(Vagree \<nu> \<nu>' (FVDiff t1) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT t1} \<Longrightarrow> frechet I t1 (fst \<nu>) (snd \<nu>) = frechet J t1 (fst \<nu>') (snd \<nu>'))"
  assume IH2:"(Vagree \<nu> \<nu>' (FVDiff t2) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT t2} \<Longrightarrow>  frechet I t2 (fst \<nu>) (snd \<nu>) = frechet J t2 (fst \<nu>') (snd \<nu>'))"
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Times t1 t2))"
  assume IA:"Iagree I J {Inl x |x. x \<in> SIGT (Times t1 t2)}"
  have subs:"{Inl x |x. x \<in> SIGT t1} \<subseteq> {Inl x |x. x \<in> SIGT (Times t1 t2)}" "{Inl x |x. x \<in> SIGT t2} \<subseteq> {Inl x |x. x \<in> SIGT (Times t1 t2)}"
    by auto
  from IA 
    have IA1:"Iagree I J {Inl x |x. x \<in> SIGT t1}"
    and  IA2:"Iagree I J {Inl x |x. x \<in> SIGT t2}"
    using Iagree_sub[OF subs(1)] Iagree_sub[OF subs(2)] by auto
  have agree1:"Vagree \<nu> \<nu>' (FVDiff t1)" using agree agree_times1 by (blast) 
  then have agree1':"Vagree \<nu> \<nu>' (FVT t1)"
    using agree1 primify_contains by (auto simp add: Vagree_def, metis)
  have agree2:"Vagree \<nu> \<nu>' (FVDiff t2)" using agree agree_times2 by (blast)
  then have agree2':"Vagree \<nu> \<nu>' (FVT t2)"
    using agree2 primify_contains by (auto simp add: Vagree_def, metis)
  have IH1':"(frechet I t1 (fst \<nu>) (snd \<nu>) = frechet J t1 (fst \<nu>') (snd \<nu>'))"
    using IH1 agree1 IA1 by (auto)
  have IH2':"(frechet I t2 (fst \<nu>) (snd \<nu>) = frechet J t2 (fst \<nu>') (snd \<nu>'))"
    using IH2 agree2 IA2 by (auto)
  note co1 = coincidence_sterm'[of "t1" \<nu> \<nu>' I J] and co2 = coincidence_sterm'[of "t2" \<nu> \<nu>' I J]
  show "?case"
    using co1 [OF dfree1 agree1' IA1] co2 [OF dfree2 agree2' IA2] IH1' IH2' by auto
qed

lemma coincidence_dterm:
  fixes I :: "('a::finite, 'b::finite, 'c::finite) interp" and \<nu> :: "'c state" and \<nu>'::"'c state"
  shows "dsafe \<theta> \<Longrightarrow> Vagree \<nu> \<nu>' (FVT \<theta>) \<Longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I \<theta> \<nu>'"
proof (induction rule: dsafe.induct)
  case (dsafe_Funl f)
  assume "Vagree \<nu> \<nu>' (FVT ($$F f))"
  then have agree:"Vagree \<nu> \<nu>' UNIV" by simp
  then show "?case"
    using agree_UNIV_eq[OF agree] by auto
next
  case (dsafe_Fun args f)
  have safe:"(\<And>i. dsafe (args i))"
  and IH:"\<And>i. Vagree \<nu> \<nu>' (FVT (args i)) \<Longrightarrow> dterm_sem I (args i) \<nu> = dterm_sem I (args i) \<nu>'"
  and agree:"Vagree \<nu> \<nu>' (FVT ($f f args))" 
    using dsafe_Fun.IH dsafe_Fun.prems by auto
  then have "\<And>i. Vagree \<nu> \<nu>' (FVT (args i))"
    using agree_func_fvt by (metis)
  then show "?case"
    using safe coincidence_sterm IH rangeI by (auto)
qed (auto simp: Vagree_def directional_derivative_def coincidence_frechet)

lemma coincidence_dterm':
  fixes I J :: "('a::finite, 'b::finite, 'c::finite) interp" and \<nu> :: "'c::finite state" and \<nu>'::"'c::finite state"
  shows "dsafe \<theta> \<Longrightarrow> Vagree \<nu> \<nu>' (FVT \<theta>) \<Longrightarrow> Iagree I J {Inl x | x. x \<in> (SIGT \<theta>)} \<Longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem J \<theta> \<nu>'"
proof (induction rule: dsafe.induct)
  case (dsafe_Fun args f) then 
    have safe:"(\<And>i. dsafe (args i))"
    and IH:"\<And>i. Vagree \<nu> \<nu>' (FVT (args i)) \<Longrightarrow> Iagree I J {Inl x | x. x \<in> (SIGT (args i))} \<Longrightarrow>  dterm_sem I (args i) \<nu> = dterm_sem J (args i) \<nu>'"
    and agree:"Vagree \<nu> \<nu>' (FVT ($f f args))"
    and IA:"Iagree I J {Inl x |x. x \<in> SIGT ($f f args)}"
      by auto
    have subs:"\<And>i. {Inl x |x. x \<in> SIGT (args i)} \<subseteq> {Inl x |x. x \<in> SIGT ($f f args)}" by auto
    from IA have IAs:
      "\<And>i. Iagree I J {Inl x |x. x \<in> SIGT (args i)}"
        using Iagree_sub [OF subs IA] by auto
    from agree have agrees:"\<And>i. Vagree \<nu> \<nu>' (FVT (args i))"
      using agree_func_fvt by (metis)
    from Iagree_Func [OF IA] have fEq:"Functions I f = Functions J f" by auto 
    then show "?case"
      using safe coincidence_sterm IH[OF agrees IAs] rangeI agrees fEq
      by (auto)
  next
  case (dsafe_Funl  f) then 
    have agree:"Vagree \<nu> \<nu>' (UNIV)"
    and IA:"Iagree I J {Inl x |x. x \<in> SIGT ($$F f)}"
      by auto
    from Iagree_Funl [OF IA] have fEq:"Funls I f = Funls J f" by auto 
    then show "?case" using agree_UNIV_eq[OF agree] by auto
next
  case (dsafe_Plus \<theta>\<^sub>1 \<theta>\<^sub>2) then
  have safe:"dsafe \<theta>\<^sub>1" "dsafe \<theta>\<^sub>2"
  and IH1:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<Longrightarrow> dterm_sem I \<theta>\<^sub>1 \<nu> = dterm_sem J \<theta>\<^sub>1 \<nu>'"
  and IH2:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<Longrightarrow> dterm_sem I \<theta>\<^sub>2 \<nu> = dterm_sem J \<theta>\<^sub>2 \<nu>'"
  and VA:"Vagree \<nu> \<nu>' (FVT (Plus \<theta>\<^sub>1 \<theta>\<^sub>2))"
  and IA:"Iagree I J {Inl x |x. x \<in> SIGT (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)}"
    by auto
  from VA have VA1:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1)" and VA2:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2)" 
    unfolding Vagree_def by auto
  have subs:"{Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<subseteq> {Inl x |x. x \<in> SIGT (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)}" 
    "{Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<subseteq> {Inl x |x. x \<in> SIGT (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)}"by auto
  from IA have IA1:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1}" and IA2:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2}"
    using Iagree_sub subs by auto
  then show ?case 
    using IH1[OF VA1 IA1] IH2[OF VA2 IA2] by auto
next
  case (dsafe_Times \<theta>\<^sub>1 \<theta>\<^sub>2) then
  have safe:"dsafe \<theta>\<^sub>1" "dsafe \<theta>\<^sub>2"
    and IH1:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<Longrightarrow> dterm_sem I \<theta>\<^sub>1 \<nu> = dterm_sem J \<theta>\<^sub>1 \<nu>'"
    and IH2:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<Longrightarrow> dterm_sem I \<theta>\<^sub>2 \<nu> = dterm_sem J \<theta>\<^sub>2 \<nu>'"
    and VA:"Vagree \<nu> \<nu>' (FVT (Times \<theta>\<^sub>1 \<theta>\<^sub>2))"
    and IA:"Iagree I J {Inl x |x. x \<in> SIGT (Times \<theta>\<^sub>1 \<theta>\<^sub>2)}"
    by auto
  from VA have VA1:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1)" and VA2:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2)" 
    unfolding Vagree_def by auto
  have subs:"{Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<subseteq> {Inl x |x. x \<in> SIGT (Times \<theta>\<^sub>1 \<theta>\<^sub>2)}" 
    "{Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<subseteq> {Inl x |x. x \<in> SIGT (Times \<theta>\<^sub>1 \<theta>\<^sub>2)}"by auto
  from IA have IA1:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1}" and IA2:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2}"
    using Iagree_sub subs by auto
  then show ?case 
    using IH1[OF VA1 IA1] IH2[OF VA2 IA2] by auto  
next
case (dsafe_Max \<theta>\<^sub>1 \<theta>\<^sub>2) then
  have safe:"dsafe \<theta>\<^sub>1" "dsafe \<theta>\<^sub>2"
    and IH1:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<Longrightarrow> dterm_sem I \<theta>\<^sub>1 \<nu> = dterm_sem J \<theta>\<^sub>1 \<nu>'"
    and IH2:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<Longrightarrow> dterm_sem I \<theta>\<^sub>2 \<nu> = dterm_sem J \<theta>\<^sub>2 \<nu>'"
    and VA:"Vagree \<nu> \<nu>' (FVT (trm.Max \<theta>\<^sub>1 \<theta>\<^sub>2))"
    and IA:"Iagree I J {Inl x |x. x \<in> SIGT (trm.Max \<theta>\<^sub>1 \<theta>\<^sub>2)}"
    by auto
  from VA have VA1:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1)" and VA2:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2)" 
    unfolding Vagree_def by auto
  have subs:"{Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<subseteq> {Inl x |x. x \<in> SIGT (Max \<theta>\<^sub>1 \<theta>\<^sub>2)}" 
    "{Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<subseteq> {Inl x |x. x \<in> SIGT (Max \<theta>\<^sub>1 \<theta>\<^sub>2)}"by auto
  from IA have IA1:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1}" and IA2:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2}"
    using Iagree_sub subs by auto
  then show ?case 
    using IH1[OF VA1 IA1] IH2[OF VA2 IA2] by auto  
next
case (dsafe_Min \<theta>\<^sub>1 \<theta>\<^sub>2) then
  have safe:"dsafe \<theta>\<^sub>1" "dsafe \<theta>\<^sub>2"
    and IH1:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<Longrightarrow> dterm_sem I \<theta>\<^sub>1 \<nu> = dterm_sem J \<theta>\<^sub>1 \<nu>'"
    and IH2:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<Longrightarrow> dterm_sem I \<theta>\<^sub>2 \<nu> = dterm_sem J \<theta>\<^sub>2 \<nu>'"
    and VA:"Vagree \<nu> \<nu>' (FVT (trm.Min \<theta>\<^sub>1 \<theta>\<^sub>2))"
    and IA:"Iagree I J {Inl x |x. x \<in> SIGT (trm.Min \<theta>\<^sub>1 \<theta>\<^sub>2)}"
    by auto
  from VA have VA1:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>1)" and VA2:"Vagree \<nu> \<nu>' (FVT \<theta>\<^sub>2)" 
    unfolding Vagree_def by auto
  have subs:"{Inl x |x. x \<in> SIGT \<theta>\<^sub>1} \<subseteq> {Inl x |x. x \<in> SIGT (Max \<theta>\<^sub>1 \<theta>\<^sub>2)}" 
    "{Inl x |x. x \<in> SIGT \<theta>\<^sub>2} \<subseteq> {Inl x |x. x \<in> SIGT (Max \<theta>\<^sub>1 \<theta>\<^sub>2)}"by auto
  from IA have IA1:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>1}" and IA2:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>\<^sub>2}"
    using Iagree_sub subs by auto
  then show ?case 
    using IH1[OF VA1 IA1] IH2[OF VA2 IA2] by auto
next
case (dsafe_Abs \<theta>) then
  have safe:"dsafe \<theta>"
    and IH1:"Vagree \<nu> \<nu>' (FVT \<theta>) \<Longrightarrow> Iagree I J {Inl x |x. x \<in> SIGT \<theta>} \<Longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem J \<theta> \<nu>'"
    and VA:"Vagree \<nu> \<nu>' (FVT (trm.Abs \<theta>))"
    and IA:"Iagree I J {Inl x |x. x \<in> SIGT (trm.Abs \<theta>)}"
    by auto
  from VA have VA1:"Vagree \<nu> \<nu>' (FVT \<theta>)" 
    unfolding Vagree_def by auto
  have subs:"{Inl x |x. x \<in> SIGT \<theta>} \<subseteq> {Inl x |x. x \<in> SIGT (Abs \<theta>)}"  by auto
  from IA have IA1:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>}"
    using Iagree_sub subs by auto
  then show ?case 
    using IH1[OF VA1 IA1] by auto  
qed (auto simp: Vagree_def directional_derivative_def coincidence_frechet')

subsection \<open>ODE Coincidence Theorems\<close>
lemma coincidence_ode:
  fixes I J :: "('a::finite, 'b::finite, 'c::finite) interp" and \<nu> :: "'c::finite state" and \<nu>'::"'c::finite state"
  assumes goodI:"is_interp I"
  assumes goodJ:"is_interp J"
  shows "osafe ODE \<Longrightarrow> 
         Vagree \<nu> \<nu>' (Inl ` FVO ODE) \<Longrightarrow> 
         Iagree I J ({Inl x | x. Inl x \<in> SIGO ODE}  \<union>  {Inr (Inr x) | x. Inr x \<in> SIGO ODE}) \<Longrightarrow> 
         ODE_sem I ODE (fst \<nu>) = ODE_sem J ODE (fst \<nu>')"
proof (induction rule: osafe.induct)
  case (osafe_Var c sp)
  then show ?case
  proof (auto, cases sp, simp)
    assume sp:"sp = None"
    assume VA:"Vagree \<nu> \<nu>' (range Inl)"
    have eqV:"(fst \<nu>) = (fst \<nu>')"
      using agree_UNIV_fst[OF VA] by auto
    assume IA:"Iagree I J {Inr (Inr c)}"
    have eqIJ:"ODEs I c All = ODEs J c All"
      using Iagree_ODE[OF IA] by auto
    have eqbvIJ:"ODEBV I c All = ODEBV J c All"
      using Iagree_ODEBV[OF IA] by auto
    show "(\<chi> i. if i \<in> ODEBV I c None then ODEs I c sp (fst \<nu>) $ i else 0) 
        = (\<chi> i. if i \<in> ODEBV J c None then ODEs J c sp (fst \<nu>') $ i else 0)"
      apply(rule vec_extensionality)
      using sp eqV eqIJ eqbvIJ by (auto)
  next 
    fix x
    assume sp:"sp = Some x"
    assume VA:"Vagree \<nu> \<nu>' (Inl ` FVO (OVar c sp))"
    then have VA:"Vagree \<nu> \<nu>' (range Inl)" using sp by auto
    have eqV:"(fst \<nu>) = (fst \<nu>')"
      using agree_UNIV_fst[OF VA] by auto
    assume IA:"Iagree I J {Inr (Inr c)}"
    have eqIJ:"ODEs I c (NB x) = ODEs J c (NB x)"
      using Iagree_ODE[OF IA] by auto
    have eqbvIJ:"ODEBV I c (NB x) = ODEBV J c (NB x)"
      using Iagree_ODEBV[OF IA] by auto
    have iBound:"\<And>ode x. ODEBV I ode (NB x) \<subseteq> - {x}" using goodI unfolding is_interp_def by auto
    have jBound:"\<And>ode x. ODEBV J ode (NB x) \<subseteq> - {x}" using goodJ unfolding is_interp_def by auto
    show "(\<chi> i. if i \<in> ODEBV I c sp then ODEs I c sp (fst \<nu>) $ i else 0) = (\<chi> i. if i \<in> ODEBV J c sp then ODEs J c sp (fst \<nu>') $ i else 0)"
       apply(rule vec_extensionality)
      using sp eqV eqIJ eqbvIJ by(auto simp add: eqV eqIJ sp eqbvIJ)
  qed
next
  case (osafe_Sing \<theta> x)
  then show ?case
  proof (auto)
  assume free:"dfree \<theta>"
  and VA:"Vagree \<nu> \<nu>' (insert (Inl x) (Inl ` {x. Inl x \<in> FVT \<theta>}))"
  and IA:"Iagree I J {Inl x |x. x \<in> SIGT \<theta>}"
  from VA have VA':"Vagree \<nu> \<nu>' {Inl x | x. Inl x \<in> FVT \<theta>}" unfolding Vagree_def by auto
  have agree_Lem:"\<And>\<theta>. dfree \<theta> \<Longrightarrow> Vagree \<nu> \<nu>' {Inl x | x. Inl x \<in> FVT \<theta>} \<Longrightarrow> Vagree \<nu> \<nu>' (FVT \<theta>)"
    subgoal for \<theta>
      apply(induction rule: dfree.induct)
           by(auto simp add: Vagree_def)
    done
  have trm:"sterm_sem I  \<theta> (fst \<nu>) = sterm_sem J \<theta> (fst \<nu>')"
    using coincidence_sterm' free VA' IA agree_Lem[of \<theta>, OF free] by blast
  show "(\<chi> i. if i = x then sterm_sem I \<theta> (fst \<nu>) else 0) = (\<chi> i. if i = x then sterm_sem J \<theta> (fst \<nu>') else 0)"
    by (auto simp add: vec_eq_iff trm)
  qed
next
  case (osafe_Prod ODE1 ODE2)
  then show ?case 
  proof (auto)
    assume safe1:"osafe ODE1"
      and  safe2:"osafe ODE2"
      and  disjoint:"ODE_dom ODE1 \<inter> ODE_dom ODE2 = {}"
      and  IH1:"Vagree \<nu> \<nu>' (Inl ` FVO ODE1) \<Longrightarrow>
         Iagree I J ({Inl x |x. Inl x \<in> SIGO ODE1} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE1}) \<Longrightarrow> ODE_sem I ODE1 (fst \<nu>) = ODE_sem J ODE1 (fst \<nu>')"
      and  IH2:"Vagree \<nu> \<nu>' (Inl ` FVO ODE2) \<Longrightarrow>
      Iagree I J ({Inl x |x. Inl x \<in> SIGO ODE2} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE2}) \<Longrightarrow> ODE_sem I ODE2 (fst \<nu>) = ODE_sem J ODE2 (fst \<nu>')"
      and VA:"Vagree \<nu> \<nu>' (Inl ` (FVO ODE1 \<union>  FVO ODE2))"
      and IA:"Iagree I J ({Inl x |x. Inl x \<in> SIGO ODE1 \<or> Inl x \<in> SIGO ODE2} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE1 \<or> Inr x \<in> SIGO ODE2})"
    let ?IA = "({Inl x |x. Inl x \<in> SIGO ODE1 \<or> Inl x \<in> SIGO ODE2} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE1 \<or> Inr x \<in> SIGO ODE2})"
    have FVsubs:
      "Inl ` FVO ODE2 \<subseteq> Inl ` (FVO ODE1 \<union> FVO ODE2)"
      "Inl ` FVO ODE1 \<subseteq> Inl ` (FVO ODE1 \<union> FVO ODE2)"
      by auto
    from VA 
    have VA1:"Vagree \<nu> \<nu>' (Inl ` FVO ODE1)"
     and VA2:"Vagree \<nu> \<nu>' (Inl ` FVO ODE2)"
      using agree_sub[OF FVsubs(1)] agree_sub[OF FVsubs(2)] 
      by (auto)
    have SIGsubs:
      "({Inl x |x. Inl x \<in> SIGO ODE1} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE1}) \<subseteq> ?IA"
      "({Inl x |x. Inl x \<in> SIGO ODE2} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE2}) \<subseteq> ?IA"
      by auto
    from IA
    have IA1:"Iagree I J ({Inl x |x. Inl x \<in> SIGO ODE1} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE1})"
      and IA2:"Iagree I J ({Inl x |x. Inl x \<in> SIGO ODE2} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE2})"
      using Iagree_sub[OF SIGsubs(1)] Iagree_sub[OF SIGsubs(2)] by auto
    show "ODE_sem I ODE1 (fst \<nu>) + ODE_sem I ODE2 (fst \<nu>) = ODE_sem J ODE1 (fst \<nu>') + ODE_sem J ODE2 (fst \<nu>')"
      using IH1[OF VA1 IA1] IH2[OF VA2 IA2] by auto
  qed
qed
  
lemma coincidence_ode':
  fixes I J :: "('a::finite, 'b::finite, 'c::finite) interp" and \<nu> :: "'c simple_state" and \<nu>'::"'c simple_state"
  assumes goodI:"is_interp I"
  assumes goodJ:"is_interp J"
  shows "
         osafe ODE \<Longrightarrow> 
         VSagree \<nu> \<nu>'  (FVO ODE) \<Longrightarrow> 
         Iagree I J ({Inl x | x. Inl x \<in> SIGO ODE}  \<union>  {Inr (Inr x) | x. Inr x \<in> SIGO ODE}) \<Longrightarrow> 
         ODE_sem I ODE \<nu> = ODE_sem J ODE \<nu>'"
  using coincidence_ode[of I J ODE  "(\<nu>, \<chi> i. 0)" "(\<nu>', \<chi> i. 0)"] goodI goodJ
  apply(auto)
  unfolding VSagree_def Vagree_def apply auto
  done
  
lemma alt_sem_lemma:"\<And> I::('a::finite,'b::finite,'c::finite) interp. \<And>  ODE::('a::finite,'c::finite) ODE. \<And>sol. \<And>t::real. \<And> ab. osafe ODE \<Longrightarrow> 
  is_interp I \<Longrightarrow>
  ODE_sem I ODE (sol t) = ODE_sem I ODE (\<chi> i. if i \<in> FVO ODE then sol t $ i else ab $ i)"
proof -
  fix I::"('a,'b,'c) interp" 
    and ODE::"('a,'c) ODE"
    and sol 
    and t::real
    and ab
  assume safe:"osafe ODE"
  assume good_interp:"is_interp I"
  have VA:"VSagree (sol t) (\<chi> i. if i \<in> FVO ODE then sol t $ i else ab $ i) (FVO ODE)"
    unfolding VSagree_def Vagree_def by auto
  have IA: "Iagree I I ({Inl x | x. Inl x \<in> SIGO ODE}  \<union>  {Inr (Inr x) | x. Inr x \<in> SIGO ODE})" unfolding Iagree_def by auto
  show "ODE_sem I ODE (sol t) = ODE_sem I ODE (\<chi> i. if  i \<in> FVO ODE then sol t $ i else ab $ i)" 
    using coincidence_ode'[OF good_interp good_interp safe VA IA] by auto
qed  
  
lemma bvo_to_fvo:"Inl x \<in> BVO ODE \<Longrightarrow>  x \<in> FVO ODE"
proof (induction ODE)
  case (OVar x1 x2)
then show ?case by(cases x2,auto)
next
  case (OSing x1 x2)
  then show ?case by auto
next
  case (OProd ODE1 ODE2)
  then show ?case by auto
qed

  
lemma ode_to_fvo:"x \<in> ODE_vars I ODE \<Longrightarrow>  x \<in> FVO ODE"
proof (induction ODE)
  case (OVar x1 x2)
then show ?case by(cases x2,auto)
next
  case (OSing x1 x2)
  then show ?case by auto
next
  case (OProd ODE1 ODE2)
  then show ?case by auto
qed

definition coincide_hp :: "('a::finite, 'b::finite, 'c::finite) hp \<Rightarrow> ('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> bool"
where "coincide_hp \<alpha> I J \<longleftrightarrow> (\<forall> \<nu> \<nu>' \<mu> V. Iagree I J (SIGP \<alpha>) \<longrightarrow> Vagree \<nu> \<nu>' V \<longrightarrow> V \<supseteq> (FVP \<alpha>) \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I \<alpha> \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J \<alpha> \<and> Vagree \<mu> \<mu>' (MBV \<alpha> \<union> V)))"

definition ode_sem_equiv ::"('a::finite, 'b::finite, 'c::finite) hp \<Rightarrow> ('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> bool"
where "ode_sem_equiv \<alpha> I \<longleftrightarrow>
   (\<forall>ODE::('a::finite,'c::finite) ODE. \<forall>\<phi>::('a::finite,'b::finite,'c::finite)formula. osafe ODE \<longrightarrow> fsafe \<phi>  \<longrightarrow>
   (\<alpha> = EvolveODE ODE \<phi>) \<longrightarrow>
  {(\<nu>, mk_v I ODE \<nu> (sol t)) | \<nu> sol t.
      t \<ge> 0 \<and>
      (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu> x \<in> fml_sem I \<phi>} \<and>
      VSagree (sol 0) (fst \<nu>) {x | x. Inl x \<in> FVP (EvolveODE ODE \<phi>)}} = 
  {(\<nu>, mk_v I ODE \<nu> (sol t)) | \<nu> sol t.
      t \<ge> 0 \<and>
      (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu> x \<in> fml_sem I \<phi>} \<and>
      sol 0 = fst \<nu>})"
  
definition coincide_hp' :: "('a::finite, 'b::finite, 'c::finite) hp \<Rightarrow> bool"
where "coincide_hp' \<alpha> \<longleftrightarrow> (\<forall> I J. is_interp I \<longrightarrow> is_interp J \<longrightarrow> (coincide_hp \<alpha> I J \<and> ode_sem_equiv \<alpha> I))"

definition coincide_fml  :: "('a::finite, 'b::finite, 'c::finite) formula \<Rightarrow> bool"
where "coincide_fml \<phi> \<longleftrightarrow> (\<forall> \<nu> \<nu>' I J . is_interp I \<longrightarrow> is_interp J \<longrightarrow> Iagree I J (SIGF \<phi>) \<longrightarrow> Vagree \<nu> \<nu>' (FVF \<phi>) \<longrightarrow> \<nu> \<in> fml_sem I \<phi> \<longleftrightarrow> \<nu>' \<in> fml_sem J \<phi>)"

lemma coinc_fml [simp]: "coincide_fml \<phi>  = (\<forall> \<nu> \<nu>' I J. is_interp I \<longrightarrow> is_interp J \<longrightarrow>Iagree I J (SIGF \<phi>) \<longrightarrow> Vagree \<nu> \<nu>' (FVF \<phi>) \<longrightarrow> \<nu> \<in> fml_sem I \<phi> \<longleftrightarrow> \<nu>' \<in> fml_sem J \<phi>)"
  unfolding coincide_fml_def by auto

subsection \<open>Coincidence Theorems for Programs and Formulas\<close>
lemma coincidence_hp_fml:
  fixes \<alpha>::"('a::finite, 'b::finite, 'c::finite) hp"
  fixes \<phi>::"('a::finite, 'b::finite, 'c::finite) formula"
 shows "(hpsafe \<alpha> \<longrightarrow> coincide_hp' \<alpha>) \<and> (fsafe \<phi> \<longrightarrow> coincide_fml \<phi>)"
proof (induction rule: hpsafe_fsafe.induct)
  case (hpsafe_Pvar x)
  thus "?case" 
    apply(unfold coincide_hp'_def | rule allI | rule conjI | rule impI)+
     prefer 2 unfolding ode_sem_equiv_def subgoal by auto
    unfolding coincide_hp_def apply(auto)
    subgoal for I J a b aa ba ab bb V
    proof -
      assume IA:"Iagree I J {Inr (Inr x)}"
        have Peq:"\<And>y. y \<in> Programs I x \<longleftrightarrow> y \<in> Programs J x" using Iagree_Prog[OF IA] by auto
      assume agree:"Vagree (a, b) (aa, ba) V"
        and sub:"UNIV \<subseteq> V"
        and sem:"((a, b), ab, bb) \<in> Programs I x"
      from agree_UNIV_eq[OF agree_sub [OF sub agree]]
      have eq:"(a,b) = (aa,ba)" by auto
      hence sem':"((aa,ba), (ab,bb)) \<in> Programs I x"
        using sem by auto
      have triv_sub:"V \<subseteq> UNIV" by auto
      have VA:"Vagree (ab,bb) (ab,bb) V" using agree_sub[OF triv_sub agree_refl[of "(ab,bb)"]] eq
        by auto
      show "\<exists>a b. ((aa, ba), a, b) \<in> Programs J x \<and> Vagree (ab, bb) (a, b) V"
        apply(rule exI[where x="ab"])
        apply(rule exI[where x="bb"])
        using sem eq VA by (auto simp add: Peq)
    qed
    done
next
  case (hpsafe_Assign e x) then 
  show "?case" 
  proof (auto simp only: coincide_hp'_def ode_sem_equiv_def coincide_hp_def)
    fix I J :: "('a::finite,'b::finite,'c::finite) interp" 
      and \<nu>1 \<nu>2 \<nu>'1 \<nu>'2 \<mu>1 \<mu>2 V
    assume safe:"dsafe e"
      and IA:"Iagree I J (SIGP (x := e))"
      and VA:"Vagree (\<nu>1, \<nu>2) (\<nu>'1, \<nu>'2) V"
      and sub:"FVP (x := e) \<subseteq> V"
      and sem:"((\<nu>1, \<nu>2), (\<mu>1, \<mu>2)) \<in> prog_sem I (x := e)"
    from VA have VA':"Vagree (\<nu>1, \<nu>2) (\<nu>'1, \<nu>'2) (FVT e)" unfolding FVP.simps Vagree_def using sub by auto
    have Ssub:"{Inl x | x. x \<in> SIGT e} \<subseteq> (SIGP (x := e))" by auto
    from IA have IA':"Iagree I J {Inl x | x. x \<in> SIGT e}" using Ssub unfolding SIGP.simps by auto
    have "((\<nu>1, \<nu>2), repv (\<nu>1, \<nu>2) x (dterm_sem I e (\<nu>1, \<nu>2))) \<in> prog_sem I (x := e)" by auto
    then have sem':"((\<nu>'1, \<nu>'2), repv (\<nu>'1, \<nu>'2) x (dterm_sem J e (\<nu>'1, \<nu>'2))) \<in> prog_sem J (x := e)" 
      using coincidence_dterm' safe VA' IA' by auto
    from sem have eq:"(\<mu>1, \<mu>2) = (repv (\<nu>1, \<nu>2) x (dterm_sem I e (\<nu>1, \<nu>2)))" by auto
    have VA'':"Vagree (\<mu>1, \<mu>2) (repv (\<nu>'1, \<nu>'2) x (dterm_sem J e (\<nu>'1, \<nu>'2))) (MBV (x := e) \<union> V)" 
      using coincidence_dterm'[of e "(\<nu>1,\<nu>2)" "(\<nu>'1,\<nu>'2)" I J] safe VA' IA' eq agree_refl VA unfolding MBV.simps Vagree_def
      by auto
    show "\<exists>\<mu>'. ((\<nu>'1, \<nu>'2), \<mu>') \<in> prog_sem J (x := e) \<and> Vagree (\<mu>1, \<mu>2) \<mu>' (MBV (x := e) \<union> V)"
      using VA'' sem' by blast
  qed
next
  case (hpsafe_AssignAny x) then 
  show "?case" 
  proof (auto simp only: coincide_hp'_def ode_sem_equiv_def coincide_hp_def)
    fix I J :: "('a::finite,'b::finite,'c::finite) interp" 
      and \<nu>1 \<nu>2 \<nu>'1 \<nu>'2 \<mu>1 \<mu>2 V
    assume IA:"Iagree I J (SIGP (AssignAny x))"
      and VA:"Vagree (\<nu>1, \<nu>2) (\<nu>'1, \<nu>'2) V"
      and sub:"FVP (AssignAny x) \<subseteq> V"
      and sem:"((\<nu>1, \<nu>2), (\<mu>1, \<mu>2)) \<in> prog_sem I (AssignAny x)"
    show "\<exists>\<mu>'. ((\<nu>'1, \<nu>'2), \<mu>') \<in> prog_sem J (AssignAny x) \<and> Vagree (\<mu>1, \<mu>2) \<mu>' (MBV (AssignAny x) \<union> V)"
      using IA VA sub sem apply auto subgoal for r
      apply(rule exI[where x="fst (repv (\<nu>'1,\<nu>'2) x r)"])
      apply(rule conjI)
      subgoal apply(rule exI[where x=r]) 
        apply(rule vec_extensionality)
        using VA sub sem by(auto simp add: vec_eq_iff Vagree_def)
      subgoal using VA sub sem by(auto simp add: vec_eq_iff Vagree_def) done done
  qed
next
  case (hpsafe_DiffAssign e x) then show "?case" 
  proof (auto simp only: coincide_hp'_def ode_sem_equiv_def coincide_hp_def)
    fix I J::"('a,'b,'c) interp"
      and \<nu> \<nu>' \<mu> V 
    assume safe:"dsafe e"
      and IA:"Iagree I J (SIGP (DiffAssign x e))"
      and VA:"Vagree \<nu> \<nu>' V"
      and sub:"FVP (DiffAssign x e) \<subseteq> V"
      and sem:"(\<nu>, \<mu>) \<in> prog_sem I (DiffAssign x e)"
    from VA have VA':"Vagree \<nu> \<nu>' (FVT e)" unfolding FVP.simps Vagree_def using sub by auto
    have Ssub:"{Inl x | x. x \<in> SIGT e} \<subseteq> (SIGP (DiffAssign x e))" by auto
    from IA have IA':"Iagree I J {Inl x | x. x \<in> SIGT e}" using Ssub unfolding SIGP.simps by auto
    have "(\<nu>, repv \<nu> x (dterm_sem I e \<nu>)) \<in> prog_sem I (x := e)" by auto
    then have sem':"(\<nu>', repd \<nu>' x (dterm_sem J e \<nu>')) \<in> prog_sem J (DiffAssign x e)" 
      using coincidence_dterm' safe VA' IA' by auto
    from sem have eq:"\<mu> = (repd \<nu> x (dterm_sem I e \<nu>))" by auto
    have VA':"Vagree \<mu> (repd \<nu>' x (dterm_sem J e \<nu>')) (MBV (DiffAssign x e) \<union> V)" 
      using coincidence_dterm'[OF safe VA', of I J, OF IA'] eq agree_refl VA unfolding MBV.simps Vagree_def
      by auto
    show "\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J (DiffAssign x e) \<and> Vagree \<mu> \<mu>' (MBV (DiffAssign x e) \<union> V)"
      using VA' sem' by blast
  qed

next
  case (hpsafe_Test P) then 
  show "?case" 
  proof (auto simp add:coincide_hp'_def ode_sem_equiv_def coincide_hp_def)
    fix I J::"('a,'b,'c) interp" and \<nu> \<nu>' \<omega> \<omega>' ::"'c simple_state"
      and V
    assume safe:"fsafe P"
    assume goodI:"is_interp I"
    assume goodJ:"is_interp J"
    assume "\<forall>a b aa ba I.
          is_interp I \<longrightarrow>
          (\<forall>J. is_interp J \<longrightarrow> Iagree I J (SIGF P) \<longrightarrow> Vagree (a, b) (aa, ba) (FVF P) \<longrightarrow> ((a, b) \<in> fml_sem I P) = ((aa, ba) \<in> fml_sem J P))"
    hence IH:"Iagree I J (SIGF P) \<Longrightarrow> Vagree (\<nu>, \<nu>') (\<omega>, \<omega>') (FVF P) \<Longrightarrow> ((\<nu>, \<nu>') \<in> fml_sem I P) = ((\<omega>, \<omega>') \<in> fml_sem J P)"
      using goodI goodJ by auto
    assume IA:"Iagree I J (SIGF P)"
    assume VA:"Vagree (\<nu>, \<nu>') (\<omega>, \<omega>') V"
    assume sub:"FVF P \<subseteq> V"
      hence VA':"Vagree (\<nu>, \<nu>') (\<omega>, \<omega>') (FVF P)" using agree_supset VA by auto
    assume sem:"(\<nu>, \<nu>') \<in> fml_sem I P"
    show "(\<omega>, \<omega>') \<in> fml_sem J P" using IH[OF IA VA'] sem by auto
  qed

next
  case (hpsafe_Evolve ODE P) then show "?case"
    proof (unfold coincide_hp'_def)
      assume osafe:"osafe ODE"
      assume fsafe:"fsafe P"
      assume IH:"coincide_fml P"
      from IH have IHF:"\<And>\<nu> \<nu>' I J. Iagree I J (SIGF P) \<Longrightarrow> is_interp I \<Longrightarrow> is_interp J \<Longrightarrow> Vagree \<nu> \<nu>' (FVF P) \<Longrightarrow> (\<nu> \<in> fml_sem I P) = (\<nu>' \<in> fml_sem J P)"
        unfolding coincide_fml_def by auto
      have equiv:"\<And>I. is_interp I \<Longrightarrow> ode_sem_equiv (EvolveODE ODE P) I"
        subgoal for I
          apply(unfold ode_sem_equiv_def)
          apply(rule allI)+
          subgoal for ODE \<phi>
            apply(rule impI)+
            apply(auto) (* 2 subgoals *)
            subgoal for aa ba ab bb sol t
              apply(rule exI[where x="(\<lambda>t. \<chi> i. if i \<in> FVO ODE then sol t $ i else ab $ i)"])
              apply(rule conjI)
              subgoal using mk_v_agree[of I ODE "(ab,bb)" "sol t"] mk_v_agree[of I ODE "(ab,bb)" "(\<chi> i. if  i \<in> FVO ODE then sol t $ i else ab $ i)"]
                unfolding Vagree_def VSagree_def by (auto simp add: vec_eq_iff)
              apply(rule exI[where x=t])
              apply(rule conjI) (* 2 subgoals*)
              subgoal
                apply(rule agree_UNIV_eq)
                using mk_v_agree[of I ODE "(ab,bb)" "sol t"] 
                mk_v_agree[of I ODE "(ab,bb)" "(\<chi> i. if  i \<in> FVO ODE then sol t $ i else ab $ i)"]
                mk_v_agree[of I ODE "(\<chi> i. if  i \<in> FVO ODE then sol 0 $ i else ab $ i, bb)" "(\<chi> i. if  i \<in> FVO ODE then sol t $ i else ab $ i)"]
                unfolding Vagree_def VSagree_def
                apply(auto) (* 2 subgoals *)
                subgoal for i
                  apply(cases "Inl i \<in> BVO ODE")
                  subgoal
                  using bvo_to_fvo[of i ODE] 
                  by (metis (no_types, lifting) image_eqI)
                  using bvo_to_fvo[of i ODE] 
                  by (smt Inl_Inr_False Inl_inject image_iff ode_to_fvo)
                using bvo_to_fvo[of i ODE]
              proof -
                fix ia :: 'c
                assume good_interp:"is_interp I"
                assume a1: "osafe ODE"
                assume a2: "(aa, ba) = mk_v I ODE (ab, bb) (sol t)"
                assume a3: "\<forall>i. (Inr i \<in> Inl ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (\<chi> i. if i \<in> FVO ODE then sol 0 $ i else ab $ i, bb) (\<chi> i. if i \<in> FVO ODE then sol t $ i else ab $ i)) $ i = ODE_sem I ODE (\<chi> i. if i \<in> FVO ODE then sol t $ i else ab $ i) $ i) \<and> ((Inr i::'c + 'c) \<in> Inr ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (\<chi> i. if i \<in> FVO ODE then sol 0 $ i else ab $ i, bb) (\<chi> i. if i \<in> FVO ODE then sol t $ i else ab $ i)) $ i = ODE_sem I ODE (\<chi> i. if i \<in> FVO ODE then sol t $ i else ab $ i) $ i)"
                assume a4: "\<forall>i. (Inr i \<in> Inl ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (ab, bb) (sol t)) $ i = ODE_sem I ODE (sol t) $ i) \<and> ((Inr i::'c + 'c) \<in> Inr ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (ab, bb) (sol t)) $ i = ODE_sem I ODE (sol t) $ i)"
                assume a5: "\<forall>i. Inr i \<notin> Inl ` ODE_vars I ODE \<and> (Inr i::'c + 'c) \<notin> Inr ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (\<chi> i. if i \<in> FVO ODE then sol 0 $ i else ab $ i, bb) (\<chi> i. if i \<in> FVO ODE then sol t $ i else ab $ i)) $ i = bb $ i"
                assume a6: "\<forall>i. Inr i \<notin> Inl ` ODE_vars I ODE \<and> (Inr i::'c + 'c) \<notin> Inr ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (ab, bb) (sol t)) $ i = bb $ i"
                have f7: "\<And>f r v. ODE_sem I ODE (\<chi> i. if i \<in> FVO ODE then f (r::real) $ i else v $ i) = ODE_sem I ODE (f r)"
(*                  using a1 good_interp alt_sem_lemma*) 
                  subgoal for f r v
                    by (rule HOL.sym[OF alt_sem_lemma[OF a1 good_interp, of f r v]] )
                    
                  done
                { assume "Inr ia \<notin> Inl ` ODE_vars I ODE"
                  { assume "(Inr ia::'c + 'c) \<notin> Inr ` ODE_vars I ODE \<and> Inr ia \<notin> Inl ` ODE_vars I ODE \<and> (Inr ia::'c + 'c) \<notin> Inr ` ODE_vars I ODE \<and> Inr ia \<notin> Inl ` ODE_vars I ODE"
                    then have "snd (aa, ba) $ ia = bb $ ia \<and> (Inr ia::'c + 'c) \<notin> Inr ` ODE_vars I ODE \<and> Inr ia \<notin> Inl ` ODE_vars I ODE"
                      using a6 a2 by presburger
                    then have "snd (mk_v I ODE (\<chi> c. if c \<in> FVO ODE then sol 0 $ c else ab $ c, bb) (\<chi> c. if c \<in> FVO ODE then sol t $ c else ab $ c)) $ ia = snd (aa, ba) $ ia"
                      using a5 by presburger }
                  then have "snd (mk_v I ODE (\<chi> c. if c \<in> FVO ODE then sol 0 $ c else ab $ c, bb) (\<chi> c. if c \<in> FVO ODE then sol t $ c else ab $ c)) $ ia = snd (aa, ba) $ ia"
                    using f7 a4 a3 a2 by force }
                then show "snd (mk_v I ODE (ab, bb) (sol t)) $ ia = snd (mk_v I ODE (\<chi> c. if c \<in> FVO ODE then sol 0 $ c else ab $ c, bb) (\<chi> c. if c \<in> FVO ODE then sol t $ c else ab $ c)) $ ia"
                  using a2 by fastforce
              qed
            apply(rule conjI)
             subgoal by auto
            apply(auto simp only: solves_ode_def has_vderiv_on_def has_vector_derivative_def)
             apply (rule has_derivative_vec[THEN has_derivative_eq_rhs])
              defer
              apply (rule ext)
              apply (subst scaleR_vec_def)
              apply (rule refl)
             subgoal for x unfolding VSagree_def apply auto
             proof - 
               assume osafe:"osafe ODE"
                 and fsafe:"fsafe \<phi>"
                 and eqP:"P = \<phi>"
                 and aaba: "(aa, ba) = mk_v I ODE (ab, bb) (sol t)"
                 and all:"\<forall>i. (*(Inl i \<in> BVO ODE \<longrightarrow> sol 0 $ i = ab $ i) \<and>*) (Inl i \<in> Inl ` FVO ODE \<longrightarrow> sol 0 $ i = ab $ i) \<and> (Inl i \<in> FVF \<phi> \<longrightarrow> sol 0 $ i = ab $ i)"
                 and allSol:"\<forall>x\<in>{0..t}. (sol has_derivative (\<lambda>xa. xa *\<^sub>R ODE_sem I ODE (sol x))) (at x within {0..t})"
                 and mkV:"sol \<in> {0..t} \<rightarrow> {x. mk_v I ODE (ab, bb) x \<in> fml_sem I \<phi>}"
                 and x:"0 \<le> x" 
                 and t:"x \<le> t"     
                 and good_interp:"is_interp I"
               from all have allT:"\<And>s. s \<ge> 0 \<Longrightarrow> s \<le> t \<Longrightarrow> mk_v I ODE (ab,bb) (sol s) \<in> fml_sem I \<phi>"
                 using mkV by auto
               have VA:"\<And>x. Vagree (mk_v I ODE (ab, bb) (sol x)) (mk_v I ODE (ab, bb) (\<chi> i. if  i \<in> FVO ODE then sol x $ i else ab $ i))
                   (FVF \<phi>)"
                 unfolding Vagree_def
                 apply(auto) (* 2 subgoals *)
                 subgoal for xa i
                   using mk_v_agree[of I ODE "(ab,bb)" "sol xa"] 
                         mk_v_agree[of I ODE "(ab,bb)" "(\<chi> i. if  i \<in> FVO ODE then sol xa $ i else ab $ i)"]
                   apply(cases "i \<in> ODE_vars I ODE")
                   using ode_to_fvo [of i I ODE] unfolding Vagree_def 
                   apply auto
                   by fastforce
                 subgoal for xa i
                   using mk_v_agree[of I ODE "(ab,bb)" "sol xa"] 
                       mk_v_agree[of I ODE "(ab,bb)" "(\<chi> i. if  i \<in> FVO ODE then sol xa $ i else ab $ i)"]
                       ODE_vars_lr
                   using ode_to_fvo[of i I ODE] unfolding Vagree_def apply auto
                   using alt_sem_lemma osafe
                   subgoal
                   proof -
                     assume a1: "\<forall>i. Inr i \<notin> Inl ` ODE_vars I ODE \<and> (Inr i::'c + 'c) \<notin> Inr ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (ab, bb) (sol xa)) $ i = bb $ i"
                     assume a2: "\<forall>i. Inr i \<notin> Inl ` ODE_vars I ODE \<and> (Inr i::'c + 'c) \<notin> Inr ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (ab, bb) (\<chi> i. if  i \<in> FVO ODE then sol xa $ i else ab $ i)) $ i = bb $ i"
                     assume a3: "\<forall>i. (Inr i \<in> Inl ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (ab, bb) (sol xa)) $ i = ODE_sem I ODE (sol xa) $ i) \<and> ((Inr i::'c + 'c) \<in> Inr ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (ab, bb) (sol xa)) $ i = ODE_sem I ODE (sol xa) $ i)"
                     assume a4: "\<forall>i. (Inr i \<in> Inl ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (ab, bb) (\<chi> i. if  i \<in> FVO ODE then sol xa $ i else ab $ i)) $ i = ODE_sem I ODE (\<chi> i. if  i \<in> FVO ODE then sol xa $ i else ab $ i) $ i) \<and> ((Inr i::'c + 'c) \<in> Inr ` ODE_vars I ODE \<longrightarrow> snd (mk_v I ODE (ab, bb) (\<chi> i. if  i \<in> FVO ODE then sol xa $ i else ab $ i)) $ i = ODE_sem I ODE (\<chi> i. if  i \<in> FVO ODE then sol xa $ i else ab $ i) $ i)"
                     have "ODE_sem I ODE (\<chi> c. if  c \<in> FVO ODE then sol xa $ c else ab $ c) $ i = ODE_sem I ODE (sol xa) $ i"
                       using good_interp
                       by (metis (no_types) alt_sem_lemma osafe)
                     then have "Inr i \<notin> Inl ` ODE_vars I ODE \<and> (Inr i::'c + 'c) \<notin> Inr ` ODE_vars I ODE \<or> snd (mk_v I ODE (ab, bb) (sol xa)) $ i = snd (mk_v I ODE (ab, bb) (\<chi> c. if  c \<in> FVO ODE then sol xa $ c else ab $ c)) $ i"
                       using a4 a3 by fastforce
                     then show ?thesis
                       using a2 a1 by presburger
                   qed
                   done
                 done
                 note sem = IHF[OF Iagree_refl[of I]]
                 have VA1:"(\<forall>i. Inl i \<in> FVF \<phi> \<longrightarrow>
                         fst (mk_v I ODE ((\<chi> i. if  i \<in> FVO ODE then sol 0 $ i else ab $ i), bb) (\<chi> i. if  i \<in> FVO ODE then sol x $ i else ab $ i)) $ i 
                       = fst (mk_v I ODE (ab, bb) (sol x)) $ i)"
                   and VA2: "(\<forall>i. Inr i \<in> FVF \<phi> \<longrightarrow> 
                         snd (mk_v I ODE ((\<chi> i. if  i \<in> FVO ODE then sol 0 $ i else ab $ i), bb) (\<chi> i. if  i \<in> FVO ODE then sol x $ i else ab $ i)) $ i 
                       = snd (mk_v I ODE (ab, bb) (sol x)) $ i)"
                   apply(auto) (* 2 subgoals *)
                   subgoal for i
                     using mk_v_agree[of I ODE "((\<chi> i. if  i \<in> FVO ODE then sol 0 $ i else ab $ i),bb)" "(\<chi> i. if  i \<in> FVO ODE then sol x $ i else ab $ i)"]
                     using mk_v_agree[of I ODE "(ab,bb)" "(sol x)"] ODE_vars_lr[of i I ODE]
                     unfolding Vagree_def apply (auto)
                      apply(erule allE[where x=i])+
                      apply(cases " i \<in> FVO ODE")
                       apply(auto)
                       apply(cases " i \<in> FVO ODE") (* 18 subgoals *)
                       apply(auto)
                       using ODE_vars_lr[of i I ODE] ode_to_fvo[of i I ODE]
                       apply auto
                      using all by meson
                   subgoal for i
                     using mk_v_agree[of I ODE "((\<chi> i. if  i \<in> FVO ODE then sol 0 $ i else ab $ i),bb)" "(\<chi> i. if  i \<in> FVO ODE then sol x $ i else ab $ i)"]
                     using mk_v_agree[of I ODE "(ab,bb)" "(sol x)"] ODE_vars_lr[of i I ODE]
                     unfolding Vagree_def apply (auto)
                     apply(erule allE[where x=i])+
                     apply(cases " i \<in> FVO ODE")
                      apply(auto) (*  32 subgoals *)
                      apply(cases " i \<in> FVO ODE")
                       apply(auto)
                      using ODE_vars_lr[of i I ODE] ode_to_fvo[of i I ODE]
                      apply(auto)
                      using alt_sem_lemma osafe
                      by (metis (no_types) alt_sem_lemma good_interp osafe)+
                    done               
                  assume good:"is_interp I"
                 show "mk_v I ODE (\<chi> i. if  i \<in> FVO ODE then sol 0 $ i else ab $ i, bb)
                                  (\<chi> i. if  i \<in> FVO ODE then sol x $ i else ab $ i) \<in> fml_sem I \<phi>"
                   using mk_v_agree[of I ODE "(\<chi> i. if  i \<in> FVO ODE then sol 0 $ i else ab $ i, bb)" 
                                             "(\<chi> i. if  i \<in> FVO ODE then sol x $ i else ab $ i)"]
                      mk_v_agree[of I ODE "(ab, bb)" "sol x"]
                   using sem[of "mk_v I ODE (\<chi> i. if  i \<in> FVO ODE then sol 0 $ i else ab $ i, bb) (\<chi> i. if  i \<in> FVO ODE then sol x $ i else ab $ i)"
                                "mk_v I ODE (ab, bb) (sol x)"]
                   VA1 VA2
                   allT[of x] allT[of 0]
                   unfolding Vagree_def
                   apply auto
                   using atLeastAtMost_iff mem_Collect_eq mkV t x
                   apply(auto)
                   using eqP VA sem good
                   by auto
               qed
               proof -
                 fix x i 
                 assume 
                   assms:"osafe ODE"
                   "fsafe \<phi>"
                   "0 \<le> t"
                   "(aa, ba) = mk_v I ODE (ab, bb) (sol t)"
                   "VSagree (sol 0) ab {x. (*Inl x \<in> BVO ODE \<or> *)Inl x \<in> Inl ` FVO ODE \<or> Inl x \<in> FVF \<phi>}"
                   and deriv:"\<forall>x\<in>{0..t}. (sol has_derivative (\<lambda>xa. xa *\<^sub>R ODE_sem I ODE (sol x))) (at x within {0..t})"
                   and sol:"sol \<in> {0..t} \<rightarrow> {x. mk_v I ODE (ab, bb) x \<in> fml_sem I \<phi>}"
                   and mem:"x \<in> {0..t}"
                   and good_interp:"is_interp I"
                 from deriv 
                 have xDeriv:"(sol has_derivative (\<lambda>xa. xa *\<^sub>R ODE_sem I ODE (sol x))) (at x within {0..t})"
                   using mem by blast
                 have silly1:"(\<lambda>x. \<chi> i. sol x $ i) = sol"
                   by (auto simp add: vec_eq_iff)
                 have silly2:"(\<lambda>h. \<chi> i. h * ODE_sem I ODE (sol x) $ i) = (\<lambda>xa. xa *\<^sub>R ODE_sem I ODE (sol x))"
                   by (auto simp add: vec_eq_iff)
                 from xDeriv have 
                   xDeriv':"((\<lambda>x. \<chi> i. sol x $ i) has_derivative (\<lambda>h. \<chi> i. h * ODE_sem I ODE (sol x) $ i)) (at x within {0..t})"
                   using silly1 silly2 apply auto done
                 from xDeriv have xDerivs:"\<And>j. ((\<lambda>t. sol t $ j) has_derivative (\<lambda>xa. (xa *\<^sub>R ODE_sem I ODE (sol x)) $ j)) (at x within {0..t})"
                   subgoal for j
                     using silly1 silly2 has_derivative_proj[of "(\<lambda>i. \<lambda>t. sol t $ i)" "(\<lambda> i. \<lambda>xa. (xa *\<^sub>R ODE_sem I ODE (sol x)) $ i)" "(at x within {0..t})" j]
                     apply auto
                     done
                   done
                 have neato:"\<And>\<nu>.  i \<notin> FVO ODE \<Longrightarrow> ODE_sem I ODE \<nu> $ i = 0"
                 proof (induction "ODE")
                   case (OVar x1 x2)
                   then show ?case by(cases x2,auto)
                 next
                   case (OSing x1 x2)
                   then show ?case by auto
                 next
                   case (OProd ODE1 ODE2)
                   then show ?case by auto
                 qed
                 show "((\<lambda>t. if i \<in> FVO ODE then sol t $ i else ab $ i) has_derivative
            (\<lambda>h. h *\<^sub>R ODE_sem I ODE (\<chi> i. if i \<in> FVO ODE then sol x $ i else ab $ i) $ i))
            (at x within {0..t})"
                   using assms sol mem
                   apply auto
                   apply (rule has_derivative_eq_rhs)
                    unfolding VSagree_def apply auto
                   apply(cases " i \<in> FVO ODE")
                    using xDerivs[of i] apply auto 
                    using alt_sem_lemma neato[of "(\<chi> i. if  i \<in> FVO ODE then sol x $ i else ab $ i)"] apply auto 
                  proof -
     
                   assume a1: "((\<lambda>t. sol t $ i) has_derivative (\<lambda>xa. xa * ODE_sem I ODE (sol x) $ i)) (at x within {0..t})"
                   have "\<And> r. ODE_sem (I::('a, 'b, 'c) interp) ODE (\<chi> c. if  c \<in> FVO ODE then sol r $ c else ab $ c) = ODE_sem I ODE (sol r)"
                     by (metis (no_types) alt_sem_lemma good_interp assms(1))
                   then show "((\<lambda>r. sol r $ i) has_derivative (\<lambda>r. r * ODE_sem I ODE (\<chi> c. if  c \<in> FVO ODE then sol x $ c else ab $ c) $ i)) (at x within {0..t})"
                     using a1 by presburger
                 qed
               qed
               proof -
                 fix aa ba bb sol t
                 assume osafe:"osafe ODE"
                   and fsafe:"fsafe \<phi>"
                   and t:"0 \<le> t"
                   and aaba:"(aa, ba) = mk_v I ODE (sol 0, bb) (sol t)"
                   and sol:"(sol solves_ode (\<lambda>a. ODE_sem I ODE)) {0..t} {x. mk_v I ODE (sol 0, bb) x \<in> fml_sem I \<phi>}"
                 show"\<exists>sola ta. mk_v I ODE (sol 0, bb) (sol t) = mk_v I ODE (sol 0, bb) (sola ta) \<and>
                           0 \<le> ta \<and>
                           (sola solves_ode (\<lambda>a. ODE_sem I ODE)) {0..ta} {x. mk_v I ODE (sol 0, bb) x \<in> fml_sem I \<phi>} \<and>
                           VSagree (sola 0) (sol 0) {x. (*Inl x \<in> BVO ODE \<or> *)Inl x \<in> Inl ` FVO ODE \<or> Inl x \<in> FVF \<phi>}"   
                   apply(rule exI[where x=sol])
                   apply(rule exI[where x=t])
                   using fsafe t aaba sol apply auto
                   unfolding VSagree_def by auto
                 qed
               done
             done

           show "\<forall>I J.  is_interp I \<longrightarrow> is_interp J \<longrightarrow> coincide_hp (EvolveODE ODE P) I J \<and> ode_sem_equiv (EvolveODE ODE P) I"
                proof (rule allI | rule impI)+
                  fix I J::"('a,'b,'c) interp"
                  assume goodI:"is_interp I" assume goodJ:"is_interp J"
                from equiv[of I] 
                have equivI:"
            {(\<nu>, mk_v I ODE \<nu> (sol t)) | \<nu> sol t.
                t \<ge> 0 \<and>
                (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu> x \<in> fml_sem I P} \<and>
                VSagree (sol 0) (fst \<nu>) {x | x. Inl x \<in> FVP (EvolveODE ODE P)}} = 
            {(\<nu>, mk_v I ODE \<nu> (sol t)) | \<nu> sol t.
                t \<ge> 0 \<and>
                (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu> x \<in> fml_sem I P} \<and>
                 (sol 0) = (fst \<nu>)}"
                  unfolding ode_sem_equiv_def using osafe fsafe goodI goodJ by blast
                
                from equiv[of J] 
                have equivJ:"
            {(\<nu>, mk_v J ODE \<nu> (sol t)) | \<nu> sol t.
                t \<ge> 0 \<and>
                (sol solves_ode (\<lambda>_. ODE_sem J ODE)) {0..t} {x. mk_v J ODE \<nu> x \<in> fml_sem J P} \<and>
                VSagree (sol 0) (fst \<nu>) {x | x. Inl x \<in> FVP (EvolveODE ODE P)}} = 
            {(\<nu>, mk_v J ODE \<nu> (sol t)) | \<nu> sol t.
                t \<ge> 0 \<and>
                (sol solves_ode (\<lambda>_. ODE_sem J ODE)) {0..t} {x. mk_v J ODE \<nu> x \<in> fml_sem J P} \<and>
                (sol 0) = (fst \<nu>)}"
                  unfolding ode_sem_equiv_def using osafe fsafe goodI goodJ  by blast
                from equivI 
                have alt_ode_semI:"prog_sem I (EvolveODE ODE P) = 
                  {(\<nu>, mk_v I ODE \<nu> (sol t)) | \<nu> sol t.
                t \<ge> 0 \<and>
                (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu> x \<in> fml_sem I P} \<and>
                VSagree (sol 0) (fst \<nu>) {x | x. Inl x \<in> FVP (EvolveODE ODE P)}}" by auto
                
                from equivJ 
                have alt_ode_semJ:"prog_sem J (EvolveODE ODE P) = 
                  {(\<nu>, mk_v J ODE \<nu> (sol t)) | \<nu> sol t.
                t \<ge> 0 \<and>
                (sol solves_ode (\<lambda>_. ODE_sem J ODE)) {0..t} {x. mk_v J ODE \<nu> x \<in> fml_sem J P} \<and>
                VSagree (sol 0) (fst \<nu>) {x | x. Inl x \<in> FVP (EvolveODE ODE P)}}" by auto
                
                have co_hp:"coincide_hp (EvolveODE ODE P) I J"
                  apply(unfold coincide_hp_def)
                  using prog_sem.simps
                  apply (auto simp del: prog_sem.simps(9) simp add: alt_ode_semI  alt_ode_semJ)
                  proof -
                fix a b aa ba ab bb V sol t
                 from IH have IHF:"\<forall>a b aa ba . is_interp I \<longrightarrow> is_interp J \<longrightarrow> Iagree I J (SIGF P) \<longrightarrow> Vagree (a, b) (aa, ba) (FVF P) \<longrightarrow> ((a, b) \<in> fml_sem I P) = ((aa, ba) \<in> fml_sem J P)"
                   unfolding coincide_fml_def by blast
                 assume IA:"Iagree I J (SIGF P \<union> {Inl x |x. Inl x \<in> SIGO ODE} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE})"
                 and VA:"Vagree (a, b) (aa, ba) V"
                 and Osub:"Inl ` FVO ODE \<subseteq> V"
                 and Fsub:"FVF P \<subseteq> V"
                 and veq:"(ab, bb) = mk_v I ODE (a, b) (sol t)"
                 and t:"0 \<le> t"
                 and sol:"(sol solves_ode (\<lambda>a. ODE_sem I ODE)) {0..t} {x. mk_v I ODE (a, b) x \<in> fml_sem I P}"
                 and VSA:"VSagree (sol 0) a  {uu. (*Inl uu \<in> BVO ODE \<or> *)Inl uu \<in> Inl ` FVO ODE \<or> Inl uu \<in> FVF P}"
                 have semBVsub:"(semBV I ODE) \<subseteq> BVO ODE" 
                 proof (induction ODE)
                   case (OVar x1 x2)
                   then show ?case apply(cases x2,auto)
                     using goodI goodJ unfolding is_interp_def by auto
                 next
                   case (OSing x1 x2)
                   then show ?case by auto
                 next
                   case (OProd ODE1 ODE2)
                   then show ?case by auto
                 qed
                 have MBVBVsub:"(Inl ` ODE_dom ODE \<union> Inr ` ODE_dom ODE) \<subseteq> BVO ODE"
                   apply(induction ODE)
                   by auto
                from sol 
                have  solSem:"\<And>x. 0 \<le> x \<Longrightarrow> x \<le> t \<Longrightarrow> mk_v I ODE (a, b) (sol x) \<in> fml_sem I P"
                  and solDeriv:"\<And>x. 0 \<le> x \<Longrightarrow> x \<le> t \<Longrightarrow> (sol has_vector_derivative ODE_sem I ODE (sol x)) (at x within {0..t})"
                  unfolding solves_ode_def has_vderiv_on_def by auto
                have SIGFsub:"(SIGF P) \<subseteq> (SIGF P \<union> {Inl x |x. Inl x \<in> SIGO ODE} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE})" by auto
                from IA have IAP:"Iagree I J (SIGF P)"
                  using Iagree_sub[OF SIGFsub] by auto
                from IHF have IH':
                  "\<forall>a b aa ba. Vagree (a, b) (aa, ba) (FVF P) \<longrightarrow> ((a, b) \<in> fml_sem I P) = ((aa, ba) \<in> fml_sem J P)"
                  using IAP goodI goodJ by blast
                from VA 
                have VAOV:"Vagree (a,b) (aa,ba) (Inl ` FVO ODE)"
                  using agree_sub[OF Osub] by auto
                have ag:"\<And>s. Vagree (mk_v I ODE (a, b) (sol s)) (a, b) (- semBV I ODE)" 
                     "\<And>s. Vagree (mk_v I ODE (a, b) (sol s)) (mk_xode I ODE (sol s)) (semBV I ODE)"
                     "\<And>s. Vagree (mk_v J ODE (aa, ba) (sol s)) (aa, ba) (- semBV J ODE)"
                     "\<And>s. Vagree (mk_v J ODE (aa, ba) (sol s)) (mk_xode J ODE (sol s)) (semBV J ODE)"
                  subgoal for s using mk_v_agree[of I ODE "(a,b)" "sol s"] by auto
                  subgoal for s using mk_v_agree[of I ODE "(a,b)" "sol s"] by auto
                  subgoal for s using mk_v_agree[of J ODE "(aa,ba)" "sol s"] by auto
                  subgoal for s using mk_v_agree[of J ODE "(aa,ba)" "sol s"] by auto
                  done  
                have sem_sub_BVO:"\<And>I::('a,'b,'c) interp. is_interp I \<Longrightarrow> semBV I ODE \<subseteq> BVO ODE"
                 proof (induction ODE)
                   case (OVar x1 x2)
                   then show ?case apply(cases x2,auto)
                     using goodI goodJ unfolding is_interp_def by auto
                 next
                   case (OSing x1 x2)
                   then show ?case by auto
                 next
                   case (OProd ODE1 ODE2)
                    assume IH1:"\<And>I::('a,'b,'c) interp. is_interp I \<Longrightarrow> semBV I ODE1 \<subseteq> BVO ODE1"
                    assume IH2:"\<And>I::('a,'b,'c) interp. is_interp I \<Longrightarrow> semBV I ODE2 \<subseteq> BVO ODE2"
                    assume good:"is_interp I"
                   then show ?case using IH1[OF good] IH2[OF good] by auto
                 qed
                have MBV_sub_sem:"\<And>I. (Inl ` ODE_dom ODE \<union> Inr ` ODE_dom ODE) \<subseteq> semBV I ODE"
                  subgoal for I by (induction ODE, auto) done
                have ag_BVO:
                  "\<And>s. Vagree (mk_v I ODE (a, b) (sol s)) (a, b) (- BVO ODE)"
                  "\<And>s. Vagree (mk_v J ODE (aa, ba) (sol s)) (aa, ba) (- BVO ODE)"
                  using ag(1) ag(3)  sem_sub_BVO[of I] sem_sub_BVO[of J] agree_sub  goodI goodJ by blast+
                have ag_semBV:
                     "\<And>s. Vagree (mk_v I ODE (a, b) (sol s)) (mk_xode I ODE (sol s)) (Inl ` ODE_dom ODE \<union> Inr ` ODE_dom ODE)"
                     "\<And>s. Vagree (mk_v J ODE (aa, ba) (sol s)) (mk_xode J ODE (sol s)) (Inl ` ODE_dom ODE \<union> Inr ` ODE_dom ODE)"
                  using ag(2) ag(4)  MBV_sub_sem[of I] MBV_sub_sem[of J]
                  by (simp add: agree_sub)+
                have IOsub:"({Inl x |x. Inl x \<in> SIGO ODE} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE}) \<subseteq> (SIGF P \<union> {Inl x |x. Inl x \<in> SIGO ODE} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE})"
                  by auto
                from IA 
                have IAO:"Iagree I J ({Inl x |x. Inl x \<in> SIGO ODE} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE})"
                  using Iagree_sub[OF IOsub] by auto
                have IOsub':"({Inr (Inr x) |x. Inr x \<in> SIGO ODE}) \<subseteq> ({Inl x |x. Inl x \<in> SIGO ODE} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO ODE})"
                  by auto
                from IAO
                have IAO':"Iagree I J ({Inr (Inr x) |x. Inr x \<in> SIGO ODE})"
                  using Iagree_sub[OF IOsub'] by auto
                have VAsol:"\<And>s \<nu>'. Vagree ((sol s), \<nu>') ((sol s), \<nu>')  (Inl `FVO ODE)" unfolding Vagree_def by auto
                have Osem:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> ODE_sem I ODE (sol s) = ODE_sem J ODE (sol s)"
                  subgoal for s
                    using coincidence_ode[OF goodI goodJ osafe VAsol[of s] IAO] by auto
                  done
                from Osem
                have Oag:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> VSagree (ODE_sem I ODE (sol s)) (ODE_sem J ODE (sol s)) {x. Inr x \<in> BVO ODE}"
                  unfolding VSagree_def by auto
                from Osem
                have Oagsem:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> VSagree (ODE_sem I ODE (sol s)) (ODE_sem J ODE (sol s)) {x. Inr x \<in> (semBV I ODE)}"
                  unfolding VSagree_def by auto
                from Osem
                have halp:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow>  Vagree (mk_xode I ODE (sol s)) (mk_xode J ODE (sol s)) (semBV I ODE)"
                  apply(auto)
                  using Oag unfolding Vagree_def VSagree_def by blast
                then have halpp:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> Vagree (sol s, ODE_sem I ODE (sol s)) (sol s, ODE_sem J ODE (sol s)) (semBV I ODE)"
                  by auto
                have neat:"\<And>ODE. Iagree I J ({Inr (Inr x) |x. Inr x \<in> SIGO ODE}) \<Longrightarrow> semBV I ODE = semBV J ODE"
                  subgoal for ODE
                  proof (induction ODE)
                    case (OVar x)
                    then show ?case unfolding Iagree_def by auto
                  next
                    case (OSing x1a x2)
                    then show ?case by auto
                  next
                    case (OProd ODE1 ODE2)
                    assume IH1:"Iagree I J {Inr (Inr x) |x. Inr x \<in> SIGO ODE1} \<Longrightarrow> semBV I ODE1 = semBV J ODE1"
                    assume IH2:"Iagree I J {Inr (Inr x) |x. Inr x \<in> SIGO ODE2} \<Longrightarrow> semBV I ODE2 = semBV J ODE2"
                    assume agree:"Iagree I J {Inr (Inr x) |x. Inr x \<in> SIGO (OProd ODE1 ODE2)}"
                    from agree have agree1:"Iagree I J {Inr (Inr x) |x. Inr x \<in> SIGO ( ODE1 )}" and agree2:"Iagree I J {Inr (Inr x) |x. Inr x \<in> SIGO ( ODE2)}"
                      unfolding Iagree_def by auto
                    show ?case using IH1[OF agree1] IH2[OF agree2] by auto
                  qed
                  done
                note semBVeq = neat[OF IAO']
                          then have halpp':"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> Vagree (mk_v I ODE (a, b) (sol s)) (mk_v J ODE (aa, ba) (sol s)) (semBV I ODE)"
                  subgoal for s using ag[of s] ag_semBV[of s] Oagsem agree_trans semBVeq
                      unfolding Vagree_def by (auto simp add: semBVeq Osem)
                  done
                have VAbar:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> Vagree (mk_v I ODE (a, b) (sol s)) (mk_v J ODE (aa, ba) (sol s)) (V \<inter> (-(semBV I ODE)))"
                  subgoal for s
                    apply(unfold Vagree_def)
                    apply(rule conjI | rule allI)+
                    subgoal for i
                      apply auto
                      using VA ag[of s] semBVeq unfolding Vagree_def apply auto 
                      by (metis Un_iff)
                      
                    apply(rule allI)+
                    subgoal for i
                      using VA ag[of s] semBVeq unfolding Vagree_def by auto
                    done
                  done
                have VAfoo:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> Vagree (mk_v I ODE (a, b) (sol s)) (mk_v J ODE (aa, ba) (sol s)) V"
                  using agree_union[OF halpp' VAbar] apply (auto simp add: Vagree_def)
                  by blast
                have duhSub:"FVF P \<subseteq> UNIV" by auto
                from VAfoo 
                have VA'foo:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> Vagree (mk_v I ODE (a, b) (sol s)) (mk_v J ODE (aa, ba) (sol s)) V"
                  using agree_sub[OF duhSub] by auto
                then have VA''foo:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> Vagree (mk_v I ODE (a, b) (sol s)) (mk_v J ODE (aa, ba) (sol s)) (FVF P)"
                  using agree_sub[OF Fsub] by auto
                from VA''foo IH' 
                have fmlSem:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> (mk_v I ODE (a, b) (sol s)) \<in> fml_sem I P \<longleftrightarrow> (mk_v J ODE (aa, ba) (sol s)) \<in> fml_sem J P"
                  using IAP coincide_fml_def hpsafe_Evolve.IH goodI goodJ by blast
                from VA 
                have VAO:"Vagree (a, b) (aa, ba) (Inl `FVO ODE)" 
                  using agree_sub[OF Osub] by auto
                have sol':"(sol solves_ode (\<lambda>_. ODE_sem J ODE)) {0..t} {x. mk_v J ODE (aa, ba) x \<in> fml_sem J P}"
                  apply(auto simp add: solves_ode_def has_vderiv_on_def)
                  subgoal for s
                    using solDeriv[of s] Osem[of s] by auto
                  subgoal for s
                    using solSem[of s] fmlSem[of s] by auto
                  done
                have VSA':"VSagree (sol 0) aa {uu. (*Inl uu \<in> BVO ODE \<or> *)Inl uu \<in> Inl `FVO ODE \<or> Inl uu \<in> FVF P}"
                  using VSA VA Osub unfolding VSagree_def Vagree_def (*ovsub *)
                  apply auto
                  using Osub (*apply blast
                  using*) Fsub by blast
                show 
                  " \<exists>ab bb. (\<exists>sol t. (ab, bb) = mk_v J ODE (aa, ba) (sol t) \<and>
                                  0 \<le> t \<and>
                                  (sol solves_ode (\<lambda>a. ODE_sem J ODE)) {0..t} {x. mk_v J ODE (aa, ba) x \<in> fml_sem J P} \<and>
                                  VSagree (sol 0) aa {uu. (*Inl uu \<in> BVO ODE \<or> *)Inl uu \<in> Inl `FVO ODE \<or> Inl uu \<in> FVF P}) \<and>
                         Vagree (mk_v I ODE (a, b) (sol t)) (ab, bb) (Inl ` ODE_dom ODE \<union> Inr ` ODE_dom ODE \<union> V) "
                  apply(rule exI[where x="fst (mk_v J ODE (aa, ba) (sol t))"])
                  apply(rule exI[where x="snd (mk_v J ODE (aa, ba) (sol t))"])
                  apply(rule conjI)
                  subgoal
                    apply(rule exI[where x="sol"])
                    apply(rule exI[where x=t])
                    apply(rule conjI)
                    subgoal
                      apply(auto)
                      done
                    subgoal
                      apply(rule conjI)
                      subgoal by (rule t)
                      subgoal
                        apply(rule conjI)
                        subgoal by (rule sol')
                        subgoal by (rule VSA')
                      done
                    done
                  done
                apply(auto)
                using mk_v_agree[of I ODE "(a,b)" "(sol t)"]
                      mk_v_agree[of J ODE "(aa,ba)" "(sol t)"]
                using agree_refl t VA'foo Osub Un_absorb1 
                by (smt MBV_sub_sem agree_sub agree_union halpp')
              qed
              show "coincide_hp (EvolveODE ODE P) I J \<and> ode_sem_equiv (EvolveODE ODE P) I" using co_hp equiv[of I] 
                using goodI goodJ by auto
    qed
  qed
next
  case (hpsafe_Choice a b) 
  then show "?case" 
proof (auto simp only: coincide_hp'_def coincide_hp_def)
  fix I J::"('a,'b,'c) interp" and \<nu>1 \<nu>1' \<nu>2 \<nu>2' \<mu> \<mu>' V
  assume safe:"hpsafe a"
     "hpsafe b"
     and preIH1:"\<forall>I J. is_interp I \<longrightarrow>
             is_interp J \<longrightarrow>
             (\<forall>\<nu> \<nu>' \<mu> V.
                 Iagree I J (SIGP a) \<longrightarrow>
                 Vagree \<nu> \<nu>' V \<longrightarrow> FVP a \<subseteq> V \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I a \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J a \<and> Vagree \<mu> \<mu>' (MBV a \<union> V))) \<and>
             ode_sem_equiv a I"
     and preIH2:"\<forall>I J. is_interp I \<longrightarrow>
             is_interp J \<longrightarrow>
             (\<forall>\<nu> \<nu>' \<mu> V.
                 Iagree I J (SIGP b) \<longrightarrow>
                 Vagree \<nu> \<nu>' V \<longrightarrow> FVP b \<subseteq> V \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I b \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J b \<and> Vagree \<mu> \<mu>' (MBV b \<union> V))) \<and>
             ode_sem_equiv b I"
    and IA:"Iagree I J (SIGP (a \<union>\<union> b))"
    and VA:"Vagree (\<nu>1, \<nu>1') (\<nu>2, \<nu>2') V"
    and sub:"FVP (a \<union>\<union> b) \<subseteq> V"
    and sem:"((\<nu>1, \<nu>1'), (\<mu>, \<mu>')) \<in> prog_sem I (a \<union>\<union> b)"
    and goodI:"is_interp I"
    and goodJ:"is_interp J"
  hence eitherSem:"((\<nu>1, \<nu>1'), (\<mu>, \<mu>')) \<in> prog_sem I a \<or> ((\<nu>1, \<nu>1'), (\<mu>, \<mu>')) \<in> prog_sem I b"
    by auto
  from preIH1 have IH1:
     "(\<forall>\<nu> \<nu>' \<mu> V.
        Iagree I J (SIGP a) \<longrightarrow>
        Vagree \<nu> \<nu>' V \<longrightarrow> FVP a \<subseteq> V \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I a \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J a \<and> Vagree \<mu> \<mu>' (MBV a \<union> V)))
        \<and> ode_sem_equiv a I" using goodI goodJ by(auto)
    from preIH2 have IH2:" (\<forall>\<nu> \<nu>' \<mu> V.
        Iagree I J (SIGP b) \<longrightarrow>
        Vagree \<nu> \<nu>' V \<longrightarrow> FVP b \<subseteq> V \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I b \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J b \<and> Vagree \<mu> \<mu>' (MBV b \<union> V)))
        \<and> ode_sem_equiv b I" using goodI goodJ by(auto)
  have Ssub:"(SIGP a) \<subseteq> SIGP (a \<union>\<union> b)" "(SIGP b) \<subseteq> SIGP (a \<union>\<union> b)" 
    unfolding SIGP.simps by auto
  have IA1:"Iagree I J (SIGP a)" and IA2:"Iagree I J (SIGP b)" 
    using IA Iagree_sub[OF Ssub(1)] Iagree_sub[OF Ssub(2)] by auto
  from sub have sub1:"FVP a \<subseteq> V" and sub2:"FVP b \<subseteq> V" by auto
  then
  show "\<exists>\<mu>''. ((\<nu>2, \<nu>2'), \<mu>'') \<in> prog_sem J (a \<union>\<union> b) \<and> Vagree (\<mu>, \<mu>') \<mu>'' (MBV (a \<union>\<union> b) \<union> V)" 
    proof (cases "((\<nu>1, \<nu>1'), (\<mu>, \<mu>')) \<in> prog_sem I a")
      case True
      then obtain \<mu>'' where prog_sem:"((\<nu>2,\<nu>2'), \<mu>'') \<in> prog_sem J a" and agree:"Vagree (\<mu>, \<mu>') \<mu>'' (MBV a \<union> V)" 
        using IH1 VA sub1 IA1 by blast
      from agree have agree':"Vagree (\<mu>, \<mu>') \<mu>'' (MBV (a \<union>\<union> b) \<union> V)"
        unfolding Vagree_def MBV.simps by auto
      from prog_sem have prog_sem':"((\<nu>2,\<nu>2'), \<mu>'') \<in> prog_sem J (a \<union>\<union> b)"
        unfolding prog_sem.simps by blast
      from agree' and prog_sem' show ?thesis by blast
    next
      case False
      then have sem2:"((\<nu>1, \<nu>1'), (\<mu>, \<mu>')) \<in> prog_sem I b" using eitherSem by blast
      then obtain \<mu>'' where prog_sem:"((\<nu>2,\<nu>2'), \<mu>'') \<in> prog_sem J b" and agree:"Vagree (\<mu>, \<mu>') \<mu>'' (MBV b \<union> V)" 
        using IH2 VA sub2 IA2 by blast
      from agree have agree':"Vagree (\<mu>, \<mu>') \<mu>'' (MBV (a \<union>\<union> b) \<union> V)"
        unfolding Vagree_def MBV.simps by auto
      from prog_sem have prog_sem':"((\<nu>2,\<nu>2'), \<mu>'') \<in> prog_sem J (a \<union>\<union> b)"
        unfolding prog_sem.simps by blast
      from agree' and prog_sem' show ?thesis by blast
    qed
  next
    fix I J::"('a,'b,'c) interp"
    assume preIHs:"\<forall>I J. is_interp I \<longrightarrow>
                 is_interp J \<longrightarrow>
                 (\<forall>\<nu> \<nu>' \<mu> V.
                     Iagree I J (SIGP a) \<longrightarrow>
                     Vagree \<nu> \<nu>' V \<longrightarrow> FVP a \<subseteq> V \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I a \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J a \<and> Vagree \<mu> \<mu>' (MBV a \<union> V))) \<and>
                 ode_sem_equiv a I"
           "\<forall>I J. is_interp I \<longrightarrow>
                 is_interp J \<longrightarrow>
                 (\<forall>\<nu> \<nu>' \<mu> V.
                     Iagree I J (SIGP b) \<longrightarrow>
                     Vagree \<nu> \<nu>' V \<longrightarrow> FVP b \<subseteq> V \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I b \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J b \<and> Vagree \<mu> \<mu>' (MBV b \<union> V))) \<and>
                 ode_sem_equiv b I"
    and goodI:"is_interp I"
    and goodJ:"is_interp J"
    then show "ode_sem_equiv (a \<union>\<union> b) I"
      unfolding ode_sem_equiv_def by auto
  qed 
next
  case (hpsafe_Sequence a b) then show "?case"
    apply (unfold coincide_hp'_def coincide_hp_def)
    apply (rule allI | rule impI)+
    apply (rule conjI)
     prefer 2 subgoal unfolding ode_sem_equiv_def  by auto
    apply(unfold prog_sem.simps SIGP.simps FVP.simps )
    apply(rule allI)+
    apply(auto)
    subgoal for I J  \<nu>2 \<nu>2' V \<nu>1 \<nu>1' \<mu> \<mu>' \<omega> \<omega>' 
    proof -
      assume goodI:"is_interp I" assume goodJ:"is_interp J"
      assume safe:"hpsafe a" "hpsafe b"
      assume "\<forall>I. is_interp I \<longrightarrow>
        (\<forall>J. is_interp J \<longrightarrow>
             (Iagree I J (SIGP a) \<longrightarrow>
              (\<forall>aa b ab ba ac bb V.
                  Vagree (aa, b) (ab, ba) V \<longrightarrow>
                  FVP a \<subseteq> V \<longrightarrow>
                  ((aa, b), ac, bb) \<in> prog_sem I a \<longrightarrow> (\<exists>aa b. ((ab, ba), aa, b) \<in> prog_sem J a \<and> Vagree (ac, bb) (aa, b) (MBV a \<union> V)))) \<and>
             ode_sem_equiv a I)"
      hence IH1':"\<And>aa b ab ba ac bb V.
         Iagree I J (SIGP a) \<Longrightarrow>
         Vagree (aa, b) (ab, ba) V \<Longrightarrow>
         FVP a \<subseteq> V \<Longrightarrow> ((aa, b), ac, bb) \<in> prog_sem I a \<Longrightarrow> (\<exists>aa b. ((ab, ba), aa, b) \<in> prog_sem J a \<and> Vagree (ac, bb) (aa, b) (MBV a \<union> V))"
        using goodI goodJ by auto
      note IH1 =  IH1'[of \<nu>1 \<nu>1' \<nu>2 \<nu>2' V \<mu> \<mu>']
      assume IH2''':"\<forall>I. is_interp I \<longrightarrow>
        (\<forall>J. is_interp J \<longrightarrow>
             (Iagree I J (SIGP b) \<longrightarrow>
              (\<forall>a ba aa bb ab bc V.
                  Vagree (a, ba) (aa, bb) V \<longrightarrow>
                  FVP b \<subseteq> V \<longrightarrow>
                  ((a, ba), ab, bc) \<in> prog_sem I b \<longrightarrow> (\<exists>a ba. ((aa, bb), a, ba) \<in> prog_sem J b \<and> Vagree (ab, bc) (a, ba) (MBV b \<union> V)))) \<and>
             ode_sem_equiv b I) "
      then have IH2'':"
        (Iagree I J (SIGP b) \<longrightarrow> (\<forall>a ba aa bb ab bc V.
         Vagree (a, ba) (aa, bb) V \<longrightarrow>
         FVP b \<subseteq> V \<longrightarrow> ((a, ba), ab, bc) \<in> prog_sem I b \<longrightarrow> (\<exists>a ba. ((aa, bb), a, ba) \<in> prog_sem J b \<and> Vagree (ab, bc) (a, ba) (MBV b \<union> V))))
         \<and> ode_sem_equiv b I" using goodI goodJ by auto
      assume IAab:"Iagree I J (SIGP a \<union> SIGP b)"
      have IAsubs:"SIGP a \<subseteq> (SIGP a \<union> SIGP b)" "SIGP b \<subseteq> (SIGP a \<union> SIGP b)" by auto
      from IAab have  IA:"Iagree I J (SIGP a)" "Iagree I J (SIGP b)" using Iagree_sub[OF IAsubs(1)] Iagree_sub[OF IAsubs(2)] by auto
      from IH2'' have IH2':"\<And>a ba aa bb ab bc V .
         Iagree I J (SIGP b) \<Longrightarrow>
         Vagree (a, ba) (aa, bb) V \<Longrightarrow>
         FVP b \<subseteq> V \<Longrightarrow> ((a, ba), ab, bc) \<in> prog_sem I b \<Longrightarrow> (\<exists>a ba. ((aa, bb), a, ba) \<in> prog_sem J b \<and> Vagree (ab, bc) (a, ba) (MBV b \<union> V))"
        using IA by auto
      assume VA:"Vagree (\<nu>1, \<nu>1') (\<nu>2, \<nu>2') V"
      assume sub:"FVP a \<subseteq> V" "FVP b - MBV a \<subseteq> V"
        hence sub':"FVP a \<subseteq> V" by auto
      assume sem:"((\<nu>1, \<nu>1'), (\<mu>, \<mu>')) \<in> prog_sem I a"
        "((\<mu>, \<mu>'), (\<omega>, \<omega>')) \<in> prog_sem I b"
      obtain \<omega>1 \<omega>1' where sem1:"((\<nu>2, \<nu>2'), (\<omega>1, \<omega>1')) \<in> prog_sem J a" and VA1:"Vagree (\<mu>, \<mu>') (\<omega>1, \<omega>1') (MBV a \<union> V)" 
        using IH1[OF IA(1) VA  sub' sem(1)] by auto
      note IH2 =  IH2'[of \<mu> \<mu>' \<omega>1 \<omega>1' " MBV a \<union> V" \<omega> \<omega>']
      have sub2:"FVP b \<subseteq> MBV a \<union> V" using sub by auto
      obtain \<omega>2 \<omega>2' where sem2:"((\<omega>1, \<omega>1'), (\<omega>2, \<omega>2')) \<in> prog_sem J b" and VA2:"Vagree (\<omega>, \<omega>') (\<omega>2, \<omega>2') (MBV b \<union> (MBV a \<union> V))"
        using IH2[OF IA(2) VA1 sub2 sem(2)] by auto
      show "\<exists>ab bb. ((\<nu>2, \<nu>2'), (ab, bb)) \<in> prog_sem J a O prog_sem J b \<and> Vagree (\<omega>, \<omega>') (ab, bb) (MBV a \<union> MBV b \<union> V)"
        using sem1 sem2 VA1 VA2
        by (metis (no_types, lifting) Un_assoc Un_left_commute relcomp.relcompI)
    qed
  done
next
  case (hpsafe_Loop a) then show "?case" 
    apply(unfold coincide_hp'_def coincide_hp_def)
    apply(rule allI | rule impI)+
    apply(rule conjI)
     prefer 2 subgoal unfolding ode_sem_equiv_def by auto
    apply(rule allI | rule impI)+
    apply(unfold prog_sem.simps FVP.simps MBV.simps SIGP.simps)
    subgoal for I J \<nu> \<nu>' \<mu> V
    proof -
      assume safe:"hpsafe a"
      assume goodI:"is_interp I" and goodJ:"is_interp J"
      assume IH':" \<forall>I J. is_interp I \<longrightarrow>
          is_interp J \<longrightarrow>
          (\<forall>\<nu> \<nu>' \<mu> V.
              Iagree I J (SIGP a) \<longrightarrow>
              Vagree \<nu> \<nu>' V \<longrightarrow> FVP a \<subseteq> V \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I a \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J a \<and> Vagree \<mu> \<mu>' (MBV a \<union> V))) \<and>
          ode_sem_equiv a I"
      then have IH:"(\<forall>\<nu> \<nu>' \<mu> V.
              Iagree I J (SIGP a) \<longrightarrow>
              Vagree \<nu> \<nu>' V \<longrightarrow> FVP a \<subseteq> V \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I a \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J a \<and> Vagree \<mu> \<mu>' (MBV a \<union> V))) \<and>
          ode_sem_equiv a I" using goodI goodJ by auto
      assume agree:"Iagree I J (SIGP a)"
      assume VA:"Vagree \<nu> \<nu>' V"
      assume sub:"FVP a \<subseteq> V"
      have "(\<nu>, \<mu>) \<in> (prog_sem I a)\<^sup>* \<Longrightarrow> (\<And>\<nu>'. Vagree \<nu> \<nu>' V \<Longrightarrow> \<exists>\<mu>'. (\<nu>', \<mu>') \<in> (prog_sem J a)\<^sup>* \<and> Vagree \<mu> \<mu>' ({} \<union> V))"
        apply(induction rule: converse_rtrancl_induct)
         apply(auto)
        subgoal for \<omega> \<omega>' s s' v v'
        proof -
          assume sem1:"((\<omega>, \<omega>'), (s, s')) \<in> prog_sem I a"
            and sem2:"((s, s'), \<mu>) \<in> (prog_sem I a)\<^sup>*"
            and IH2:"\<And>v v'. (Vagree (s, s') (v,v') V \<Longrightarrow> \<exists>ab ba. ((v,v'), (ab, ba)) \<in> (prog_sem J a)\<^sup>* \<and> Vagree \<mu> (ab, ba) V)"
            and VA:"Vagree (\<omega>, \<omega>') (v,v') V"
          obtain s'' where sem'':"((v, v'), s'') \<in> prog_sem J a" and VA'':"Vagree (s,s') s'' (MBV a \<union> V)"
            using IH agree VA sub sem1 agree_refl by blast
          then obtain s'1 and s'2 where sem'':"((v, v'), (s'1, s'2)) \<in> prog_sem J a" and VA'':"Vagree (s,s') (s'1, s'2) (MBV a \<union> V)"
            using IH agree VA sub sem1 agree_refl by (cases "s''", blast)
          from VA'' have VA''V:"Vagree (s,s') (s'1, s'2) V" 
            using agree_sub by blast
          note IH2' = IH2[of s'1 s'2]
          note IH2'' = IH2'[OF VA''V]
          then obtain ab and ba where  sem''':"((s'1, s'2), (ab, ba)) \<in> (prog_sem J a)\<^sup>*" and VA''':"Vagree \<mu> (ab, ba) V"
              using  IH2'' by auto
          from sem'' sem''' have sem:"((v, v'), (ab, ba)) \<in> (prog_sem J a)\<^sup>*" by auto
          show "\<exists>\<mu>'1 \<mu>'2. ((v, v'), (\<mu>'1, \<mu>'2)) \<in> (prog_sem J a)\<^sup>* \<and> Vagree \<mu> (\<mu>'1, \<mu>'2) V"
            using sem VA''' by blast
          qed
        done
      then show "(\<nu>, \<mu>) \<in> (prog_sem I a)\<^sup>* \<Longrightarrow>  Vagree \<nu> \<nu>' V \<Longrightarrow> \<exists>\<mu>'. (\<nu>', \<mu>') \<in> (prog_sem J a)\<^sup>* \<and> Vagree \<mu> \<mu>' ({} \<union> V)"
        by auto
    qed
  done
next
  case (fsafe_Geq t1 t2) 
  then have safe:"dsafe t1" "dsafe t2" by auto
  have almost:"\<And>\<nu> \<nu>'. \<And> I J :: ('a, 'b, 'c) interp. Iagree I J (SIGF (Geq t1 t2)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVF (Geq t1 t2)) \<Longrightarrow> (\<nu> \<in> fml_sem I (Geq t1 t2)) = (\<nu>' \<in> fml_sem J (Geq t1 t2))" 
  proof -
    fix \<nu> \<nu>'  and I J :: "('a, 'b, 'c) interp"
    assume IA:"Iagree I J (SIGF (Geq t1 t2))"
    hence IAs:"Iagree I J {Inl x | x. x \<in> (SIGT t1)}"
              "Iagree I J {Inl x | x. x \<in> (SIGT t2)}" 
      unfolding SIGF.simps Iagree_def by auto
    assume VA:"Vagree \<nu> \<nu>' (FVF (Geq t1 t2))"
    hence VAs:"Vagree \<nu> \<nu>' (FVT t1)" "Vagree \<nu> \<nu>' (FVT t2)"
      unfolding FVF.simps Vagree_def by auto
    have sem1:"dterm_sem I t1 \<nu> = dterm_sem J t1 \<nu>'"
      by (auto simp add: coincidence_dterm'[OF safe(1) VAs(1) IAs(1)])
    have sem2:"dterm_sem I t2 \<nu> = dterm_sem J t2 \<nu>'"
      by (auto simp add: coincidence_dterm'[OF safe(2) VAs(2) IAs(2)])
    show "(\<nu> \<in> fml_sem I (Geq t1 t2)) = (\<nu>' \<in> fml_sem J (Geq t1 t2))"
      by (simp add: sem1 sem2)
  qed
  show "?case" using almost unfolding coincide_fml_def by blast
next
  case (fsafe_Prop args p)
    then have safes:"\<And>arg. arg \<in> range args \<Longrightarrow> dsafe arg" using dfree_is_dsafe by auto
    have almost:"\<And>\<nu> \<nu>'. \<And> I J::('a, 'b, 'c) interp. Iagree I J (SIGF (Prop p args)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVF (Prop p args)) \<Longrightarrow> (\<nu> \<in> fml_sem I (Prop p args)) = (\<nu>' \<in> fml_sem J (Prop p args))" 
    proof -
      fix \<nu> \<nu>' and I J :: "('a, 'b, 'c) interp"
      assume IA:"Iagree I J (SIGF (Prop p args))"
      have subs:"\<And>i. {Inl x | x. x \<in> SIGT (args i)} \<subseteq> (SIGF (Prop p args))"
        by auto
      have IAs:"\<And>i. Iagree I J {Inl x | x. x \<in> SIGT (args i)}"
        using IA apply(unfold SIGF.simps)
        subgoal for i
          using Iagree_sub[OF subs[of i]] by auto
        done
      have mem:"Inr (Inr p) \<in> {Inr (Inr p)} \<union> {Inl x |x. x \<in> (\<Union>i. SIGT (args i))}"
        by auto
      from IA have pSame:"Predicates I p = Predicates J p"
        by (auto simp add: Iagree_Pred IA mem)
      assume VA:"Vagree \<nu> \<nu>' (FVF (Prop p args))"
      hence VAs:"\<And>i. Vagree \<nu> \<nu>' (FVT (args i))"
        unfolding FVF.simps Vagree_def by auto
      have sems:"\<And>i. dterm_sem I (args i) \<nu> = dterm_sem J (args i) \<nu>'"
        using IAs VAs coincidence_dterm' rangeI safes 
        by (simp add: coincidence_dterm')
      hence vecSem:"(\<chi> i. dterm_sem I (args i) \<nu>) = (\<chi> i. dterm_sem J (args i) \<nu>')"
        by auto
      show "(\<nu> \<in> fml_sem I (Prop p args)) = (\<nu>' \<in> fml_sem J (Prop p args))"
        apply(unfold fml_sem.simps mem_Collect_eq)
        using IA vecSem pSame by (auto)
    qed
  then show "?case" unfolding coincide_fml_def by blast
next
  case fsafe_Not then show "?case" by auto
next
  case (fsafe_And p1 p2)
  then have safes:"fsafe p1" "fsafe p2" 
    and IH1:"\<forall> \<nu> \<nu>' I J. is_interp I \<longrightarrow> is_interp J \<longrightarrow> Iagree I J (SIGF p1) \<longrightarrow> Vagree \<nu> \<nu>' (FVF p1) \<longrightarrow> (\<nu> \<in> fml_sem I p1) = (\<nu>' \<in> fml_sem J p1)"
    and IH2:"\<forall> \<nu> \<nu>' I J. is_interp I \<longrightarrow> is_interp J \<longrightarrow> Iagree I J (SIGF p2) \<longrightarrow> Vagree \<nu> \<nu>' (FVF p2) \<longrightarrow> (\<nu> \<in> fml_sem I p2) = (\<nu>' \<in> fml_sem J p2)"
      by auto
  have almost:"\<And>\<nu> \<nu>' I J. is_interp I \<Longrightarrow> is_interp J \<Longrightarrow> Iagree I J (SIGF (And p1 p2)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVF (And p1 p2)) \<Longrightarrow> (\<nu> \<in> fml_sem I (And p1 p2)) = (\<nu>' \<in> fml_sem J (And p1 p2))" 
  proof -
    fix \<nu> \<nu>' and I J::"('a,'b,'c) interp"
    assume goodI:"is_interp I" and goodJ:"is_interp J"
    assume IA:"Iagree I J (SIGF (And p1 p2))"
    have IAsubs:"(SIGF p1) \<subseteq> (SIGF (And p1 p2))" "(SIGF p2) \<subseteq> (SIGF (And p1 p2))" by auto
    from IA have IAs:"Iagree I J (SIGF p1)" "Iagree I J (SIGF p2)"
      using Iagree_sub[OF IAsubs(1)] Iagree_sub[OF IAsubs(2)] goodI goodJ by auto
    assume VA:"Vagree \<nu> \<nu>' (FVF (And p1 p2))"
    hence VAs:"Vagree \<nu> \<nu>' (FVF p1)" "Vagree \<nu> \<nu>' (FVF p2)"
      unfolding FVF.simps Vagree_def by auto
    have eq1:"(\<nu> \<in> fml_sem I p1) = (\<nu>' \<in> fml_sem J p1)" using IH1 IAs VAs  goodI goodJ by blast
    have eq2:"(\<nu> \<in> fml_sem I p2) = (\<nu>' \<in> fml_sem J p2)" using IH2 IAs VAs  goodI goodJ by blast
    show "(\<nu> \<in> fml_sem I (And p1 p2)) = (\<nu>' \<in> fml_sem J (And p1 p2))"
      using eq1 eq2 by auto
  qed
  then show "?case" unfolding coincide_fml_def by blast
next
  case (fsafe_Exists p x)
  then have safe:"fsafe p"
    and IH:"\<forall> \<nu> \<nu>' I J. is_interp I \<longrightarrow> is_interp J \<longrightarrow> Iagree I J (SIGF p) \<longrightarrow> Vagree \<nu> \<nu>' (FVF p) \<longrightarrow> (\<nu> \<in> fml_sem I p) = (\<nu>' \<in> fml_sem J p)"
    by auto
  have almost:"\<And>\<nu> \<nu>' I J. is_interp I \<Longrightarrow> is_interp J \<Longrightarrow> Iagree I J (SIGF (Exists x p)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVF (Exists x p)) \<Longrightarrow> (\<nu> \<in> fml_sem I (Exists x p)) = (\<nu>' \<in> fml_sem J (Exists x p))" 
  proof -
    fix \<nu> \<nu>' and I J::"('a,'b,'c)interp"
    assume goodI:"is_interp I" and goodJ:"is_interp J"
    assume IA:"Iagree I J (SIGF (Exists x p))"
    hence IA':"Iagree I J (SIGF p)" 
      unfolding SIGF.simps Iagree_def by auto
    assume VA:"Vagree \<nu> \<nu>' (FVF (Exists x p))"
    hence VA':"Vagree \<nu> \<nu>' (FVF p - {Inl x})" by auto
    hence VA'':"\<And>r. Vagree (repv \<nu> x r) (repv \<nu>' x r) (FVF p)" 
      subgoal for r 
        unfolding Vagree_def FVF.simps repv.simps
        by auto
      done
    have IH': "\<And>r. Iagree I J (SIGF p) \<Longrightarrow> Vagree (repv \<nu> x r) (repv \<nu>' x r) (FVF p) \<Longrightarrow> ((repv \<nu> x r) \<in> fml_sem I p) = ((repv \<nu>' x r) \<in> fml_sem J p)"
      subgoal for r
        using IH apply(rule allE[where x = "repv \<nu> x r"])
        apply(erule allE[where x = "repv \<nu>' x r"])
        using goodI goodJ by (auto)
      done
    hence IH'':"\<And>r. ((repv \<nu> x r) \<in> fml_sem I p) = ((repv \<nu>' x r) \<in> fml_sem J p)"
      subgoal for r
        using IA' VA'' by auto
      done
    have fact:"\<And>r. (repv \<nu> x r \<in> fml_sem I p) = (repv \<nu>' x r \<in> fml_sem J p)"
      subgoal for r
        using IH'[OF IA' VA''] by auto
      done
    show "(\<nu> \<in> fml_sem I (Exists x p)) = (\<nu>' \<in> fml_sem J (Exists x p))"
      apply(simp only: fml_sem.simps mem_Collect_eq)
      using IH'' by auto
  qed
  then show "?case" unfolding coincide_fml_def by blast
next
  case (fsafe_Diamond a p) then 
  have hsafe:"hpsafe a"
    and psafe:"fsafe p"
    and IH1':"\<forall>I J \<nu> \<nu>' \<mu> V. is_interp I \<longrightarrow> is_interp J \<longrightarrow>
       Iagree I J (SIGP a) \<longrightarrow>
       Vagree \<nu> \<nu>' V \<longrightarrow> FVP a \<subseteq> V \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I a \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J a \<and> Vagree \<mu> \<mu>' (MBV a \<union> V))"
   
    and IH2:"\<forall>\<nu> \<nu>' I J. is_interp I \<longrightarrow> is_interp J \<longrightarrow>Iagree I J (SIGF p) \<longrightarrow> Vagree \<nu> \<nu>' (FVF p) \<longrightarrow> (\<nu> \<in> fml_sem I p) = (\<nu>' \<in> fml_sem J p)"
    unfolding coincide_hp'_def coincide_hp_def coincide_fml_def apply auto done
  have almost:"\<And>\<nu> \<nu>' I J. is_interp I \<Longrightarrow> is_interp J \<Longrightarrow> Iagree I J (SIGF (Diamond a p)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVF (Diamond a p)) \<Longrightarrow> (\<nu> \<in> fml_sem I (Diamond a p)) = (\<nu>' \<in> fml_sem J (Diamond a p))" 
  proof -
    fix \<nu> \<nu>' and I J::"('a,'b,'c) interp"
    assume goodI:"is_interp I" assume goodJ:"is_interp J"
    have IH1:"\<forall> \<nu> \<nu>' \<mu> V. is_interp I \<longrightarrow> is_interp J \<longrightarrow>
       Iagree I J (SIGP a) \<longrightarrow>
       Vagree \<nu> \<nu>' V \<longrightarrow> FVP a \<subseteq> V \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I a \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J a \<and> Vagree \<mu> \<mu>' (MBV a \<union> V))" 
      using goodI goodJ IH1' by auto
    assume IA:"Iagree I J (SIGF (Diamond a p))"
    have IAsubs:"(SIGP a) \<subseteq> (SIGF (Diamond a p))" "(SIGF p) \<subseteq> (SIGF (Diamond a p))" by auto
    from IA have IAP:"Iagree I J (SIGP a)"
      and IAF:"Iagree I J (SIGF p)" using Iagree_sub[OF IAsubs(1)] Iagree_sub[OF IAsubs(2)] by auto
    from IAP have IAP':"Iagree J I (SIGP a)" by (rule Iagree_comm)
    from IAF have IAF':"Iagree J I (SIGF p)" by (rule Iagree_comm)
    assume VA:"Vagree \<nu> \<nu>' (FVF (Diamond a p))"
    hence VA':"Vagree \<nu>' \<nu> (FVF (Diamond a p))" by (rule agree_comm)
    have dir1:"\<nu> \<in> fml_sem I (Diamond a p) \<Longrightarrow> \<nu>' \<in> fml_sem J (Diamond a p)"
    proof - 
      assume sem:"\<nu> \<in> fml_sem I (Diamond a p)"
      let ?V = "FVF (Diamond a p)"
      have Vsup:"FVP a \<subseteq> ?V" by auto
      obtain \<mu> where prog:"(\<nu>, \<mu>) \<in> prog_sem I a" and fml:"\<mu> \<in> fml_sem I p" 
        using sem by auto
      from IH1 have IH1':
        "Iagree I J (SIGP a) \<Longrightarrow>
           Vagree \<nu> \<nu>' ?V \<Longrightarrow>
           FVP a \<subseteq> ?V \<Longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I a \<Longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J a \<and> Vagree \<mu> \<mu>' (MBV a \<union> ?V))"
        using goodI goodJ by blast
      obtain \<mu>' where prog':"(\<nu>', \<mu>') \<in> prog_sem J a" and agree:"Vagree \<mu> \<mu>' (MBV a \<union> ?V)"
        using IH1'[OF IAP VA Vsup prog] by blast
      from IH2 
      have IH2':"Iagree I J (SIGF p) \<Longrightarrow> Vagree \<mu> \<mu>' (FVF p) \<Longrightarrow> (\<mu> \<in> fml_sem I p) = (\<mu>' \<in> fml_sem J p)"
        using goodI goodJ by blast
      have  VAF:"Vagree \<mu> \<mu>' (FVF p)"
        using agree VA by (auto simp only: Vagree_def FVF.simps)
      hence IH2'':"(\<mu> \<in> fml_sem I p) = (\<mu>' \<in> fml_sem J p)"
        using IH2'[OF IAF VAF] by auto
      have fml':"\<mu>' \<in> fml_sem J p" using IH2'' fml by auto
      have "\<exists> \<mu>'. (\<nu>', \<mu>') \<in> prog_sem J a \<and> \<mu>' \<in> fml_sem J p" using fml' prog' by blast
      then show "\<nu>' \<in> fml_sem J (Diamond a p)" 
        unfolding fml_sem.simps by (auto simp only: mem_Collect_eq)
    qed
    have dir2:"\<nu>' \<in> fml_sem J (Diamond a p) \<Longrightarrow> \<nu> \<in> fml_sem I (Diamond a p)"
    proof - 
      assume sem:"\<nu>' \<in> fml_sem J (Diamond a p)"
      let ?V = "FVF (Diamond a p)"
      have Vsup:"FVP a \<subseteq> ?V" by auto
      obtain \<mu> where prog:"(\<nu>', \<mu>) \<in> prog_sem J a" and fml:"\<mu> \<in> fml_sem J p" 
        using sem by auto
      from IH1 have IH1':
        "Iagree J I (SIGP a) \<Longrightarrow>
           Vagree \<nu>' \<nu> ?V \<Longrightarrow>
           FVP a \<subseteq> ?V \<Longrightarrow> (\<nu>', \<mu>) \<in> prog_sem J a \<Longrightarrow> (\<exists>\<mu>'. (\<nu>, \<mu>') \<in> prog_sem I a \<and> Vagree \<mu> \<mu>' (MBV a \<union> ?V))"
        using goodI goodJ  IH1' by blast
      obtain \<mu>' where prog':"(\<nu>, \<mu>') \<in> prog_sem I a" and agree:"Vagree \<mu> \<mu>' (MBV a \<union> ?V)"
        using IH1'[OF IAP' VA' Vsup prog] by blast
      from IH2 
      have IH2':"Iagree J I (SIGF p) \<Longrightarrow> Vagree \<mu> \<mu>' (FVF p) \<Longrightarrow> (\<mu> \<in> fml_sem J p) = (\<mu>' \<in> fml_sem I p)"
        using goodI goodJ by blast
      have  VAF:"Vagree \<mu> \<mu>' (FVF p)"
        using agree VA by (auto simp only: Vagree_def FVF.simps)
      hence IH2'':"(\<mu> \<in> fml_sem J p) = (\<mu>' \<in> fml_sem I p)"
        using IH2'[OF IAF' VAF] by auto
      have fml':"\<mu>' \<in> fml_sem I p" using IH2'' fml by auto
      have "\<exists> \<mu>'. (\<nu>, \<mu>') \<in> prog_sem I a \<and> \<mu>' \<in> fml_sem I p" using fml' prog' by blast
      then show "\<nu> \<in> fml_sem I (Diamond a p)" 
        unfolding fml_sem.simps by (auto simp only: mem_Collect_eq)
    qed
    show "(\<nu> \<in> fml_sem I (Diamond a p)) = (\<nu>' \<in> fml_sem J (Diamond a p))"
      using dir1 dir2 by auto
  qed
  then show "?case" unfolding coincide_fml_def by blast
next
  case (fsafe_InContext \<phi>) then 
  have safe:"fsafe \<phi>"
    and IH:"(\<forall> \<nu> \<nu>' I J. is_interp I \<longrightarrow> is_interp J \<longrightarrow> Iagree I J (SIGF \<phi>) \<longrightarrow> Vagree \<nu> \<nu>' (FVF \<phi>) \<longrightarrow> \<nu> \<in> fml_sem I \<phi> \<longleftrightarrow> \<nu>' \<in> fml_sem J \<phi>)"
    by (unfold coincide_fml_def)
  hence IH':"\<And>\<nu> \<nu>' I J. is_interp I \<Longrightarrow> is_interp J \<Longrightarrow>  Iagree I J (SIGF \<phi>) \<Longrightarrow> Vagree \<nu> \<nu>' (FVF \<phi>) \<Longrightarrow> \<nu> \<in> fml_sem I \<phi> \<longleftrightarrow> \<nu>' \<in> fml_sem J \<phi>"
    by auto
  hence sem_eq:"\<And>I J. is_interp I \<Longrightarrow> is_interp J \<Longrightarrow>  Iagree I J (SIGF \<phi>) \<Longrightarrow> fml_sem I \<phi> = fml_sem J \<phi>"
    apply (auto simp: Collect_cong Collect_mem_eq agree_refl)
     using agree_refl by blast+
  have "(\<And> \<nu> \<nu>' I J C . is_interp I \<Longrightarrow> is_interp J \<Longrightarrow>  Iagree I J (SIGF (InContext C \<phi>)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVF (InContext C \<phi>)) \<Longrightarrow> \<nu> \<in> fml_sem I (InContext C \<phi>)  \<longleftrightarrow> \<nu>' \<in> fml_sem J (InContext C \<phi>))"
    proof -
      fix \<nu> \<nu>' and I J::"('a,'b,'c) interp" and C
      assume goodI:"is_interp I" and goodJ:"is_interp J"
      assume IA:"Iagree I J (SIGF (InContext C \<phi>))"
      then have IA':"Iagree I J (SIGF \<phi>)" unfolding SIGF.simps Iagree_def by auto
      assume VA:"Vagree \<nu> \<nu>' (FVF (InContext C \<phi>))"
      then have VAU:"Vagree \<nu> \<nu>' UNIV" unfolding FVF.simps Vagree_def by auto
      then have VA':"Vagree \<nu> \<nu>' (FVF \<phi>)" unfolding FVF.simps Vagree_def by auto
      from VAU have eq:"\<nu> = \<nu>'" by (cases "\<nu>", cases "\<nu>'", auto simp add: vec_eq_iff Vagree_def)
      from IA have Cmem:"Inr (Inl C) \<in> SIGF (InContext C \<phi>)"
        by simp
      have Cagree:"Contexts I C = Contexts J C" by (rule Iagree_Contexts[OF IA Cmem])
      show "\<nu> \<in> fml_sem I (InContext C \<phi>)  \<longleftrightarrow> \<nu>' \<in> fml_sem J (InContext C \<phi>)"  
        using Cagree eq sem_eq IA' goodI goodJ by (auto)
    qed
  then show "?case" by simp
qed 

lemma coincidence_formula:"\<And>\<nu> \<nu>' I J. fsafe (\<phi>::('a::finite, 'b::finite, 'c::finite) formula) \<Longrightarrow> is_interp I \<Longrightarrow> is_interp J \<Longrightarrow> Iagree I J (SIGF \<phi>) \<Longrightarrow> Vagree \<nu> \<nu>' (FVF \<phi>) \<Longrightarrow> (\<nu> \<in> fml_sem I \<phi> \<longleftrightarrow> \<nu>' \<in> fml_sem J \<phi>)"
  using coincidence_hp_fml unfolding coincide_fml_def by blast 

lemma coincidence_hp:
  fixes \<nu> \<nu>' \<mu> V I J
  assumes safe:"hpsafe (\<alpha>::('a::finite, 'b::finite, 'c::finite) hp)"
  assumes goodI:"is_interp I"
  assumes goodJ:"is_interp J"
  assumes IA:"Iagree I J (SIGP \<alpha>)"
  assumes VA:"Vagree \<nu> \<nu>' V"
  assumes sub:"V \<supseteq> (FVP \<alpha>)"
  assumes sem:"(\<nu>, \<mu>) \<in> prog_sem I \<alpha>"   
  shows "(\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J \<alpha> \<and> Vagree \<mu> \<mu>' (MBV \<alpha> \<union> V))"
proof -
  have thing:"(\<forall>I J. is_interp I \<longrightarrow> is_interp J \<longrightarrow> (\<forall>\<nu> \<nu>' \<mu> V.
            Iagree I J (SIGP \<alpha>) \<longrightarrow>
            Vagree \<nu> \<nu>' V \<longrightarrow> FVP \<alpha> \<subseteq> V \<longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I \<alpha> \<longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J \<alpha> \<and> Vagree \<mu> \<mu>' (MBV \<alpha> \<union> V))) \<and>
        ode_sem_equiv \<alpha> I)" 
    using coincidence_hp_fml unfolding coincide_hp_def coincide_hp'_def
    using safe by blast
  then have "(Iagree I J (SIGP \<alpha>) \<Longrightarrow>
            Vagree \<nu> \<nu>' V \<Longrightarrow> FVP \<alpha> \<subseteq> V \<Longrightarrow> (\<nu>, \<mu>) \<in> prog_sem I \<alpha> \<Longrightarrow> (\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J \<alpha> \<and> Vagree \<mu> \<mu>' (MBV \<alpha> \<union> V)))"
    using IA VA sub sem thing  goodI goodJ by blast
  then show "(\<exists>\<mu>'. (\<nu>', \<mu>') \<in> prog_sem J \<alpha> \<and> Vagree \<mu> \<mu>' (MBV \<alpha> \<union> V))"
    using IA VA sub sem by auto
qed

subsection \<open>Corollaries: Alternate ODE semantics definition\<close>

lemma ode_sem_eq:
  fixes I::"('a::finite,'b::finite,'c::finite) interp" and ODE::"('a,'c) ODE" and \<phi>::"('a,'b,'c) formula"
  assumes goodI:"is_interp I"
  assumes goodJ:"is_interp J"
  assumes osafe:"osafe ODE"
  assumes fsafe:"fsafe \<phi>"
  shows
 "({(\<nu>, mk_v I ODE \<nu> (sol t)) | \<nu> sol t.
      t \<ge> 0 \<and>
      (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu> x \<in> fml_sem I \<phi>} \<and>
      VSagree (sol 0) (fst \<nu>) {x | x. Inl x \<in> FVP (EvolveODE ODE \<phi>)}}) = 
  ({(\<nu>, mk_v I ODE \<nu> (sol t)) | \<nu> sol t.
      t \<ge> 0 \<and>
      (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu> x \<in> fml_sem I \<phi>} \<and>
      (sol 0) = (fst \<nu>)})"
proof - 
  have hpsafe:"hpsafe (EvolveODE ODE \<phi>)" using osafe fsafe by (auto intro: hpsafe_fsafe.intros)
  have "coincide_hp'(EvolveODE ODE \<phi>)" using coincidence_hp_fml hpsafe goodI goodJ by blast
  hence "ode_sem_equiv (EvolveODE ODE \<phi>) I" unfolding coincide_hp'_def using goodI goodJ by auto
  then show "?thesis" 
    unfolding ode_sem_equiv_def using osafe fsafe by auto
qed

lemma ode_alt_sem:"\<And>I ::('a::finite,'b::finite,'c::finite) interp. \<And>ODE::('a,'c) ODE. \<And>\<phi>::('a,'b,'c)formula. 
is_interp I \<Longrightarrow> osafe ODE \<Longrightarrow> fsafe \<phi>  \<Longrightarrow> 
  prog_sem I (EvolveODE ODE \<phi>)
= 
{(\<nu>, mk_v I ODE \<nu> (sol t)) | \<nu> sol t.
      t \<ge> 0 \<and>
      (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu> x \<in> fml_sem I \<phi>} \<and>
      VSagree (sol 0) (fst \<nu>) {x | x. Inl x \<in> FVP (EvolveODE ODE \<phi>)}}
" 
  subgoal for I ODE \<phi>
    using ode_sem_eq[of I I ODE \<phi> ] by auto
  done
end
end 
