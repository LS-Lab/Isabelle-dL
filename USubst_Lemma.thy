theory "USubst_Lemma"
imports
  Complex_Main HOL
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
  "./Ids"
  "./Lib"
  "./Syntax"
  "./Denotational_Semantics"
  "./Frechet_Correctness"
  "./Static_Semantics"
  "./Coincidence"
  "./Bound_Effect"
  "./USubst"
begin context ids begin
lemma interp_eq:
  "f = f' \<Longrightarrow> p = p' \<Longrightarrow> c = c' \<Longrightarrow> PP = PP' \<Longrightarrow> ode = ode' \<Longrightarrow>
   \<lparr>Functions = f, Predicates = p, Contexts = c, Programs = PP, ODEs = ode\<rparr> =
   \<lparr>Functions = f', Predicates = p', Contexts = c', Programs = PP', ODEs = ode'\<rparr>"
  by auto

(* Properties of adjoints *)
lemma adjoint_consequence:"(\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f') \<Longrightarrow> (\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f') \<Longrightarrow> Vagree \<nu> \<omega> (FVS \<sigma>) \<Longrightarrow> adjoint I \<sigma> \<nu> = adjoint I \<sigma> \<omega>"
  apply(unfold FVS_def)
  apply(auto)
  apply(unfold adjoint_def)
  apply(rule interp_eq)
  apply(auto simp add: fun_eq_iff)
  subgoal for xa xaa 
    apply(cases "SFunctions \<sigma> xa")
    apply(auto)
    subgoal for a 
      proof -
        assume safes:"(\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
        assume agrees:"Vagree \<nu> \<omega> (\<Union>x. SFV \<sigma> x)"
        assume some:"SFunctions \<sigma> xa = Some a"
        from safes some have safe:"dsafe a" by auto
        have sub:"SFV \<sigma> (Inl xa) \<subseteq> (\<Union>x. SFV \<sigma> x)"
          by blast
        from agrees 
        have "Vagree \<nu> \<omega> (SFV \<sigma> (Inl xa))"
          using agree_sub[OF sub agrees] by auto
        then have agree:"Vagree \<nu> \<omega> (FVT a)"
          using some by auto
        show "?thesis"
          using coincidence_dterm[of a, OF safes[of xa a, OF some] agree] by auto
      qed
      done
   subgoal for xa xaa 
    apply(cases "SPredicates \<sigma> xa")
    apply(auto)
    subgoal for a 
      proof -
        assume safes:"(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
        assume agrees:"Vagree \<nu> \<omega> (\<Union>x. SFV \<sigma> x)"
        assume some:"SPredicates \<sigma> xa = Some a"
        assume sem:"\<nu> \<in> fml_sem \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. xaa $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                    ODEs = ODEs I\<rparr>
          a"
        from safes some have safe:"fsafe a" by auto
        have sub:"SFV \<sigma> (Inr (Inr xa)) \<subseteq> (\<Union>x. SFV \<sigma> x)"
          by blast
        from agrees 
        have "Vagree \<nu> \<omega> (SFV \<sigma> (Inr (Inr xa)))"
          using agree_sub[OF sub agrees] by auto
        then have agree:"Vagree \<nu> \<omega> (FVF a)"
          using some by auto
        let ?I' = "\<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. xaa $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                    ODEs = ODEs I\<rparr>"
        have IA:"\<And>S. Iagree ?I' ?I' (SIGF a)" using Iagree_refl by auto
        show "?thesis"
          using coincidence_formula[of a, OF safes[of xa a, OF some] IA agree] sem by auto
      qed
      done
   subgoal for xa xaa 
    apply(cases "SPredicates \<sigma> xa")
    apply(auto)
    subgoal for a 
      proof -
        assume safes:"(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
        assume agrees:"Vagree \<nu> \<omega> (\<Union>x. SFV \<sigma> x)"
        assume some:"SPredicates \<sigma> xa = Some a"
        assume sem:"\<omega> \<in> fml_sem \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. xaa $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                    ODEs = ODEs I\<rparr>
          a"
        from safes some have safe:"fsafe a" by auto
        have sub:"SFV \<sigma> (Inr (Inr xa)) \<subseteq> (\<Union>x. SFV \<sigma> x)"
          by blast
        from agrees 
        have "Vagree \<nu> \<omega> (SFV \<sigma> (Inr (Inr xa)))"
          using agree_sub[OF sub agrees] by auto
        then have agree:"Vagree \<nu> \<omega> (FVF a)"
          using some by auto
        let ?I' = "\<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. xaa $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                    ODEs = ODEs I\<rparr>"
        have IA:"\<And>S. Iagree ?I' ?I' (SIGF a)" using Iagree_refl by auto
        show "?thesis"
          using coincidence_formula[of a, OF safes[of xa a, OF some] IA agree] sem by auto
      qed
      done    
    done

lemma SIGT_plus1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Plus t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x)"
  unfolding Vagree_def by auto

lemma SIGT_plus2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Plus t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t2. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x)"
  unfolding Vagree_def by auto

lemma SIGT_times1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Times t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x)"
  unfolding Vagree_def by auto

lemma SIGT_times2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Times t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t2. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x)"
  unfolding Vagree_def by auto

lemma uadmit_sterm_adjoint':
  assumes dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f'"
  shows  "Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x) \<Longrightarrow> sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  case (Plus \<theta>1 \<theta>2)
    assume IH1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>1. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>1 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>1"
    assume IH2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>2. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>2 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Plus \<theta>1 \<theta>2). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a)"
  then show ?case
    using IH1[OF SIGT_plus1[OF VA]] IH2[OF SIGT_plus2[OF VA]] by auto
next
  case (Times \<theta>1 \<theta>2)
    assume IH1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>1. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>1 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>1"
    assume IH2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>2. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>2 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Times \<theta>1 \<theta>2). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a)"    
  then show ?case
    using IH1[OF SIGT_times1[OF VA]] IH2[OF SIGT_times2[OF VA]] by auto
next
  case (Function x1a x2a)
    assume IH:"\<And>x. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT x. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a) \<Longrightarrow>
      sterm_sem (local.adjoint I \<sigma> \<nu>) x = sterm_sem (local.adjoint I \<sigma> \<omega>) x"
    from IH have IH':"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2a j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a) \<Longrightarrow>
      sterm_sem (local.adjoint I \<sigma> \<nu>) (x2a j) = sterm_sem (local.adjoint I \<sigma> \<omega>) (x2a j)"
      using rangeI by auto
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT ($f x1a x2a). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a)"
    from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2a j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a)"
      unfolding Vagree_def SIGT.simps using rangeI by blast
    have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
    have VAsub:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> (FVT a) \<subseteq> (\<Union>i\<in>SIGT ($f x1a x2a). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a)"
      using SIGT by auto
    have VAf:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a)"
      using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "SFunctions \<sigma> x1a")
    defer
    subgoal for x a
      proof -
        assume VA:"(\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a))"
        assume sems:"(\<And>j. \<forall>x. sterm_sem (local.adjoint I \<sigma> \<nu>) (x2a j) x = sterm_sem (local.adjoint I \<sigma> \<omega>) (x2a j) x)"
        assume some:"SFunctions \<sigma> x1a = Some a"
        note FVT = VAf[OF some]
        have dsem:"\<And>R . dterm_sem (extendf I R) a \<nu> = dterm_sem (extendf I R) a \<omega>"
          using coincidence_dterm[OF dsafe[OF some] FVT] by auto
        have "\<And>R. Functions (local.adjoint I \<sigma> \<nu>) x1a R = Functions (local.adjoint I \<sigma> \<omega>) x1a R"
          using dsem some unfolding adjoint_def by auto
        then show "Functions (local.adjoint I \<sigma> \<nu>) x1a (\<chi> i. sterm_sem (local.adjoint I \<sigma> \<omega>) (x2a i) x) =
                   Functions (local.adjoint I \<sigma> \<omega>) x1a (\<chi> i. sterm_sem (local.adjoint I \<sigma> \<omega>) (x2a i) x)"
          by auto
      qed
    unfolding adjoint_def apply auto    
    done
qed (auto)  
  
(* Not used, but good practice for dterm adjoint *)
lemma uadmit_sterm_adjoint:
  assumes TUA:"TUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f'"
  shows  "sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
  proof -
    have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
      by auto
    have "\<And>x. x \<in> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x) \<Longrightarrow> x \<in> (-U)"
      using TUA unfolding TUadmit_def by auto
    then have sub1:"(\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x) \<subseteq> -U"
      by auto
    then have VA':"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x)"
      using agree_sub[OF sub1 VA] by auto
    (*have "\<And>x. x \<in> (\<Union>x. SFV \<sigma> x) \<Longrightarrow> x \<in> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x)"*)
    have "\<And>x y . x \<in> (SFV \<sigma> y) \<Longrightarrow> (\<exists>i. i \<in> SIGT \<theta> \<and> (x \<in> (case SFunctions \<sigma> i of Some z \<Rightarrow> FVT z)))"
      subgoal for x y
        apply(cases "y")
        subgoal for a 
          apply(cases "SFunctions \<sigma> a")
          subgoal using VA unfolding Vagree_def by auto
          subgoal for aa
            apply(rule exI[where x="a"])
            apply auto
            using TUA VA unfolding Vagree_def TUadmit_def apply auto
            sorry
          done
          (*subgoal for aa using VA unfolding Vagree_def apply auto sledgehammer*)
        subgoal for b
          using TUA VA unfolding Vagree_def TUadmit_def apply auto
            
          using TUA VA unfolding Vagree_def TUadmit_def apply auto
          
          using VA unfolding Vagree_def apply auto
          
      using TUA VA unfolding Vagree_def TUadmit_def apply auto
      sorry
    (* have "\<And>x. x \<in> (\<Union>x. SFV \<sigma> x) \<Longrightarrow> x \<in> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x)"
    *)
    then have sub2:"(\<Union>x. SFV \<sigma> x) \<subseteq> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x)"
      by auto
    have sub:"(\<Union>x. SFV \<sigma> x) \<subseteq> (-U)"
      using sub1 sub2 by auto
      apply (auto)
      subgoal for x xa
        apply(cases "xa")
        apply(auto)
        subgoal for a
          apply(cases "SFunctions \<sigma> a")
          apply(auto)
          using TUA unfolding TUadmit_def
          using TUA unfolding TUadmit_def using VA unfolding Vagree_def apply auto
          using TUA unfolding TUadmit_def unfolding SFV.simps 
          apply auto
          subgoal for aa
            apply (cases "xa")
            apply auto
            apply(cases "SFunctions \<sigma> a")
            apply auto
            sorry
            done
          subgoal for b sorry
        done
      done
    have VAF:"Vagree \<nu> \<omega> (FVS \<sigma>)" 
      using agree_sub[OF sub VA] 
      by (auto simp add: FVS_def)
    have eq:"(adjoint I \<sigma> \<nu>) = (adjoint I \<sigma> \<omega>)"
      apply(rule adjoint_consequence)
      using VAF
      using fsafe dsafe by auto
    then show "?thesis"
      by auto
  qed
  
(* TODO: Actually used, so prove it *)
lemma uadmit_dterm_adjoint:
  assumes TUA:"TUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> Vagree \<nu> \<omega> (FVS \<sigma>) \<Longrightarrow> dsafe f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> Vagree \<nu> \<omega> (FVS \<sigma>) \<Longrightarrow> fsafe f'"
  shows  "dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
  sorry

lemma uadmit_prog_adjoint:"PUadmit \<sigma> a U \<Longrightarrow> Vagree \<nu> \<omega> (-U) \<Longrightarrow> prog_sem (adjoint I \<sigma> \<nu>) a = prog_sem (adjoint I \<sigma> \<omega>) a"
and   uadmit_fml_sem:"FUadmit \<sigma> \<phi> U \<Longrightarrow> Vagree \<nu> \<omega> (-U) \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
  sorry

lemma nsubst_sterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
shows "dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> sterm_sem I (NTsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induction rule: dfree.induct)
  case (dfree_Fun args f) then
    show "?case" 
      by(cases "f") (auto simp add:  NTadjoint_free)
qed (auto)

lemma sterm_determines_frechet:
fixes I J::"('sf, 'sc, 'sz) interp" 
  and \<theta>1 \<theta>2 :: "('sf, 'sz) trm"
  and \<nu> 
assumes good_interp1:"is_interp I"
assumes good_interp2:"is_interp J"
assumes free1:"dfree \<theta>1"
assumes free2:"dfree \<theta>2"
assumes sem:"sterm_sem I \<theta>1 = sterm_sem J \<theta>2"
shows "frechet I \<theta>1 (fst \<nu>) (snd \<nu>) = frechet J \<theta>2 (fst \<nu>) (snd \<nu>)"
proof -
  have d1:"(sterm_sem I \<theta>1 has_derivative (frechet I \<theta>1 (fst \<nu>))) (at (fst \<nu>))"
    using frechet_correctness[OF good_interp1 free1] by auto
  have d2:"(sterm_sem J \<theta>2 has_derivative (frechet J \<theta>2 (fst \<nu>))) (at (fst \<nu>))"
    using frechet_correctness[OF good_interp2 free2] by auto
  then have d1':"(sterm_sem I \<theta>1 has_derivative (frechet J \<theta>2 (fst \<nu>))) (at (fst \<nu>))"
    using sem by auto
  thus "?thesis" using has_derivative_unique d1 d1' by metis 
qed

lemma ntsubst_preserves_free:
"dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dfree(NTsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case"
    by (cases "i") (auto intro:dfree.intros)
qed (auto intro: dfree.intros)

lemma tsubst_preserves_free:
"dfree \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dfree(Tsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case" 
    by (cases "SFunctions \<sigma> i") (auto intro:dfree.intros ntsubst_preserves_free)
qed (auto intro: dfree.intros)

lemma subst_sterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
shows "
  dfree \<theta> \<Longrightarrow>
  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> 
   sterm_sem I (Tsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induction rule: dfree.induct)
  case (dfree_Fun args f) 
    note frees = dfree_Fun.hyps(1) and sfree = dfree_Fun.prems(1)
    have IH:"(\<And>i. dfree (args i) \<Longrightarrow>
        sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>))" 
      using  dfree_Fun.prems dfree_Fun.IH by auto
    have eqs:"\<And>i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)"
      by (auto simp add: IH frees)
    show "?case" 
    proof (cases "SFunctions \<sigma> f")
      fix f'
      assume some:"SFunctions \<sigma> f = Some f'" 
      let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
      have subFree:"(\<And>i. dfree (?sub i))" using tsubst_preserves_free[OF frees sfree] 
        using frees sfree tsubst_preserves_free by blast
      have IH2:"sterm_sem I (NTsubst f' ?sub) (fst \<nu>) = sterm_sem (NTadjoint I ?sub \<nu>) f' (fst \<nu>)"
        using frees subFree sfree[OF some] by (simp add: nsubst_sterm)
      show "?thesis" 
        using IH frees by (auto simp add: eqs adjoint_free[OF sfree] IH2 NTadjoint_free[OF subFree] some)
    qed (auto simp add: IH adjoint_def vec_extensionality frees)
  qed auto


(* TODO: In principle useful, but not actually used. *)
lemma nsubst_frechet:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"
shows "dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> frechet I (NTsubst \<theta> \<sigma>) (fst \<nu>) = frechet (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induct rule: dfree.induct)
  case (dfree_Times \<theta>\<^sub>1 \<theta>\<^sub>2)
    assume free1:"dfree \<theta>\<^sub>1"
    assume IH1:"(\<And>i. dfree (\<sigma> i)) \<Longrightarrow> frechet I (NTsubst \<theta>\<^sub>1 \<sigma>) (fst \<nu>) = frechet (NTadjoint I \<sigma> \<nu>) \<theta>\<^sub>1 (fst \<nu>)"
    assume free2:"dfree \<theta>\<^sub>2"
    assume IH2:"(\<And>i. dfree (\<sigma> i)) \<Longrightarrow> frechet I (NTsubst \<theta>\<^sub>2 \<sigma>) (fst \<nu>) = frechet (NTadjoint I \<sigma> \<nu>) \<theta>\<^sub>2 (fst \<nu>)"
    assume freeSub:"\<And>i. dfree (\<sigma> i)"
    show "frechet I (NTsubst (Times \<theta>\<^sub>1 \<theta>\<^sub>2) \<sigma>) (fst \<nu>) = frechet (NTadjoint I \<sigma> \<nu>) (Times \<theta>\<^sub>1 \<theta>\<^sub>2) (fst \<nu>)"
      using IH1[OF freeSub] IH2[OF freeSub] apply (auto simp add: fun_eq_iff)
      using nsubst_sterm[OF free1, of \<sigma> I \<nu>] nsubst_sterm[OF free2, of \<sigma> I \<nu>] 
      by (simp add: freeSub) 
next
  case (dfree_Fun args f) then
  show "?case"
    unfolding NTsubst.simps NTadjoint_def
    apply (cases "f")
    subgoal
      apply (auto simp add:  NTadjoint_free nsubst_sterm good_interp)
      proof -
      fix a :: 'sf
      assume a1: "\<And>i. dfree (\<sigma> i)"
      { fix vv :: "(real, 'sz) vec"
        have "\<And>i p. \<lparr>Functions = case_sum (Functions i) (\<lambda>a v. sterm_sem i (\<sigma> a) (fst p)), Predicates = Predicates i, Contexts = Contexts i, Programs = Programs i, ODEs = ODEs i\<rparr> = NTadjoint i \<sigma> p"
          using a1 by (simp add: NTadjoint_free)
        then have "(THE f. \<forall>v. (Functions I a has_derivative f v) (at v)) (\<chi> s. sterm_sem \<lparr>Functions = case_sum (Functions I) (\<lambda>a v. sterm_sem I (\<sigma> a) (fst \<nu>)), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I\<rparr> (args s) (fst \<nu>)) (\<chi> s. frechet \<lparr>Functions = case_sum (Functions I) (\<lambda>a v. dterm_sem I (\<sigma> a) \<nu>), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I\<rparr> (args s) (fst \<nu>) vv) = (THE f. \<forall>v. (Functions I a has_derivative f v) (at v)) (\<chi> s. sterm_sem \<lparr>Functions = case_sum (Functions I) (\<lambda>a v. dterm_sem I (\<sigma> a) \<nu>), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I\<rparr> (args s) (fst \<nu>)) (\<chi> s. frechet \<lparr>Functions = case_sum (Functions I) (\<lambda>a v. dterm_sem I (\<sigma> a) \<nu>), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I\<rparr> (args s) (fst \<nu>) vv)"
          by (simp add: NTadjoint_def) }
      then show "(\<lambda>v. (THE f. \<forall>v. (Functions I a has_derivative f v) (at v)) (\<chi> s. sterm_sem \<lparr>Functions = case_sum (Functions I) (\<lambda>a v. sterm_sem I (\<sigma> a) (fst \<nu>)), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I\<rparr> (args s) (fst \<nu>)) (\<chi> s. frechet \<lparr>Functions = case_sum (Functions I) (\<lambda>a v. dterm_sem I (\<sigma> a) \<nu>), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I\<rparr> (args s) (fst \<nu>) v)) = (\<lambda>v. (THE f. \<forall>v. (Functions I a has_derivative f v) (at v)) (\<chi> s. sterm_sem \<lparr>Functions = case_sum (Functions I) (\<lambda>a v. dterm_sem I (\<sigma> a) \<nu>), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I\<rparr> (args s) (fst \<nu>)) (\<chi> s. frechet \<lparr>Functions = case_sum (Functions I) (\<lambda>a v. dterm_sem I (\<sigma> a) \<nu>), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I\<rparr> (args s) (fst \<nu>) v))"
        by blast
      qed
    subgoal for b
     (* using frechet_correctness[OF good_interp] dfree_Fun.hyps apply auto*)
      (* apply (auto simp add:  NTadjoint_free nsubst_sterm good_interp)
    *)
      sorry
    done
qed (auto) (*(auto  simp add: nsubst_sterm)*)


lemma the_deriv:
  assumes deriv:"(f has_derivative F) (at x)"
  shows "(THE G. (f has_derivative G) (at x)) = F"
    apply(rule the_equality)
    subgoal by (rule deriv)
    subgoal for G by (auto simp add: deriv has_derivative_unique)
    done
   
lemma the_all_deriv:
  assumes deriv:"\<forall>x. (f has_derivative F x) (at x)"
  shows "(THE G. \<forall> x. (f has_derivative G x) (at x)) = F"
    apply(rule the_equality)
    subgoal by (rule deriv)
    subgoal for G 
      apply(rule ext)
      subgoal for x
        apply(erule allE[where x=x])
        by (auto simp add: deriv has_derivative_unique)
      done
    done

(* TODO: Actually also not used so no need to prove it. *)
lemma subst_frechet:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"
shows "dfree \<theta> \<Longrightarrow> (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> frechet I (Tsubst \<theta> \<sigma>) (fst \<nu>) = frechet (adjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induct rule: dfree.induct)
  case (dfree_Times \<theta>\<^sub>1 \<theta>\<^sub>2)
  assume free1:"(dfree \<theta>\<^sub>1)"
  assume IH1:"((\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> frechet I (Tsubst \<theta>\<^sub>1 \<sigma>) (fst \<nu>) = frechet (local.adjoint I \<sigma> \<nu>) \<theta>\<^sub>1 (fst \<nu>))"
  assume free2:"(dfree \<theta>\<^sub>2)"
  assume IH2:"((\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> frechet I (Tsubst \<theta>\<^sub>2 \<sigma>) (fst \<nu>) = frechet (local.adjoint I \<sigma> \<nu>) \<theta>\<^sub>2 (fst \<nu>))"
  assume subFree:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
  show "frechet I (Tsubst (Times \<theta>\<^sub>1 \<theta>\<^sub>2) \<sigma>) (fst \<nu>) = frechet (local.adjoint I \<sigma> \<nu>) (Times \<theta>\<^sub>1 \<theta>\<^sub>2) (fst \<nu>)"
    using IH1[OF subFree] IH2[OF subFree] subst_sterm[OF free1 subFree] subst_sterm[OF free2 subFree] by auto 
next
  case (dfree_Fun args f) then
  show "?case"
    unfolding NTsubst.simps NTadjoint_def
    apply (cases "SFunctions \<sigma> f")
    apply (auto simp add:  NTadjoint_free nsubst_sterm good_interp)
    subgoal using subst_sterm frechet_correctness apply auto sorry
    subgoal for a 
      proof -
        assume frees:"(\<And>i. dfree (args i))"
        assume freches:"(\<And>i. frechet I (Tsubst (args i) \<sigma>) (fst \<nu>) = frechet (local.adjoint I \<sigma> \<nu>) (args i) (fst \<nu>))"
        assume freeSub:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
        assume some: "SFunctions \<sigma> f = Some a"
        have P:"\<forall>x. (Functions (local.adjoint I \<sigma> \<nu>) f has_derivative (frechet I (NTsubst a (\<lambda>i. Tsubst (args i) \<sigma>)) (fst \<nu>))) (at x)"
          sorry
        have eqThe:"(THE f'. \<forall>x. (Functions (local.adjoint I \<sigma> \<nu>) f has_derivative f' x) (at x)) 
          = (\<lambda> _. frechet I (NTsubst a (\<lambda>i. Tsubst (args i) \<sigma>)) (fst \<nu>))"
          apply (rule the_all_deriv)
          using P by auto
        show "frechet I (NTsubst a (\<lambda>i. Tsubst (args i) \<sigma>)) (fst \<nu>) =
          (\<lambda>a. (THE f'. \<forall>x. (Functions (local.adjoint I \<sigma> \<nu>) f has_derivative f' x) (at x)) 
            (\<chi> i. sterm_sem (local.adjoint I \<sigma> \<nu>) (args i) (fst \<nu>))
          (\<chi> i. frechet (local.adjoint I \<sigma> \<nu>) (args i) (fst \<nu>) a))"
          using eqThe apply auto
          sorry
      qed      
      using subst_sterm frechet_correctness[OF good_interp] dfree_Fun.prems[of f] sorry
qed (auto)

(* TODO: In theory useful, but not used yet. *)
lemma nsubst_dterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
fixes \<nu>'::"'sz state"
assumes good_interp:"is_interp I"    
shows "NTadmit \<sigma> \<theta> \<Longrightarrow> dsafe \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dterm_sem I (NTsubst \<theta> \<sigma>) \<nu>' = dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> \<nu>'"
  sorry

lemma nsubst_dterm':
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"    
shows "NTadmit \<sigma> \<theta> \<Longrightarrow> dfree \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dterm_sem I (NTsubst \<theta> \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> \<nu>"
proof (induction rule: NTadmit.induct)
  case (NTadmit_Fun \<sigma> args f)
    assume admit:"\<And>i. NTadmit \<sigma> (args i)"
    assume IH:"\<And>i. dfree (args i) \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dterm_sem I (NTsubst (args i) \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) (args i) \<nu>"
    assume free:"dfree ($f f args)"
    assume safe:"\<And>i. dsafe (\<sigma> i)"
    from free have frees: "\<And>i. dfree (args i)" by (auto dest: dfree.cases)
    have sem:"\<And>i. dterm_sem I (NTsubst (args i) \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) (args i) \<nu>"
      using IH[OF frees safe] by auto
    have vecEq:" (\<chi> i. dterm_sem (NTadjoint I \<sigma> \<nu>) (args i) \<nu>) =
     (\<chi> i. dterm_sem
            \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. dterm_sem I (\<sigma> f') \<nu>), Predicates = Predicates I, Contexts = Contexts I,
               Programs = Programs I, ODEs = ODEs I\<rparr>
            (args i) \<nu>) "
      apply(rule vec_extensionality)
      by (auto simp add: NTadjoint_def)
    show " dterm_sem I (NTsubst ($f f args) \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) ($f f args) \<nu>"
      apply (cases "f") 
      apply (auto simp add: vec_extensionality  NTadjoint_def)
      using sem apply auto
      subgoal for a using vecEq by auto
      done
next
    case (NTadmit_Diff \<sigma> \<theta>) 
    hence admit:"NTadmit \<sigma> \<theta>"
      and admitU:"NTUadmit \<sigma> \<theta> UNIV"
      and IH : "dfree \<theta> \<Longrightarrow>
            (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dterm_sem I (NTsubst \<theta> \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> \<nu>"
      and safe: "dfree (Differential \<theta>)" 
      and freeSub:"\<And>i. dsafe (\<sigma> i)"
      by auto
    from safe have "False" by (auto dest: dfree.cases)
    then show "dterm_sem I (NTsubst (Differential \<theta>) \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) (Differential \<theta>) \<nu>"
      by auto
qed (auto simp add: NTadmit.cases)

lemma ntsubst_free_to_safe:
"dfree \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dsafe (NTsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case"
    by (cases "i") (auto intro:dsafe.intros ntsubst_preserves_free)
qed (auto intro: dsafe.intros)

lemma ntsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dsafe (NTsubst \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Fun args i) then show "?case"
    by (cases "i") (auto intro:dsafe.intros ntsubst_preserves_free dfree_is_dsafe)
next
  case (dsafe_Diff \<theta>) then show "?case"
    by  (auto intro:dsafe.intros ntsubst_preserves_free)
qed (auto simp add: ntsubst_preserves_free intro: dsafe.intros)

(* TODO: Actually used, so prove it *)
lemma tsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dsafe(Tsubst \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Fun args i) then show "?case" 
    sorry 
    (* by (cases "SFunctions \<sigma> i") (auto intro:dsafe.intros ntsubst_preserves_safe tsubst_preserves_free dfree_is_dsafe)*)
qed (auto intro: dsafe.intros tsubst_preserves_free)

(* TODO: In principle useful, not used yet *)
lemma extendf_safe:
assumes good_interp:"is_interp I"
shows "is_interp (extendf I R)"
  sorry

(* TODO: In principle useful, not used yet *)
lemma extendc_safe:
assumes good_interp:"is_interp I"
shows "is_interp (extendc I R)"
  sorry

primrec extendf_deriv :: "('sf,'sc,'sz) interp \<Rightarrow> 'sf \<Rightarrow> ('sf + 'sz,'sz) trm \<Rightarrow> 'sz state \<Rightarrow> 'sz Rvec \<Rightarrow> ('sz Rvec \<Rightarrow> real)"
where
  "extendf_deriv I _ (Var i) \<nu> x = (\<lambda>_. 0)"
| "extendf_deriv I _ (Const r) \<nu> x = (\<lambda>_. 0)"
| "extendf_deriv I g (Function f args) \<nu> x =
  (case f of 
    Inl ff \<Rightarrow> (THE f'. \<forall>y. (Functions I ff has_derivative f' y) (at y))
              (\<chi> i. dterm_sem
                     \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. x $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                        ODEs = ODEs I\<rparr>
                     (args i) \<nu>) \<circ>
             (\<lambda>\<nu>'. \<chi> ia. extendf_deriv I g (args ia) \<nu> x \<nu>')
  | Inr ff \<Rightarrow> (\<lambda> \<nu>'. 1))"
| "extendf_deriv I g (Plus t1 t2) \<nu> x = (\<lambda>\<nu>'. (extendf_deriv I g t1 \<nu> x \<nu>') + (extendf_deriv I g t2 \<nu> x \<nu>'))"
| "extendf_deriv I g (Times t1 t2) \<nu> x = 
   (\<lambda>\<nu>'. ((dterm_sem (extendf I x) t1 \<nu> * (extendf_deriv I g t2 \<nu> x \<nu>'))) 
       + (extendf_deriv I g t1 \<nu> x \<nu>') * (dterm_sem (extendf I x) t2 \<nu>))"
| "extendf_deriv I g ($' _) \<nu> = undefined"
| "extendf_deriv I g (Differential _) \<nu> = undefined"

lemma extendf_deriv:
  fixes f'::"('sf + 'sz,'sz) trm" and I::"('sf,'sc,'sz) interp"
  assumes free:"dfree f'"
  assumes good_interp:"is_interp I"
  (*assumes some:"SFunctions \<sigma> i = Some f'"*)
  shows "\<exists>f''. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) f' \<nu>) has_derivative (extendf_deriv I i_f f' \<nu> x)) (at x)"
  using free apply (induction rule: dfree.induct)
  apply(auto)+
  defer
  subgoal for \<theta>\<^sub>1 \<theta>\<^sub>2 x
    apply(rule has_derivative_mult)
    by auto
  subgoal for args i x
    apply(cases "i")
    defer
    apply auto
    subgoal for b using has_derivative_proj' by blast
    subgoal for a
    proof -
    assume dfrees:"(\<And>i. dfree (args i))"
    assume IH1:"(\<And>ia. \<forall>x. ((\<lambda>R. dterm_sem
                      \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                         ODEs = ODEs I\<rparr>
                      (args ia) \<nu>) has_derivative
                extendf_deriv I i_f (args ia) \<nu> x)
                (at x))"
    then have IH1':"(\<And>ia. \<And>x. ((\<lambda>R. dterm_sem
                      \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                         ODEs = ODEs I\<rparr>
                      (args ia) \<nu>) has_derivative
                extendf_deriv I i_f (args ia) \<nu> x)
                (at x))"
      by auto
    assume a:"i = Inl a"
    note chain = Deriv.derivative_intros(105)
    let ?f = "(\<lambda>x. Functions I a x)"
    let ?g = "(\<lambda> R. (\<chi> i. dterm_sem
                       \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I,
                          Programs = Programs I, ODEs = ODEs I\<rparr>
                       (args i) \<nu>))"
    let ?myf' = "(\<lambda>x. (THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y)) (?g x))"
    let ?myg' = "(\<lambda>x. (\<lambda>\<nu>'. \<chi> ia. extendf_deriv I i_f (args ia) \<nu> x \<nu>'))"
    have fg_eq:"(\<lambda>R. Functions I a
           (\<chi> i. dterm_sem
                  \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                     ODEs = ODEs I\<rparr>
                  (args i) \<nu>)) = (?f \<circ> ?g)"
      by auto
    have "\<forall>x. ((?f o ?g) has_derivative (?myf' x \<circ> ?myg' x)) (at x)"
      apply (rule allI)
      apply (rule chain)
      subgoal for xa
        apply (rule has_derivative_vec)
        subgoal for i using IH1'[of i xa] by auto
      done
      subgoal for xa 
        using good_interp unfolding is_interp_def by auto
      done
    then have "((?f o ?g) has_derivative (?myf' x \<circ> ?myg' x)) (at x)" by auto
    then show "((\<lambda>R. Functions I a
           (\<chi> i. dterm_sem
                  \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                     ODEs = ODEs I\<rparr>
                  (args i) \<nu>)) has_derivative
              (THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y))
      (\<chi> i. dterm_sem
             \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. x $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                ODEs = ODEs I\<rparr>
             (args i) \<nu>) \<circ>
     (\<lambda>\<nu>'. \<chi> ia. extendf_deriv I i_f (args ia) \<nu> x \<nu>'))
     (at x) "
      using fg_eq by auto
      qed
    done
  done
   
lemma adjoint_safe:
assumes good_interp:"is_interp I"
assumes good_subst:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') "    
shows "is_interp (adjoint I \<sigma> \<nu>)"
  apply(unfold adjoint_def)
  apply(unfold is_interp_def)
  apply(auto simp del: extendf.simps extendc.simps FunctionFrechet.simps)
  subgoal for x i
    apply(cases "SFunctions \<sigma> i = None")
    subgoal
      apply(auto  simp del: extendf.simps extendc.simps)
      using good_interp unfolding is_interp_def by simp
    apply(auto  simp del: extendf.simps extendc.simps)
    subgoal for f'
      using good_subst[of i f'] apply (auto  simp del: extendf.simps extendc.simps)
      proof -
        assume some:"SFunctions \<sigma> i = Some f'"
        assume free:"dfree f'"
        let ?f = "(\<lambda>R. dterm_sem (extendf I R) f' \<nu>)"
        let ?Poo = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
        let ?f''="extendf_deriv I i f' \<nu>"
        have Pf:"?Poo ?f''"
            using extendf_deriv[OF good_subst[of i f'] good_interp, of \<nu> i, OF some]
            by auto
        have "(THE G. (?f has_derivative G) (at x)) = ?f'' x"
          apply(rule the_deriv)
          using Pf by auto
        then have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
          using Pf the_all_deriv by auto
        show "((\<lambda>R. dterm_sem (extendf I R) f' \<nu>) has_derivative (THE f'a. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) f' \<nu>) has_derivative f'a x) (at x)) x) (at x)"
          using the_eq Pf by simp
        qed
    done
  done

lemma subst_dterm:
fixes I::"('sf, 'sc, 'sz) interp"
assumes good_interp:"is_interp I"
shows "
  Tadmit \<sigma> \<theta> \<Longrightarrow>
  dsafe \<theta> \<Longrightarrow>
  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> 
  (\<And>f f'. SPredicates \<sigma> f = Some f'  \<Longrightarrow> fsafe f') \<Longrightarrow>
  (\<And>\<nu>. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) \<theta> \<nu>)"
proof (induction rule: Tadmit.induct)
  case (Tadmit_Fun1 \<sigma> args f f' \<nu>) 
    note safe = Tadmit_Fun1.prems(1) and sfree = Tadmit_Fun1.prems(2) and TA = Tadmit_Fun1.hyps(1)
    and some = Tadmit_Fun1.hyps(2) and NTA = Tadmit_Fun1.hyps(3)
    hence safes:"\<And>i. dsafe (args i)" by auto
    have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
        dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
      using  Tadmit_Fun1.prems Tadmit_Fun1.IH by auto
    have eqs:"\<And>i \<nu>'. dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>"
      by (auto simp add: IH safes)
    let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
    have subSafe:"(\<And>i. dsafe (?sub i))"
      using tsubst_preserves_safe[OF safes sfree]
      by (simp add: safes sfree tsubst_preserves_safe)
    have freef:"dfree f'" using sfree some by auto 
    have IH2:"dterm_sem I (NTsubst f' ?sub) \<nu> = dterm_sem (NTadjoint I ?sub \<nu>) f' \<nu>"
      by (simp add: nsubst_dterm'[OF good_interp NTA freef subSafe])
    have vec:"(\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (args i) \<nu>)"
      apply(auto simp add: vec_eq_iff)
      subgoal for i
        using IH[of i, OF safes[of i]] 
        by auto
      done
    show "?case" 
      using IH safes eqs apply (auto simp add:  IH2  some good_interp)
      using some unfolding adjoint_def NTadjoint_def by auto
next
   case (Tadmit_Fun2 \<sigma> args f \<nu>) 
    note safe = Tadmit_Fun2.prems(1) and sfree = Tadmit_Fun2.prems(2) and TA = Tadmit_Fun2.hyps(1)
    and none = Tadmit_Fun2.hyps(2) 
    hence safes:"\<And>i. dsafe (args i)" by auto
    have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
        dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
      using  Tadmit_Fun2.prems Tadmit_Fun2.IH by auto
      have Ieq:"Functions I f = Functions (adjoint I \<sigma> \<nu>) f"
        using none unfolding adjoint_def by auto
      have vec:"(\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)"
        apply(auto simp add: vec_eq_iff)
        subgoal for i using IH[of i, OF safes[of i]] by auto
        done
      show "?case" using none IH Ieq vec by auto
next
    case (Tadmit_Diff \<sigma> \<theta>)  then
      have TA:"Tadmit \<sigma> \<theta>"
      and TUA:"TUadmit \<sigma> \<theta> UNIV"
      and IH:"dsafe \<theta> \<Longrightarrow> (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> (\<And>\<nu>. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> \<nu>)"
      and safe:"dsafe (Differential \<theta>)"
      and sfree:"\<And>i f'1. SFunctions \<sigma> i = Some f'1 \<Longrightarrow> dfree f'1"
      and spsafe:"\<And>f f'. SPredicates \<sigma> f = Some f'  \<Longrightarrow> fsafe f'"
        by auto
      from sfree have sdsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
        using dfree_is_dsafe by auto  
      have VA:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
      from safe have free:"dfree \<theta>" by (auto dest: dsafe.cases intro: dfree.intros)
      from free have tsafe:"dsafe \<theta>" using dfree_is_dsafe by auto
      have freeSubst:"dfree (Tsubst \<theta> \<sigma>)" 
        using tsubst_preserves_free[OF free sfree]
        using Tadmit_Diff.prems(2) free tsubst_preserves_free by blast 
      have IH':"\<And>\<nu>. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> \<nu>"
        using IH[OF tsafe sfree] by auto
      have IH'':"\<And>\<nu>'. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu>' = dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> \<nu>'"
        subgoal for \<nu>'
        using uadmit_dterm_adjoint[OF TUA VA sdsafe spsafe, of \<nu> \<nu>'] IH'[of \<nu>'] by auto
      done
      have sem_eq:"sterm_sem I (Tsubst \<theta> \<sigma>) = sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>" 
        apply (auto simp add: fun_eq_iff)
        subgoal for \<nu>'
          apply (cases "\<nu>'")
          subgoal for \<nu>''
            apply auto
            using dsem_to_ssem[OF free, of "(local.adjoint I \<sigma> \<nu>)" "(\<nu>',\<nu>')"] dsem_to_ssem[OF freeSubst, of I "(\<nu>',\<nu>')"] IH'[of "(\<nu>)"]
            apply auto
          using IH'' by auto
          done
        done
    show "?case"
      apply (auto simp add: directional_derivative_def fun_eq_iff)
        using sterm_determines_frechet[of I "(adjoint I \<sigma> \<nu>)" "(Tsubst \<theta> \<sigma>)" \<theta> "\<nu>", 
            OF good_interp adjoint_safe[OF good_interp sfree] tsubst_preserves_free[OF free sfree] 
            free sem_eq]
        by auto
  qed auto
end end