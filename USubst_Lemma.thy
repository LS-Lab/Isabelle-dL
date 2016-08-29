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

lemma sterm_determines_frechet:
fixes I ::"('a1::finite, 'b1::finite, 'c::finite) interp"
  and J ::"('a2::finite, 'b2::finite, 'c::finite) interp"
  and \<theta>1 :: "('a1::finite, 'c::finite) trm"
  and \<theta>2 :: "('a2::finite, 'c::finite) trm"
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
  | Inr ff \<Rightarrow> (\<lambda> \<nu>'. \<nu>' $ ff))"
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

lemma NTadjoint_safe:
assumes good_interp:"is_interp I"
assumes good_subst:"(\<And>i. dfree (\<sigma> i))"
shows "is_interp (NTadjoint I \<sigma> \<nu>)"
  apply(unfold NTadjoint_def)
  apply(unfold is_interp_def)
  apply(auto simp del: extendf.simps extendc.simps FunctionFrechet.simps)
  subgoal for x i
    apply(cases "i")
    subgoal
      apply(auto  simp del: extendf.simps extendc.simps)
      using good_interp unfolding is_interp_def by simp
    apply(auto  simp del: extendf.simps extendc.simps)
    subgoal for f'
      proof -
        assume some:"i = Inr f'"
        have free:"dfree (\<sigma> f')" using good_subst by auto
        let ?f = "(\<lambda>_. dterm_sem I (\<sigma> f') \<nu>)"
        let ?Poo = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
        let ?f''="(\<lambda>_ _. 0)"
        have Pf:"?Poo ?f''"
          proof (induction "\<sigma> f'")
          qed (auto)
        have "(THE G. (?f has_derivative G) (at x)) = ?f'' x"
          apply(rule the_deriv)
          using Pf by auto
        then have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
          using Pf the_all_deriv[of ?f ?f''] by auto
        have another_eq:"(THE f'a. \<forall>x. ((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative f'a x) (at x)) x = (\<lambda> _. 0)"
          using Pf by (simp add: the_eq) 
        then show "((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative (THE f'a. \<forall>x. ((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative f'a x) (at x)) x) (at x)"
          using the_eq Pf by simp
        qed
    done
  done

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

lemma SIGT_plus1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Plus t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  unfolding Vagree_def by auto

lemma SIGT_plus2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Plus t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t2. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  unfolding Vagree_def by auto

lemma SIGT_times1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Times t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  unfolding Vagree_def by auto

lemma SIGT_times2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Times t1 t2). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) 
  \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT t2. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  unfolding Vagree_def by auto

lemma uadmit_sterm_adjoint':
  assumes dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f'"
  shows  "Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  case (Plus \<theta>1 \<theta>2)
    assume IH1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>1. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>1 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>1"
    assume IH2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>2. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>2 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Plus \<theta>1 \<theta>2). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
  then show ?case
    using IH1[OF SIGT_plus1[OF VA]] IH2[OF SIGT_plus2[OF VA]] by auto
next
  case (Times \<theta>1 \<theta>2)
    assume IH1:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>1. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>1 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>1"
    assume IH2:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>2. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>2 = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Times \<theta>1 \<theta>2). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"    
  then show ?case
    using IH1[OF SIGT_times1[OF VA]] IH2[OF SIGT_times2[OF VA]] by auto
next
  case (Function x1a x2a)
    assume IH:"\<And>x. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT x. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow>
      sterm_sem (local.adjoint I \<sigma> \<nu>) x = sterm_sem (local.adjoint I \<sigma> \<omega>) x"
    from IH have IH':"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2a j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow>
      sterm_sem (local.adjoint I \<sigma> \<nu>) (x2a j) = sterm_sem (local.adjoint I \<sigma> \<omega>) (x2a j)"
      using rangeI by auto
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT ($f x1a x2a). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
    from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2a j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
      unfolding Vagree_def SIGT.simps using rangeI by blast
    have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
    have VAsub:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> (FVT a) \<subseteq> (\<Union>i\<in>SIGT ($f x1a x2a). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
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
    have "\<And>x. x \<in> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> x \<in> (-U)"
      using TUA unfolding TUadmit_def by auto
    then have sub1:"(\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> -U"
      by auto
    then have VA':"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
      using agree_sub[OF sub1 VA] by auto
    then show "?thesis" using uadmit_sterm_adjoint'[OF dsafe fsafe VA'] by auto
  qed

lemma uadmit_sterm_ntadjoint':
  assumes dsafe:"\<And>i. dfree (\<sigma> i)"
  shows  "Vagree \<nu> \<omega> ((\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i))) \<Longrightarrow> sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> = sterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  case (Plus \<theta>1 \<theta>2)
    assume IH1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta>1 = sterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>1"
    assume IH2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta>2 = sterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>2"
    assume VA:"Vagree \<nu> \<omega> ((\<Union> i\<in>{i. Inr i \<in> SIGT (Plus \<theta>1 \<theta>2)}. FVT (\<sigma> i)))"
    from VA have 
       VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
   and VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i))" unfolding Vagree_def by auto
  then show ?case
    using IH1[OF VA1] IH2[OF VA2] by auto
next
  case (Times \<theta>1 \<theta>2)
    assume IH1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta>1 = sterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>1"
    assume IH2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta>2 = sterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>2"
    assume VA:"Vagree \<nu> \<omega> ((\<Union> i\<in>{i. Inr i \<in> SIGT (Times \<theta>1 \<theta>2)}. FVT (\<sigma> i)))"
    from VA have 
       VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
   and VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i))" unfolding Vagree_def by auto
  then show ?case
    using IH1[OF VA1] IH2[OF VA2] by auto
next
  case (Function x1a x2a) 
    assume IH:"\<And>x. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT x}. FVT (\<sigma> i)) \<Longrightarrow>
      sterm_sem (NTadjoint I \<sigma> \<nu>) x = sterm_sem (NTadjoint I \<sigma> \<omega>) x"
    from IH have IH':"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (x2a j)}. FVT (\<sigma> i)) \<Longrightarrow>
      sterm_sem (NTadjoint I \<sigma> \<nu>) (x2a j) = sterm_sem (NTadjoint I \<sigma> \<omega>) (x2a j)"
      using rangeI by auto
    assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i)) "
    from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (x2a j)}. FVT (\<sigma> i))"
      unfolding Vagree_def SIGT.simps using rangeI by blast
    have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
    have VAsub:"\<And>a. x1a = Inr a \<Longrightarrow> (FVT (\<sigma> a)) \<subseteq> (\<Union> i\<in>{i. Inr i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i))"
      using SIGT by auto
    have VAf:"\<And>a. x1a = Inr a \<Longrightarrow>Vagree \<nu> \<omega> (FVT (\<sigma> a))"
      using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "x1a")
    defer
    subgoal for x a
      proof -
        assume VA:"(\<And>a.  x1a = Inr a \<Longrightarrow> Vagree \<nu> \<omega> (FVT (\<sigma> a)))"
        assume sems:"(\<And>j. \<forall>x. sterm_sem (NTadjoint I \<sigma> \<nu>) (x2a j) x = sterm_sem (NTadjoint I \<sigma> \<omega>) (x2a j) x)"
        assume some:"x1a = Inr a"
        note FVT = VAf[OF some]
        from dsafe have dsafer:"\<And>i. dsafe (\<sigma> i)" using dfree_is_dsafe by auto
        have dsem:"dterm_sem I (\<sigma> a) \<nu> = dterm_sem I (\<sigma> a) \<omega>"
          using coincidence_dterm[OF dsafer FVT] some by auto
        then have "\<And>R. Functions (NTadjoint I \<sigma> \<nu>) x1a R = Functions (NTadjoint I \<sigma> \<omega>) x1a R"
          using some unfolding adjoint_def unfolding NTadjoint_def by auto
        then show "Functions (NTadjoint I \<sigma> \<nu>) x1a (\<chi> i. sterm_sem (NTadjoint I \<sigma> \<omega>) (x2a i) x) =
                   Functions (NTadjoint I \<sigma> \<omega>) x1a (\<chi> i. sterm_sem (NTadjoint I \<sigma> \<omega>) (x2a i) x)"
          by auto
      qed
    unfolding NTadjoint_def by auto
qed (auto) 
  
lemma uadmit_sterm_ntadjoint:
  assumes TUA:"NTUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>i . dfree (\<sigma> i)"
  assumes good_interp:"is_interp I"
  shows  "sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> = sterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>"
proof -
    have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
      by auto
    have "\<And>x. x \<in> ((\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i))) \<Longrightarrow> x \<in> (-U)"
      using TUA unfolding NTUadmit_def by auto
    then have sub1:"(\<Union>i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<subseteq> -U"
      by auto
    then have VA':"Vagree \<nu> \<omega> (\<Union>i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i))"
      using agree_sub[OF sub1 VA] by auto
    then show "?thesis" using uadmit_sterm_ntadjoint'[OF  dfree VA'] by auto
  qed

lemma uadmit_dterm_adjoint':
  assumes dfree:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dfree f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f'"
  assumes good_interp:"is_interp I"
  shows  "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  case (Plus \<theta>1 \<theta>2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>1. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>2. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>2 = dterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Plus \<theta>1 \<theta>2). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
    assume safe:"dsafe (Plus \<theta>1 \<theta>2)"
  then show ?case
    using IH1[OF SIGT_plus1[OF VA]] IH2[OF SIGT_plus2[OF VA]] by auto
next
  case (Times \<theta>1 \<theta>2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>1. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>2. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta>2 = dterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Times \<theta>1 \<theta>2). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
    assume safe:"dsafe (Times \<theta>1 \<theta>2)"
  then show ?case
    using IH1[OF SIGT_times1[OF VA]] IH2[OF SIGT_times2[OF VA]] by auto
next
  case (Function x1a x2a)
    assume IH:"\<And>x. \<And>\<nu> \<omega>. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (\<Union>i\<in>SIGT x. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow>
      dsafe x \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) x = dterm_sem (local.adjoint I \<sigma> \<omega>) x"
    assume safe:"dsafe (Function x1a x2a)"
    from safe have safes:"\<And>j. dsafe (x2a j)" by auto
    from IH have IH':"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2a j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow>
      dterm_sem (local.adjoint I \<sigma> \<nu>) (x2a j) = dterm_sem (local.adjoint I \<sigma> \<omega>) (x2a j)"
      using rangeI safes by auto
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT ($f x1a x2a). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
    from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2a j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
      unfolding Vagree_def SIGT.simps using rangeI by blast
    have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
    have VAsub:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> (FVT a) \<subseteq> (\<Union>i\<in>SIGT ($f x1a x2a). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
      using SIGT by auto
    have VAf:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a)"
      using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "SFunctions \<sigma> x1a")
    defer
    subgoal for x1 x2 a
      proof -
        assume VA:"(\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a))"
        assume sems:"(\<And>j. \<forall>x1 x2. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2a j) (x1,x2) = dterm_sem (local.adjoint I \<sigma> \<omega>) (x2a j) (x1,x2))"
        assume some:"SFunctions \<sigma> x1a = Some a"
        note FVT = VAf[OF some]
        have dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
          using dfree dfree_is_dsafe by auto
        have dsem:"\<And>R . dterm_sem (extendf I R) a \<nu> = dterm_sem (extendf I R) a \<omega>"
          using coincidence_dterm[OF dsafe[OF some] FVT] by auto
        have "\<And>R. Functions (local.adjoint I \<sigma> \<nu>) x1a R = Functions (local.adjoint I \<sigma> \<omega>) x1a R"
          using dsem some unfolding adjoint_def by auto
        then show "Functions (local.adjoint I \<sigma> \<nu>) x1a (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<omega>) (x2a i) (x1,x2)) =
                   Functions (local.adjoint I \<sigma> \<omega>) x1a (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<omega>) (x2a i) (x1,x2))"
          by auto
      qed
    unfolding adjoint_def apply auto    
    done
next
  case (Differential \<theta>)
    assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {}) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>"
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (Differential \<theta>). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
    assume safe:"dsafe (Differential \<theta>)"
    then have free:"dfree \<theta>" by (auto dest: dsafe.cases)
    from VA have VA':"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
      by auto
    have dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
          using dfree dfree_is_dsafe by auto
    have sem:"sterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (local.adjoint I \<sigma> \<omega>) \<theta>"
      using uadmit_sterm_adjoint'[OF dsafe fsafe VA', of "\<lambda> x y. x" "\<lambda> x y. x" I] by auto
    have good1:"is_interp (adjoint I \<sigma> \<nu>)" using adjoint_safe[OF good_interp dfree] by auto
    have good2:"is_interp (adjoint I \<sigma> \<omega>)" using adjoint_safe[OF good_interp dfree] by auto
    have frech:"frechet (local.adjoint I \<sigma> \<nu>) \<theta> = frechet (local.adjoint I \<sigma> \<omega>) \<theta>"
      apply (auto simp add: fun_eq_iff)
      subgoal for a b
        using sterm_determines_frechet [OF good1 good2 free free sem, of "(a,b)"] by auto
      done
    then show "dterm_sem (local.adjoint I \<sigma> \<nu>) (Differential \<theta>) = dterm_sem (local.adjoint I \<sigma> \<omega>) (Differential \<theta>)"
      by (auto simp add: directional_derivative_def)
qed (auto)  

lemma uadmit_dterm_adjoint:
  assumes TUA:"TUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dfree f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow>  fsafe f'"
  assumes dsafe:"dsafe \<theta>"
  assumes good_interp:"is_interp I"
  shows  "dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof -
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have "\<And>x. x \<in> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> x \<in> (-U)"
    using TUA unfolding TUadmit_def by auto
  then have sub1:"(\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> -U"
    by auto
  then have VA':"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
    using agree_sub[OF sub1 VA] by auto
  then show "?thesis" using uadmit_dterm_adjoint'[OF dfree fsafe good_interp VA' dsafe] 
    by auto
qed

lemma uadmit_dterm_ntadjoint':
  assumes dfree:"\<And>i. dfree (\<sigma> i)"
  assumes good_interp:"is_interp I"
  shows  "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> = dterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  case (Plus \<theta>1 \<theta>2 \<nu> \<omega>)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta>2 = dterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>2"
    assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (Plus \<theta>1 \<theta>2)}. FVT (\<sigma> i))"
    then have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
      and VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i))"
      unfolding Vagree_def by auto
    assume safe:"dsafe (Plus \<theta>1 \<theta>2)"
  show ?case 
    using IH1[OF VA1] IH2[OF VA2] safe by auto
next
  case (Times \<theta>1 \<theta>2 \<nu> \<omega>)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta>2 = dterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>2"
    assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (Times \<theta>1 \<theta>2)}. FVT (\<sigma> i))"
    then have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
      and VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>2}. FVT (\<sigma> i))"
      unfolding Vagree_def by auto
    assume safe:"dsafe (Times \<theta>1 \<theta>2)"
  show ?case 
    using IH1[OF VA1] IH2[OF VA2] safe by auto
next
  case (Function x1a x2a)
    assume IH:"\<And>x. \<And>\<nu> \<omega>. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT x}. FVT (\<sigma> i)) \<Longrightarrow>
      dsafe x \<Longrightarrow> dterm_sem (NTadjoint I \<sigma> \<nu>) x = dterm_sem (NTadjoint I \<sigma> \<omega>) x"
    assume safe:"dsafe (Function x1a x2a)"
    from safe have safes:"\<And>j. dsafe (x2a j)" by auto
    from IH have IH':"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (x2a j)}. FVT (\<sigma> i)) \<Longrightarrow>
      dterm_sem (NTadjoint I \<sigma> \<nu>) (x2a j) = dterm_sem (NTadjoint I \<sigma> \<omega>) (x2a j)"
      using rangeI safes by auto
    assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i))"
    from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (x2a j)}. FVT (\<sigma> i))"
      unfolding Vagree_def SIGT.simps using rangeI by blast
    have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
    have VAsub:"\<And>a. x1a = Inr a\<Longrightarrow> (FVT (\<sigma> a)) \<subseteq> (\<Union> i\<in>{i. Inr i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i))"
      using SIGT by auto
    have VAf:"\<And>a. x1a = Inr a \<Longrightarrow> Vagree \<nu> \<omega> (FVT (\<sigma> a))"
      using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "x1a")
    defer
    subgoal for x1 x2 a
      proof -
        assume VA:"(\<And>a. x1a = Inr a \<Longrightarrow> Vagree \<nu> \<omega> (FVT (\<sigma> a)))"
        assume sems:"(\<And>j. \<forall>x1 x2. dterm_sem (NTadjoint I \<sigma> \<nu>) (x2a j) (x1,x2) = dterm_sem (NTadjoint I \<sigma> \<omega>) (x2a j) (x1,x2))"
        assume some:"x1a = Inr a"
        note FVT = VAf[OF some]
        have dsafe:"\<And>i. dsafe (\<sigma> i)"
          using dfree dfree_is_dsafe by auto
        have dsem:"\<And>R . dterm_sem I (\<sigma> a) \<nu> = dterm_sem I (\<sigma> a) \<omega>"
          using coincidence_dterm[OF dsafe FVT] by auto
        have "\<And>R. Functions (NTadjoint I \<sigma> \<nu>) x1a R = Functions (NTadjoint I \<sigma> \<omega>) x1a R"
          using dsem some unfolding NTadjoint_def by auto
        then show "Functions (NTadjoint I \<sigma> \<nu>) x1a (\<chi> i. dterm_sem (NTadjoint I \<sigma> \<omega>) (x2a i) (x1,x2)) =
                   Functions (NTadjoint I \<sigma> \<omega>) x1a (\<chi> i. dterm_sem (NTadjoint I \<sigma> \<omega>) (x2a i) (x1,x2))"
          by auto
      qed
    unfolding NTadjoint_def apply auto    
    done
next
  case (Differential \<theta>)
    assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> = dterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>"
    assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT (Differential \<theta>)}. FVT (\<sigma> i))"
    assume safe:"dsafe (Differential \<theta>)"
    then have free:"dfree \<theta>" by (auto dest: dsafe.cases)
    from VA have VA':"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i))"
      by auto
    have dsafe:"\<And>i. dsafe (\<sigma> i)"
          using dfree dfree_is_dsafe by auto
    have sem:"sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> = sterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>"
      using uadmit_sterm_ntadjoint'[OF dfree  VA'] by auto
    have good1:"is_interp (NTadjoint I \<sigma> \<nu>)" using NTadjoint_safe[OF good_interp dfree, of "\<lambda>i. i"] by auto
    have good2:"is_interp (NTadjoint I \<sigma> \<omega>)" using NTadjoint_safe[OF good_interp dfree, of "\<lambda>i. i"] by auto
    have frech:"frechet (NTadjoint I \<sigma> \<nu>) \<theta> = frechet (NTadjoint I \<sigma> \<omega>) \<theta>"
      apply (auto simp add: fun_eq_iff)
      subgoal for a b
        using sterm_determines_frechet [OF good1 good2 free free sem, of "(a,b)"] by auto
      done
    then show "dterm_sem (NTadjoint I \<sigma> \<nu>) (Differential \<theta>) = dterm_sem (NTadjoint I \<sigma> \<omega>) (Differential \<theta>)"
      by (auto simp add: directional_derivative_def)
qed (auto)  

lemma uadmit_dterm_ntadjoint:
  assumes TUA:"NTUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>i . dfree (\<sigma> i)"
  assumes dsafe:"dsafe \<theta>"
  assumes good_interp:"is_interp I"
  shows  "dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> = dterm_sem (NTadjoint I \<sigma> \<omega>) \<theta>"
proof -
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have "\<And>x. x \<in> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<Longrightarrow> x \<in> (-U)"
    using TUA unfolding NTUadmit_def by auto
  then have sub1:"(\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<subseteq> -U"
    by auto
  then have VA':"Vagree \<nu> \<omega> (\<Union> i\<in>{i. Inr i \<in> SIGT \<theta>}. FVT (\<sigma> i))"
    using agree_sub[OF sub1 VA] by auto
  then show "?thesis" using uadmit_dterm_ntadjoint'[OF dfree good_interp VA' dsafe] 
    by auto
qed

definition ssafe ::"('sf, 'sc, 'sz) subst \<Rightarrow> bool"
where "ssafe \<sigma> \<equiv>
  (\<forall> i f'. SFunctions \<sigma> i = Some f' \<longrightarrow> dfree f') \<and> 
  (\<forall> f f'. SPredicates \<sigma> f = Some f'  \<longrightarrow> fsafe f') \<and>
  (\<forall> f f'. SPrograms \<sigma> f = Some f'  \<longrightarrow> hpsafe f') \<and>
  (\<forall> f f'. SODEs \<sigma> f = Some f'  \<longrightarrow> osafe f') \<and>
  (\<forall> C C'. SContexts \<sigma> C = Some C'  \<longrightarrow> fsafe C')"

lemma uadmit_dterm_adjointS:
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  fixes \<nu> \<omega>
  assumes VA:"Vagree \<nu> \<omega> (\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  assumes dsafe:"dsafe \<theta>"
  shows  "dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof -
  show "?thesis" 
    apply(rule uadmit_dterm_adjoint')
    using good_interp ssafe VA dsafe unfolding ssafe_def by auto 
qed

lemma adj_sub_assign_fact:"\<And>i j e. i\<in>SIGT e \<Longrightarrow> j \<in> (case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union> {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
        {Inl x |x. x \<in> SIGT e}"
  unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> i")
    by auto
  done

lemma adj_sub_geq1_fact:"\<And>i j x1 x2. i\<in>SIGT x1 \<Longrightarrow> j \<in> (case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union> {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
        {Inl x |x. x \<in> SIGT x1 \<or> x \<in> SIGT x2}"
  unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> i")
    by auto
  done

lemma adj_sub_geq2_fact:"\<And>i j x1 x2. i\<in>SIGT x2 \<Longrightarrow> j \<in> (case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union> {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
        {Inl x |x. x \<in> SIGT x1 \<or> x \<in> SIGT x2}"
  unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> i")
    by auto
  done
lemma adj_sub_prop_fact:"\<And>i j x1 x2 k. i\<in>SIGT (x2 k) \<Longrightarrow> j \<in> (case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union> {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
         insert (Inr (Inr x1)) {Inl x |x. \<exists>xa. x \<in> SIGT (x2 xa)}"
  unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> i")
    by auto
  done

lemma adj_sub_ode_fact:"\<And>i j x1 x2. Inl i \<in> SIGO x1 \<Longrightarrow> j \<in> (case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union> {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
         (SIGF x2 \<union> {Inl x |x. Inl x \<in> SIGO x1} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO x1})"
  unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> i")
    by auto
  done

lemma adj_sub_assign:"\<And>e \<sigma> x. (\<Union>i\<in>SIGT e. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
subgoal for e \<sigma> x
 unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> j")
    apply auto
    subgoal for a
      using adj_sub_assign_fact[of j e i]
      by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5))
    done
  done
done

lemma adj_sub_diff_assign:"\<And>e \<sigma> x. (\<Union>i\<in>SIGT e. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (DiffAssign x e). SFV \<sigma> a)"
subgoal for e \<sigma> x
 unfolding SDom_def apply auto
  subgoal for i j
    apply (cases "SFunctions \<sigma> j")
    apply auto
    subgoal for a
      using adj_sub_assign_fact[of j e i]
      by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5))
    done
  done
done
   
lemma adj_sub_geq1:"\<And>\<sigma> x1 x2. (\<Union>i\<in>SIGT x1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
 subgoal for \<sigma> x1 x2
 unfolding SDom_def apply auto
  subgoal for x i
    apply (cases "SFunctions \<sigma> i")
    apply auto
    subgoal for a
      using adj_sub_geq1_fact[of i x1 x \<sigma>] 
      by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5))
    done
  done
done

lemma adj_sub_geq2:"\<And>\<sigma> x1 x2. (\<Union>i\<in>SIGT x2. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
 subgoal for \<sigma> x1 x2
 unfolding SDom_def apply auto
  subgoal for x i
    apply (cases "SFunctions \<sigma> i")
    apply auto
    subgoal for a
      using adj_sub_geq2_fact[of i x2 x \<sigma>] 
      by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5))
    done
  done
done

lemma adj_sub_prop:"\<And>\<sigma> x1 x2 j . (\<Union>i\<in>SIGT (x2 j). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> a)"
 subgoal for \<sigma> x1 x2 j
 unfolding SDom_def apply auto
  subgoal for x i
    apply (cases "SFunctions \<sigma> i")
    apply auto
    subgoal for a
      using adj_sub_prop_fact[of i x2 j x \<sigma> x1] 
      by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5))
       
    done
  done
done

lemma adj_sub_ode:"\<And>\<sigma> x1 x2. (\<Union>i\<in>{i |i. Inl i \<in> SIGO x1}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
 subgoal for \<sigma> x1 x2
 unfolding SDom_def apply auto
  subgoal for x i
    apply (cases "SFunctions \<sigma> i")
    apply auto
    subgoal for a
      using adj_sub_ode_fact[of i x1 x \<sigma> x2]
      by (metis (mono_tags, lifting) SFV.simps(1) option.simps(5)) 
    done
  done
done

lemma uadmit_ode_adjoint':
  fixes \<sigma> I
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  shows"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i \<in> {i | i. (Inl i\<in>SIGO ODE)}. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<Longrightarrow> osafe ODE \<Longrightarrow> ODE_sem (local.adjoint I \<sigma> \<nu>) ODE = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE"
proof (induction ODE)
  case (OVar x)
  then show ?case unfolding adjoint_def by auto
next
  case (OSing x1a x2)
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>{i |i. Inl i \<in> SIGO (OSing x1a x2)}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a)"
    assume osafe:"osafe (OSing x1a x2)"
    then have dfree:"dfree x2" by (auto dest: osafe.cases)
    have safes:"(\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      using ssafe unfolding ssafe_def using dfree_is_dsafe by auto
    have sem:"sterm_sem (local.adjoint I \<sigma> \<nu>) x2 = sterm_sem (local.adjoint I \<sigma> \<omega>) x2"
       using uadmit_sterm_adjoint'[of \<sigma> \<nu> \<omega> x2 I, OF safes, of "(\<lambda> x y. x)" "(\<lambda> x y. x)"] VA
       by auto
    show ?case 
      apply auto
      apply (rule ext)
      subgoal for x
        apply (rule vec_extensionality)
        using sem by auto
      done
next
  case (OProd ODE1 ODE2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE1}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a) \<Longrightarrow>
      osafe ODE1 \<Longrightarrow> ODE_sem (local.adjoint I \<sigma> \<nu>) ODE1 = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE2}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a) \<Longrightarrow>
    osafe ODE2 \<Longrightarrow> ODE_sem (local.adjoint I \<sigma> \<nu>) ODE2 = ODE_sem (local.adjoint I \<sigma> \<omega>) ODE2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>i\<in>{i |i. Inl i \<in> SIGO (OProd ODE1 ODE2)}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a)"
    assume safe:"osafe (OProd ODE1 ODE2)"
    from safe have safe1:"osafe ODE1" and safe2:"osafe ODE2" by (auto dest: osafe.cases) 
    have sub1:"(\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE1}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a) \<subseteq> (\<Union>i\<in>{i |i. Inl i \<in> SIGO (OProd ODE1 ODE2)}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a)"
      by auto
    have sub2:"(\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE2}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a) \<subseteq> (\<Union>i\<in>{i |i. Inl i \<in> SIGO (OProd ODE1 ODE2)}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some a \<Rightarrow> FVT a)"
      by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
qed

lemma uadmit_mkv_adjoint:
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  assumes VA:"Vagree \<nu> \<omega> (\<Union>i \<in> {i | i. (Inl i\<in>SIGO ODE)}. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})"
  assumes osafe:"osafe ODE"
  shows "mk_v (adjoint I \<sigma> \<nu>) ODE = mk_v (adjoint I \<sigma> \<omega>) ODE"
  apply(rule ext)
  subgoal for R
    apply(rule ext)
    subgoal for solt
      apply(rule agree_UNIV_eq)
      using mk_v_agree[of "(adjoint I \<sigma> \<nu>)" ODE "R" solt]
      using mk_v_agree[of "(adjoint I \<sigma> \<omega>)" ODE "R" solt]
      using uadmit_ode_adjoint'[OF ssafe good_interp VA osafe]
      unfolding Vagree_def
      apply auto
      apply metis
      apply metis
      done
    done
  done

lemma uadmit_prog_fml_adjoint':
  fixes \<sigma> I
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  shows "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>x\<in>SDom \<sigma> \<inter> SIGP \<alpha>. SFV \<sigma> x) \<Longrightarrow> hpsafe \<alpha> \<Longrightarrow> prog_sem (adjoint I \<sigma> \<nu>) \<alpha> = prog_sem (adjoint I \<sigma> \<omega>) \<alpha>"
  and "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>x\<in>SDom \<sigma> \<inter> SIGF \<phi>. SFV \<sigma> x) \<Longrightarrow> fsafe \<phi> \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
proof (induct "\<alpha>" and "\<phi>")
  case (Pvar x)
  then show ?case unfolding adjoint_def by auto
next
  case (Assign x e)
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
    assume safe:"hpsafe (x := e)"
    from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
    have sub:"(\<Union>i\<in>SIGT e. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
      using adj_sub_assign[of \<sigma> e x] by auto
    have "dterm_sem (local.adjoint I \<sigma> \<nu>) e = dterm_sem (local.adjoint I \<sigma> \<omega>) e"
      by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub VA] dsafe])
    then show ?case by (auto simp add: vec_eq_iff)
next
  case (DiffAssign x e)
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (DiffAssign x e). SFV \<sigma> a)"
    assume safe:"hpsafe (DiffAssign x e)"
    from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
    have sub:"(\<Union>i\<in>SIGT e. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (DiffAssign x e). SFV \<sigma> a)"
      using adj_sub_diff_assign[of \<sigma> e] by auto
    have "dterm_sem (local.adjoint I \<sigma> \<nu>) e = dterm_sem (local.adjoint I \<sigma> \<omega>) e"
      by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub VA] dsafe])
    then show ?case by (auto simp add: vec_eq_iff)
next
  case (Test x)
    assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<Longrightarrow> fsafe x \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) x = fml_sem (adjoint I \<sigma> \<omega>) x"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (? x). SFV \<sigma> a)"
    assume hpsafe:"hpsafe (? x)"
    then have fsafe:"fsafe x" by (auto dest: hpsafe.cases)
    have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (? x). SFV \<sigma> a)"
      by auto
    have "fml_sem (adjoint I \<sigma> \<nu>) x = fml_sem (adjoint I \<sigma> \<omega>) x"
      using IH[OF agree_sub[OF sub VA] fsafe] by auto
  then show ?case by auto
next
  case (EvolveODE x1 x2)
    assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
    assume safe:"hpsafe (EvolveODE x1 x2)"
    then have osafe:"osafe x1" and fsafe:"fsafe x2" by (auto dest: hpsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
      by auto
    then have VAF:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a)"
      using agree_sub[OF sub1 VA] by auto 
    note IH' = IH[OF VAF fsafe]
    have sub:"(\<Union>i\<in>{i |i. Inl i \<in> SIGO x1}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
      using adj_sub_ode[of \<sigma> x1 x2] by auto
    moreover have IH2:"ODE_sem (local.adjoint I \<sigma> \<nu>) x1 = ODE_sem (local.adjoint I \<sigma> \<omega>) x1"
      apply (rule uadmit_ode_adjoint')
      subgoal by (rule ssafe)
      subgoal by (rule good_interp)
      subgoal using agree_sub[OF sub VA] by auto
      subgoal by (rule osafe)
      done
    have mkv:"mk_v (adjoint I \<sigma> \<nu>) x1 = mk_v (adjoint I \<sigma> \<omega>) x1"
      apply (rule uadmit_mkv_adjoint)
      using ssafe good_interp osafe agree_sub[OF sub VA] by auto
    show ?case 
      apply auto
      subgoal for aa ba bb sol t
        apply(rule exI[where x = sol])
        apply(rule conjI)
        subgoal by auto
        apply(rule exI[where x=t])
        apply(rule conjI)
        subgoal using mkv by auto
        apply(rule conjI)
        subgoal by auto using IH2 mkv IH' by auto
      subgoal for aa ba bb sol t
        apply(rule exI[where x = sol])
        apply(rule conjI)
        subgoal by auto
        apply(rule exI[where x=t])
        apply(rule conjI)
        subgoal using mkv by auto
        apply(rule conjI)
        subgoal by auto using IH2 mkv IH' by auto
      done
next
  case (Choice x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x1 = prog_sem (local.adjoint I \<sigma> \<omega>) x1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x2 = prog_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 \<union>\<union> x2). SFV \<sigma> a)"
    assume safe:"hpsafe (x1 \<union>\<union> x2)"
    from safe have
      safe1:"hpsafe x1"
      and safe2:"hpsafe x2"
      by (auto dest: hpsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 \<union>\<union> x2). SFV \<sigma> a)"
      by auto
    have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 \<union>\<union> x2). SFV \<sigma> a)"
      by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Sequence x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x1 = prog_sem (local.adjoint I \<sigma> \<omega>) x1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x2 = prog_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 ;; x2). SFV \<sigma> a)"
    assume safe:"hpsafe (x1 ;; x2)"
    from safe have
      safe1:"hpsafe x1"
      and safe2:"hpsafe x2"
      by (auto dest: hpsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 ;; x2). SFV \<sigma> a)"
      by auto
    have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 ;; x2). SFV \<sigma> a)"
      by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Loop x)
    assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x. SFV \<sigma> a) \<Longrightarrow> hpsafe x \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x = prog_sem (local.adjoint I \<sigma> \<omega>) x"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x**). SFV \<sigma> a)"
    assume safe:"hpsafe (x**)"
    from safe have
      safe:"hpsafe x"
      by (auto dest: hpsafe.cases)
    have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x**). SFV \<sigma> a)"
      by auto
    show ?case using IH[OF agree_sub[OF sub VA] safe] by auto
next
  case (Geq x1 x2)
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe (Geq x1 x2)"
    then have dsafe1:"dsafe x1" and dsafe2:"dsafe x2" by (auto dest: fsafe.cases)
    have sub1:"(\<Union>i\<in>SIGT x1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
      using adj_sub_geq1[of \<sigma> x1 x2] by auto
    have sub2:"(\<Union>i\<in>SIGT x2. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
      using adj_sub_geq2[of \<sigma> x2 x1] by auto
    have "dterm_sem (local.adjoint I \<sigma> \<nu>) x1 = dterm_sem (local.adjoint I \<sigma> \<omega>) x1"
      by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub1 VA] dsafe1])
    moreover have "dterm_sem (local.adjoint I \<sigma> \<nu>) x2 = dterm_sem (local.adjoint I \<sigma> \<omega>) x2"
      by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub2 VA] dsafe2])
    ultimately show ?case by auto
next
  case (Prop x1 x2 \<nu> \<omega>)
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe ($\<phi> x1 x2)"
    from safe have frees:"\<And>i. dfree (x2 i)"
      by (auto dest: fsafe.cases)
    then have safes:"\<And>i. dsafe (x2 i)" using dfree_is_dsafe by auto
    have subs:"\<And>j. (\<Union>i\<in>SIGT (x2 j). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> a)"
      subgoal for j using adj_sub_prop[of \<sigma> x2 j x1] by auto
      done
    have "\<And>i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) = dterm_sem (local.adjoint I \<sigma> \<omega>) (x2 i)"
      by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF subs VA] safes])
    then have vec_eq:"\<And>R. (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) R) = (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<omega>) (x2 i) R)"
      by (auto simp add: vec_eq_iff)
    from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2 j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
      unfolding Vagree_def SIGT.simps using rangeI 
      by (metis (no_types, lifting) set_mp subs)
    have SIGF:"\<And>a. SPredicates \<sigma> x1 = Some a \<Longrightarrow> Inr (Inr x1) \<in> SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2)" unfolding SDom_def
      by auto
    have VAsub:"\<And>a. SPredicates \<sigma> x1 = Some a \<Longrightarrow> (FVF a) \<subseteq> (\<Union>i\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> i)"
      using SIGF by auto
    have VAf:"\<And>a. SPredicates \<sigma> x1 = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVF a)"
      using agree_sub[OF VAsub VA] by auto
    then show ?case 
      apply(cases "SPredicates \<sigma> x1")
      defer
      subgoal for a
      proof -
        assume some:"SPredicates \<sigma> x1 = Some a"
        note FVF = VAf[OF some]
        have dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
          using ssafe dfree_is_dsafe unfolding ssafe_def by auto
        have dsem:"\<And>R . (\<nu> \<in> fml_sem (extendf I R) a) = (\<omega> \<in> fml_sem (extendf I R) a)"
          subgoal for R
            apply (rule coincidence_formula)
            subgoal using ssafe unfolding ssafe_def using some by auto
            subgoal unfolding Iagree_def by auto
            subgoal by (rule FVF)
          done
        done
        have pred_eq:"\<And>R. Predicates (local.adjoint I \<sigma> \<nu>) x1 R = Predicates (local.adjoint I \<sigma> \<omega>) x1 R"
          using dsem some unfolding adjoint_def by auto
         show "fml_sem (local.adjoint I \<sigma> \<nu>) ($\<phi> x1 x2) = fml_sem (local.adjoint I \<sigma> \<omega>) ($\<phi> x1 x2)"
          apply auto
          subgoal for a b using pred_eq[of "(\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) (a, b))"] vec_eq by auto
          subgoal for a b using pred_eq[of "(\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) (a, b))"] vec_eq by auto
          done
      qed
      unfolding adjoint_def using local.adjoint_def local.vec_eq apply auto
      done
next
  case (Not x)
    assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<Longrightarrow> fsafe x \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x = fml_sem (local.adjoint I \<sigma> \<omega>) x"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Not x). SFV \<sigma> a)"
    assume safe:"fsafe (Not x)"
    from safe have
      safe:"fsafe x"
      by (auto dest: fsafe.cases)
    have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Not x). SFV \<sigma> a)"
      by auto
    show ?case using IH[OF agree_sub[OF sub VA] safe] by auto
next
  case (And x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x1. SFV \<sigma> a) \<Longrightarrow> fsafe x1 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x1 = fml_sem (local.adjoint I \<sigma> \<omega>) x1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (And x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe (And x1 x2)"
    from safe have
      safe1:"fsafe x1"
  and safe2:"fsafe x2"
      by (auto dest: fsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (And x1 x2). SFV \<sigma> a)"
      by auto
    have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (And x1 x2). SFV \<sigma> a)"
      by auto
    show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Exists x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Exists x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe (Exists x1 x2)"
    from safe have safe1:"fsafe x2"
      by (auto dest: fsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Exists x1 x2). SFV \<sigma> a)"
      by auto
    show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] by auto
next
  case (Diamond x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x1 = prog_sem (local.adjoint I \<sigma> \<omega>) x1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Diamond x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe (Diamond x1 x2)"
    from safe have
      safe1:"hpsafe x1"
  and safe2:"fsafe x2"
      by (auto dest: fsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Diamond x1 x2). SFV \<sigma> a)"
      by auto
    have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Diamond x1 x2). SFV \<sigma> a)"
      by auto
    show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (DiffFormula x)
  then show ?case sorry
next
  case (InContext x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (InContext x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe (InContext x1 x2)"
    from safe have  safe1:"fsafe x2"
      by (auto dest: fsafe.cases)
    have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (InContext x1 x2). SFV \<sigma> a)"
      by auto
    show ?case using IH1[OF agree_sub[OF sub VA] safe1]  
      unfolding adjoint_def by auto
qed
 
lemma uadmit_prog_adjoint:
  assumes PUA:"PUadmit \<sigma> a U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes hpsafe:"hpsafe a"
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  shows "prog_sem (adjoint I \<sigma> \<nu>) a = prog_sem (adjoint I \<sigma> \<omega>) a"
  proof -
    have sub:"(\<Union>x\<in>SDom \<sigma> \<inter> SIGP a. SFV \<sigma> x) \<subseteq> -U" using PUA unfolding PUadmit_def by auto
    have VA':"Vagree \<nu> \<omega> (\<Union>x\<in>SDom \<sigma> \<inter> SIGP a. SFV \<sigma> x)" using agree_sub[OF sub VA] by auto
    show ?thesis 
      apply(rule uadmit_prog_fml_adjoint'[OF ssafe good_interp])
      subgoal by (rule VA')
      subgoal by (rule hpsafe)
      done
  qed

lemma uadmit_fml_adjoint:
  assumes FUA:"FUadmit \<sigma> \<phi> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes fsafe:"fsafe \<phi>"
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  shows "fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
  proof -
    have sub:"(\<Union>x\<in>SDom \<sigma> \<inter> SIGF \<phi>. SFV \<sigma> x) \<subseteq> -U" using FUA unfolding FUadmit_def by auto
    have VA':"Vagree \<nu> \<omega> (\<Union>x\<in>SDom \<sigma> \<inter> SIGF \<phi>. SFV \<sigma> x)" using agree_sub[OF sub VA] by auto
    show ?thesis 
      apply(rule uadmit_prog_fml_adjoint'[OF ssafe good_interp])
      subgoal by (rule VA')
      subgoal by (rule fsafe)
      done
  qed

lemma uadmit_prog_fml_ntadjoint':
  fixes \<sigma> I
  assumes ssafe:"\<And>i. dfree (\<sigma> i)"
  assumes good_interp:"is_interp I"
  shows "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (Inl x) \<in> SIGP \<alpha>}. FVT (\<sigma> x)) \<Longrightarrow> hpsafe \<alpha> \<Longrightarrow> prog_sem (NTadjoint I \<sigma> \<nu>) \<alpha> = prog_sem (NTadjoint I \<sigma> \<omega>) \<alpha>"
  and "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (Inl x) \<in> SIGF \<phi>}. FVT (\<sigma> x)) \<Longrightarrow> fsafe \<phi> \<Longrightarrow> fml_sem (NTadjoint I \<sigma> \<nu>) \<phi> = fml_sem (NTadjoint I \<sigma> \<omega>) \<phi>"
    sorry
(*proof (induct "\<alpha>" and "\<phi>")
  case (Pvar x)
  then show ?case unfolding adjoint_def by auto
next
  case (Assign x e)
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
    assume safe:"hpsafe (x := e)"
    from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
    have sub:"(\<Union>i\<in>SIGT e. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
      using adj_sub_assign[of \<sigma> e x] by auto
    have "dterm_sem (local.adjoint I \<sigma> \<nu>) e = dterm_sem (local.adjoint I \<sigma> \<omega>) e"
      by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub VA] dsafe])
    then show ?case by (auto simp add: vec_eq_iff)
next
  case (DiffAssign x e)
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (DiffAssign x e). SFV \<sigma> a)"
    assume safe:"hpsafe (DiffAssign x e)"
    from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
    have sub:"(\<Union>i\<in>SIGT e. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (DiffAssign x e). SFV \<sigma> a)"
      using adj_sub_diff_assign[of \<sigma> e] by auto
    have "dterm_sem (local.adjoint I \<sigma> \<nu>) e = dterm_sem (local.adjoint I \<sigma> \<omega>) e"
      by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub VA] dsafe])
    then show ?case by (auto simp add: vec_eq_iff)
next
  case (Test x)
    assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<Longrightarrow> fsafe x \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) x = fml_sem (adjoint I \<sigma> \<omega>) x"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (? x). SFV \<sigma> a)"
    assume hpsafe:"hpsafe (? x)"
    then have fsafe:"fsafe x" by (auto dest: hpsafe.cases)
    have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (? x). SFV \<sigma> a)"
      by auto
    have "fml_sem (adjoint I \<sigma> \<nu>) x = fml_sem (adjoint I \<sigma> \<omega>) x"
      using IH[OF agree_sub[OF sub VA] fsafe] by auto
  then show ?case by auto
next
  case (EvolveODE x1 x2)
    assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
    assume safe:"hpsafe (EvolveODE x1 x2)"
    then have osafe:"osafe x1" and fsafe:"fsafe x2" by (auto dest: hpsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
      by auto
    then have VAF:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a)"
      using agree_sub[OF sub1 VA] by auto 
    note IH' = IH[OF VAF fsafe]
    have sub:"(\<Union>i\<in>{i |i. Inl i \<in> SIGO x1}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
      using adj_sub_ode[of \<sigma> x1 x2] by auto
    moreover have IH2:"ODE_sem (local.adjoint I \<sigma> \<nu>) x1 = ODE_sem (local.adjoint I \<sigma> \<omega>) x1"
      apply (rule uadmit_ode_adjoint')
      subgoal by (rule ssafe)
      subgoal by (rule good_interp)
      subgoal using agree_sub[OF sub VA] by auto
      subgoal by (rule osafe)
      done
    have mkv:"mk_v (adjoint I \<sigma> \<nu>) x1 = mk_v (adjoint I \<sigma> \<omega>) x1"
      apply (rule uadmit_mkv_adjoint)
      using ssafe good_interp osafe agree_sub[OF sub VA] by auto
    show ?case 
      apply auto
      subgoal for aa ba bb sol t
        apply(rule exI[where x = sol])
        apply(rule conjI)
        subgoal by auto
        apply(rule exI[where x=t])
        apply(rule conjI)
        subgoal using mkv by auto
        apply(rule conjI)
        subgoal by auto using IH2 mkv IH' by auto
      subgoal for aa ba bb sol t
        apply(rule exI[where x = sol])
        apply(rule conjI)
        subgoal by auto
        apply(rule exI[where x=t])
        apply(rule conjI)
        subgoal using mkv by auto
        apply(rule conjI)
        subgoal by auto using IH2 mkv IH' by auto
      done
next
  case (Choice x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x1 = prog_sem (local.adjoint I \<sigma> \<omega>) x1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x2 = prog_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 \<union>\<union> x2). SFV \<sigma> a)"
    assume safe:"hpsafe (x1 \<union>\<union> x2)"
    from safe have
      safe1:"hpsafe x1"
      and safe2:"hpsafe x2"
      by (auto dest: hpsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 \<union>\<union> x2). SFV \<sigma> a)"
      by auto
    have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 \<union>\<union> x2). SFV \<sigma> a)"
      by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Sequence x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x1 = prog_sem (local.adjoint I \<sigma> \<omega>) x1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x2 = prog_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 ;; x2). SFV \<sigma> a)"
    assume safe:"hpsafe (x1 ;; x2)"
    from safe have
      safe1:"hpsafe x1"
      and safe2:"hpsafe x2"
      by (auto dest: hpsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 ;; x2). SFV \<sigma> a)"
      by auto
    have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x1 ;; x2). SFV \<sigma> a)"
      by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Loop x)
    assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x. SFV \<sigma> a) \<Longrightarrow> hpsafe x \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x = prog_sem (local.adjoint I \<sigma> \<omega>) x"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x** ). SFV \<sigma> a)"
    assume safe:"hpsafe (x** )"
    from safe have
      safe:"hpsafe x"
      by (auto dest: hpsafe.cases)
    have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x** ). SFV \<sigma> a)"
      by auto
    show ?case using IH[OF agree_sub[OF sub VA] safe] by auto
next
  case (Geq x1 x2)
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe (Geq x1 x2)"
    then have dsafe1:"dsafe x1" and dsafe2:"dsafe x2" by (auto dest: fsafe.cases)
    have sub1:"(\<Union>i\<in>SIGT x1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
      using adj_sub_geq1[of \<sigma> x1 x2] by auto
    have sub2:"(\<Union>i\<in>SIGT x2. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
      using adj_sub_geq2[of \<sigma> x2 x1] by auto
    have "dterm_sem (local.adjoint I \<sigma> \<nu>) x1 = dterm_sem (local.adjoint I \<sigma> \<omega>) x1"
      by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub1 VA] dsafe1])
    moreover have "dterm_sem (local.adjoint I \<sigma> \<nu>) x2 = dterm_sem (local.adjoint I \<sigma> \<omega>) x2"
      by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub2 VA] dsafe2])
    ultimately show ?case by auto
next
  case (Prop x1 x2 \<nu> \<omega>)
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe ($\<phi> x1 x2)"
    from safe have frees:"\<And>i. dfree (x2 i)"
      by (auto dest: fsafe.cases)
    then have safes:"\<And>i. dsafe (x2 i)" using dfree_is_dsafe by auto
    have subs:"\<And>j. (\<Union>i\<in>SIGT (x2 j). case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> a)"
      subgoal for j using adj_sub_prop[of \<sigma> x2 j x1] by auto
      done
    have "\<And>i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) = dterm_sem (local.adjoint I \<sigma> \<omega>) (x2 i)"
      by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF subs VA] safes])
    then have vec_eq:"\<And>R. (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) R) = (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<omega>) (x2 i) R)"
      by (auto simp add: vec_eq_iff)
    from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union>i\<in>SIGT (x2 j). case SFunctions \<sigma> i of Some a \<Rightarrow> FVT a | None \<Rightarrow> {})"
      unfolding Vagree_def SIGT.simps using rangeI 
      by (metis (no_types, lifting) set_mp subs)
    have SIGF:"\<And>a. SPredicates \<sigma> x1 = Some a \<Longrightarrow> Inr (Inr x1) \<in> SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2)" unfolding SDom_def
      by auto
    have VAsub:"\<And>a. SPredicates \<sigma> x1 = Some a \<Longrightarrow> (FVF a) \<subseteq> (\<Union>i\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> i)"
      using SIGF by auto
    have VAf:"\<And>a. SPredicates \<sigma> x1 = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVF a)"
      using agree_sub[OF VAsub VA] by auto
    then show ?case 
      apply(cases "SPredicates \<sigma> x1")
      defer
      subgoal for a
      proof -
        assume some:"SPredicates \<sigma> x1 = Some a"
        note FVF = VAf[OF some]
        have dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
          using ssafe dfree_is_dsafe unfolding ssafe_def by auto
        have dsem:"\<And>R . (\<nu> \<in> fml_sem (extendf I R) a) = (\<omega> \<in> fml_sem (extendf I R) a)"
          subgoal for R
            apply (rule coincidence_formula)
            subgoal using ssafe unfolding ssafe_def using some by auto
            subgoal unfolding Iagree_def by auto
            subgoal by (rule FVF)
          done
        done
        have pred_eq:"\<And>R. Predicates (local.adjoint I \<sigma> \<nu>) x1 R = Predicates (local.adjoint I \<sigma> \<omega>) x1 R"
          using dsem some unfolding adjoint_def by auto
         show "fml_sem (local.adjoint I \<sigma> \<nu>) ($\<phi> x1 x2) = fml_sem (local.adjoint I \<sigma> \<omega>) ($\<phi> x1 x2)"
          apply auto
          subgoal for a b using pred_eq[of "(\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) (a, b))"] vec_eq by auto
          subgoal for a b using pred_eq[of "(\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (x2 i) (a, b))"] vec_eq by auto
          done
      qed
      unfolding adjoint_def using local.adjoint_def local.vec_eq apply auto
      done
next
  case (Not x)
    assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<Longrightarrow> fsafe x \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x = fml_sem (local.adjoint I \<sigma> \<omega>) x"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Not x). SFV \<sigma> a)"
    assume safe:"fsafe (Not x)"
    from safe have
      safe:"fsafe x"
      by (auto dest: fsafe.cases)
    have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Not x). SFV \<sigma> a)"
      by auto
    show ?case using IH[OF agree_sub[OF sub VA] safe] by auto
next
  case (And x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x1. SFV \<sigma> a) \<Longrightarrow> fsafe x1 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x1 = fml_sem (local.adjoint I \<sigma> \<omega>) x1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (And x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe (And x1 x2)"
    from safe have
      safe1:"fsafe x1"
  and safe2:"fsafe x2"
      by (auto dest: fsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (And x1 x2). SFV \<sigma> a)"
      by auto
    have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (And x1 x2). SFV \<sigma> a)"
      by auto
    show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Exists x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Exists x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe (Exists x1 x2)"
    from safe have safe1:"fsafe x2"
      by (auto dest: fsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Exists x1 x2). SFV \<sigma> a)"
      by auto
    show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] by auto
next
  case (Diamond x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (local.adjoint I \<sigma> \<nu>) x1 = prog_sem (local.adjoint I \<sigma> \<omega>) x1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Diamond x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe (Diamond x1 x2)"
    from safe have
      safe1:"hpsafe x1"
  and safe2:"fsafe x2"
      by (auto dest: fsafe.cases)
    have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Diamond x1 x2). SFV \<sigma> a)"
      by auto
    have sub2:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Diamond x1 x2). SFV \<sigma> a)"
      by auto
    show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (DiffFormula x)
  then show ?case sorry
next
  case (InContext x1 x2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (local.adjoint I \<sigma> \<nu>) x2 = fml_sem (local.adjoint I \<sigma> \<omega>) x2"
    assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (InContext x1 x2). SFV \<sigma> a)"
    assume safe:"fsafe (InContext x1 x2)"
    from safe have  safe1:"fsafe x2"
      by (auto dest: fsafe.cases)
    have sub:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (InContext x1 x2). SFV \<sigma> a)"
      by auto
    show ?case using IH1[OF agree_sub[OF sub VA] safe1]  
      unfolding adjoint_def by auto
qed
*)

lemma uadmit_prog_ntadjoint:
  fixes \<alpha> :: "('sf + 'sf::finite,'sc,'sz) hp"
  assumes TUA:"NPUadmit \<sigma> \<alpha> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>i . dfree (\<sigma> i)"
  assumes hpsafe:"hpsafe \<alpha>"
  assumes good_interp:"is_interp I"
  shows  "prog_sem (NTadjoint I \<sigma> \<nu>) \<alpha> = prog_sem (NTadjoint I \<sigma> \<omega>) \<alpha>"
proof -
    have sub:"(\<Union>x\<in>{x. Inl (Inl x) \<in> SIGP \<alpha>}. FVT (\<sigma> x)) \<subseteq> -U" using TUA unfolding NPUadmit_def by auto
    have VA':"Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (Inl x) \<in> SIGP \<alpha>}. FVT (\<sigma> x))" using agree_sub[OF sub VA] by auto
    show ?thesis 
      apply(rule uadmit_prog_fml_ntadjoint'[OF dfree good_interp])
      subgoal by (rule VA')
      subgoal by (rule hpsafe)
      done
qed

lemma uadmit_fml_ntadjoint:
  fixes \<phi> :: "('sf + 'sf::finite,'sc,'sz) formula"
  assumes TUA:"NFUadmit \<sigma> \<phi> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>i . dfree (\<sigma> i)"
  assumes fsafe:"fsafe \<phi>"
  assumes good_interp:"is_interp I"
  shows  "fml_sem (NTadjoint I \<sigma> \<nu>) \<phi> = fml_sem (NTadjoint I \<sigma> \<omega>) \<phi>"
proof -
  have sub:"(\<Union>x\<in>{x. Inl (Inl x) \<in> SIGF \<phi>}. FVT (\<sigma> x)) \<subseteq> -U" using TUA unfolding NFUadmit_def by auto
  have VA':"Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (Inl x) \<in> SIGF \<phi>}. FVT (\<sigma> x))" using agree_sub[OF sub VA] by auto
  show ?thesis 
    apply(rule uadmit_prog_fml_ntadjoint'[OF dfree good_interp])
    subgoal by (rule VA')
    subgoal by (rule fsafe)
    done
qed

lemma nsubst_sterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
shows "dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> sterm_sem I (NTsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induction rule: dfree.induct)
  case (dfree_Fun args f) then
    show "?case" 
      by(cases "f") (auto simp add:  NTadjoint_free)
qed (auto)

lemma nsubst_sterm':
fixes I::"('sf, 'sc, 'sz) interp"
fixes a b::"'sz simple_state"
shows "dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> sterm_sem I (NTsubst \<theta> \<sigma>) a = sterm_sem (NTadjoint I \<sigma> (a,b)) \<theta> a"
  using nsubst_sterm by (metis fst_conv)

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

lemma tsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dsafe(Tsubst \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Fun args i) 
    assume dsafes:"\<And>i. dsafe (args i)"
    assume IH:"\<And>j. (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dsafe (Tsubst (args j) \<sigma>)"
    assume frees:"\<And>i f. SFunctions \<sigma> i = Some f \<Longrightarrow> dfree f"
    have IH':"\<And>i. dsafe (Tsubst (args i) \<sigma>)"
      using frees IH by auto
  then show "?case" 
    apply auto
    apply(cases "SFunctions \<sigma> i")
    subgoal using IH frees by auto
    subgoal for a using frees[of i a] ntsubst_free_to_safe[of a] IH' by auto
    done 
qed (auto intro: dsafe.intros tsubst_preserves_free)

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
      have sem_eq:"\<And>\<nu>'. dsafe \<theta> \<Longrightarrow> is_interp I \<Longrightarrow> dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (local.adjoint I \<sigma> \<nu>') \<theta>"
        subgoal for \<nu>'
          using uadmit_dterm_adjoint[OF TUA VA sfree spsafe, of "(\<lambda> x y. x)" "(\<lambda> x y. x)" I \<nu> \<nu>']
          by auto
        done
      have IH'':"\<And>\<nu>'. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu>' = dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> \<nu>'"
        subgoal for \<nu>'
          using sem_eq[OF tsafe good_interp, of \<nu>'] IH'[of \<nu>'] by auto
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
        using sterm_determines_frechet[OF 
            good_interp 
            adjoint_safe[OF good_interp sfree] 
            tsubst_preserves_free[OF free sfree] 
            free sem_eq]
        by auto
  qed auto  

lemma osubst_preserves_safe:
assumes ssafe:"ssafe \<sigma>"
shows "(osafe ODE \<Longrightarrow> Oadmit \<sigma> ODE U \<Longrightarrow> osafe (Osubst ODE \<sigma>))"
proof (induction rule: osafe.induct)
  case (osafe_Var c)
  then show ?case using ssafe unfolding ssafe_def by (cases "SODEs \<sigma> c", auto intro: osafe.intros)
next
  case (osafe_Sing \<theta> x)
    then show ?case 
      using tsubst_preserves_free ssafe unfolding ssafe_def by (auto intro: osafe.intros)
next
  case (osafe_Prod ODE1 ODE2)
  moreover have "Oadmit \<sigma> ODE1 U" "Oadmit \<sigma> ODE2 U" "ODE_dom (Osubst ODE1 \<sigma>) \<inter>  ODE_dom (Osubst ODE2 \<sigma>) = {}"
    using osafe_Prod.prems by (auto dest: Oadmit.cases) 
  ultimately show ?case by (auto intro: osafe.intros)
qed

lemma nosubst_preserves_safe:
assumes sfree:"\<And>i. dfree (\<sigma> i)"
fixes \<alpha> ::"('a + 'd, 'b, 'c) hp" and \<phi> ::"('a + 'd, 'b, 'c) formula"
shows "(osafe ODE \<Longrightarrow> NOUadmit \<sigma> ODE U \<Longrightarrow> osafe (NOsubst ODE \<sigma>))"
proof (induction rule: osafe.induct)
  case (osafe_Var c)
  then show ?case by (auto intro: osafe.intros)
next
  case (osafe_Sing \<theta> x)
  then show ?case using sfree ntsubst_preserves_free[of \<theta> \<sigma>] unfolding NOUadmit_def by (auto intro: osafe.intros)
next
  case (osafe_Prod ODE1 ODE2)
    assume safe1:"osafe ODE1"
    and safe2:"osafe ODE2"
    and disj:"ODE_dom ODE1 \<inter> ODE_dom ODE2 = {}"
    and IH1:"NOUadmit \<sigma> ODE1 U \<Longrightarrow> osafe (NOsubst ODE1 \<sigma>)"
    and IH2:"NOUadmit \<sigma> ODE2 U \<Longrightarrow> osafe (NOsubst ODE2 \<sigma>)"
    and NOUA:"NOUadmit \<sigma> (OProd ODE1 ODE2) U"    
    have nosubst_preserves_ODE_dom:"\<And>ODE. ODE_dom (NOsubst ODE \<sigma>) = ODE_dom ODE"
      subgoal for ODE
        apply(induction "ODE")
        by auto
      done
    have disj':"ODE_dom (NOsubst ODE1 \<sigma>) \<inter> ODE_dom (NOsubst ODE2 \<sigma>) = {}"
      using disj nosubst_preserves_ODE_dom by auto
    from NOUA have NOUA1:"NOUadmit \<sigma> ODE1 U" and NOUA2:"NOUadmit \<sigma>  ODE2 U"  unfolding NOUadmit_def by auto
  then show ?case using IH1[OF NOUA1] IH2[OF NOUA2] disj' by (auto intro: osafe.intros)
qed
  
lemma npsubst_nfsubst_preserves_safe:
assumes sfree:"\<And>i. dfree (\<sigma> i)"
fixes \<alpha> ::"('a + 'd, 'b, 'c) hp" and \<phi> ::"('a + 'd, 'b, 'c) formula"
shows "(hpsafe \<alpha> \<longrightarrow> NPadmit \<sigma> \<alpha> \<longrightarrow> hpsafe (NPsubst \<alpha> \<sigma>)) \<and> 
    (fsafe \<phi> \<longrightarrow> NFadmit \<sigma> \<phi> \<longrightarrow> fsafe (NFsubst \<phi> \<sigma>))"
proof (induction rule: hpsafe_fsafe.induct)
  case (hpsafe_Pvar x)
  then show ?case by (auto intro: hpsafe_fsafe.intros)
next
  case (hpsafe_Assign e x)
  then show ?case using ntsubst_preserves_safe sfree by (auto intro: hpsafe_fsafe.intros)
next
  case (hpsafe_DiffAssign e x)
  then show ?case using ntsubst_preserves_safe sfree by (auto intro: hpsafe_fsafe.intros)
next
  case (hpsafe_Evolve ODE P)
  then show ?case using nosubst_preserves_safe sfree by (auto intro: hpsafe_fsafe.intros) 
next
  case (fsafe_Geq t1 t2)
  then show ?case using ntsubst_preserves_safe sfree by (auto intro: hpsafe_fsafe.intros)
next
  case (fsafe_Prop args p)
  then show ?case using sfree ntsubst_preserves_free sfree by (auto intro: hpsafe_fsafe.intros)
next
  case (fsafe_DiffFormula p)
  then show ?case sorry
qed (auto intro: hpsafe_fsafe.intros)

lemma npsubst_preserves_safe:
assumes sfree:"\<And>i. dfree (\<sigma> i)"
fixes \<alpha> ::"('a + 'd, 'b, 'c) hp"
assumes safe:"hpsafe \<alpha>"
assumes admit:"NPadmit \<sigma> \<alpha>"
shows "hpsafe (NPsubst \<alpha> \<sigma>)"
using npsubst_nfsubst_preserves_safe sfree safe admit by auto

lemma nfsubst_preserves_safe:
assumes sfree:"\<And>i. dfree (\<sigma> i)"
fixes \<phi> ::"('a + 'd, 'b, 'c) formula"
assumes safe:"fsafe \<phi>"
assumes admit:"NFadmit \<sigma> \<phi>"
shows "fsafe (NFsubst \<phi> \<sigma>)"
using npsubst_nfsubst_preserves_safe sfree safe admit by auto

lemma ppsubst_pfsubst_preserves_safe:
assumes sfree:"\<And>i. fsafe (\<sigma> i)"
fixes \<alpha> ::"('a, 'b + 'd, 'c) hp" and \<phi> ::"('a, 'b + 'd, 'c) formula"
shows "(hpsafe \<alpha> \<longrightarrow> PPadmit \<sigma> \<alpha> \<longrightarrow> hpsafe (PPsubst \<alpha> \<sigma>)) \<and> 
    (fsafe \<phi> \<longrightarrow> PFadmit \<sigma> \<phi> \<longrightarrow> fsafe (PFsubst \<phi> \<sigma>))"
proof (induction rule: hpsafe_fsafe.induct)
  case (fsafe_InContext f C)
  then show ?case using sfree ntsubst_preserves_free sfree 
    by (cases "C", auto intro: hpsafe_fsafe.intros)
next
  case (hpsafe_Evolve ODE P)
  then show ?case using nosubst_preserves_safe sfree 
    by (auto intro: hpsafe_fsafe.intros)
next
  case (fsafe_DiffFormula p)
  then show ?case sorry
qed (auto intro: hpsafe_fsafe.intros)

lemma ppsubst_preserves_safe:
assumes sfree:"\<And>i. fsafe (\<sigma> i)"
assumes safe:"hpsafe \<alpha>"
assumes PPA:"PPadmit \<sigma> \<alpha>"
shows "hpsafe (PPsubst \<alpha> \<sigma>)"
    using sfree safe PPA ppsubst_pfsubst_preserves_safe by auto

lemma pfsubst_preserves_safe:
assumes sfree:"\<And>i. fsafe (\<sigma> i)"
assumes safe:"fsafe \<phi>"
assumes PFA:"PFadmit \<sigma> \<phi>"
shows "fsafe (PFsubst \<phi> \<sigma>)"
    using sfree safe PFA ppsubst_pfsubst_preserves_safe by auto

lemma psubst_fsubst_preserves_safe:
assumes ssafe:"ssafe \<sigma>"
shows "(hpsafe \<alpha> \<longrightarrow> Padmit \<sigma> \<alpha> \<longrightarrow> hpsafe (Psubst \<alpha> \<sigma>)) \<and>
   (fsafe \<phi> \<longrightarrow> Fadmit \<sigma> \<phi> \<longrightarrow> fsafe (Fsubst \<phi> \<sigma>))"
proof (induction rule: hpsafe_fsafe.induct)
  case (hpsafe_Pvar x)
  then show ?case 
    using ssafe unfolding ssafe_def by (cases "SPrograms \<sigma> x", auto intro: hpsafe_fsafe.intros)
next
  case (hpsafe_Assign e x) then
  show ?case
    using tsubst_preserves_safe ssafe unfolding ssafe_def by (auto intro: hpsafe_fsafe.intros)    
next
  case (hpsafe_DiffAssign e x) then 
  show ?case
    using tsubst_preserves_safe ssafe unfolding ssafe_def by (auto intro: hpsafe_fsafe.intros)
next
  case (hpsafe_Evolve ODE P) then
    have osafe:"osafe ODE"
    and fsafe:"fsafe P"
    and IH:"Fadmit \<sigma> P \<Longrightarrow> fsafe (Fsubst P \<sigma>)"
      by auto
    have "Padmit \<sigma> (EvolveODE ODE P) \<Longrightarrow>  hpsafe (Psubst (EvolveODE ODE P) \<sigma>)"
    proof -
      assume PA:"Padmit \<sigma> (EvolveODE ODE P)"
      have OA:"Oadmit \<sigma> ODE (ODE_vars ODE)" and FA:"Fadmit \<sigma>  P" using PA by (auto dest: Padmit.cases)
      show "?thesis"
        using osubst_preserves_safe[of \<sigma> ODE, OF ssafe osafe OA] IH[OF FA] by (auto intro: hpsafe_fsafe.intros)
    qed
    then show ?case by auto
next
  case (fsafe_Geq t1 t2) then 
  show ?case
    using tsubst_preserves_safe ssafe unfolding ssafe_def by (auto intro: hpsafe_fsafe.intros)  
next
  case (fsafe_Prop args p) then
  show ?case 
    apply(cases "SPredicates \<sigma> p")
    using tsubst_preserves_safe tsubst_preserves_free ssafe unfolding ssafe_def 
    apply (auto intro: hpsafe_fsafe.intros) apply blast
    using tsubst_preserves_safe tsubst_preserves_free ssafe unfolding ssafe_def 
    apply (auto intro: hpsafe_fsafe.intros)
    by (simp add: nfsubst_preserves_safe tsubst_preserves_free) 
next
  case (fsafe_DiffFormula p)
  then show ?case sorry
next
  case (fsafe_InContext f C) then 
  show ?case
    using ssafe unfolding ssafe_def by (cases "SContexts \<sigma> C", auto simp add: case_unit_Unity ppsubst_pfsubst_preserves_safe)
qed (auto intro: hpsafe_fsafe.intros)
    
lemma fsubst_preserves_safe:
  assumes ssafe:"ssafe \<sigma>"
  assumes fsafe:"fsafe \<phi>"
  assumes FA:"Fadmit \<sigma> \<phi>"  
  shows "fsafe (Fsubst \<phi> \<sigma>)"
    using ssafe fsafe FA psubst_fsubst_preserves_safe by auto

lemma psubst_preserves_safe:
  assumes ssafe:"ssafe \<sigma>"
  assumes hpsafe:"hpsafe \<alpha>"
  assumes PA:"Padmit \<sigma> \<alpha>"  
  shows "hpsafe (Psubst \<alpha> \<sigma>)"
    using ssafe hpsafe PA psubst_fsubst_preserves_safe by auto
  
lemma nsubst_dterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
fixes \<nu>'::"'sz state"
assumes good_interp:"is_interp I"    
shows "NTadmit \<sigma> \<theta> \<Longrightarrow> dsafe \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dterm_sem I (NTsubst \<theta> \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> \<nu>"
proof (induction rule: NTadmit.induct)
  case (NTadmit_Diff \<sigma> \<theta>)
  then show ?case
    apply auto
    apply (unfold directional_derivative_def) 
    apply (rule sterm_determines_frechet)
    apply (auto)
    subgoal using good_interp by auto
    subgoal using NTadjoint_safe[OF good_interp, of \<sigma>] by auto
    subgoal using ntsubst_preserves_free[of \<theta> \<sigma>] by auto
    subgoal
      apply(rule ext)
      subgoal for x
        using nsubst_sterm'[of \<theta> \<sigma> I "(fst \<nu>)" "(snd \<nu>)"] apply auto
        proof -
          assume NT:"NTadmit \<sigma> \<theta>"
          assume NTU:"NTUadmit \<sigma> \<theta> UNIV"
          assume IH:"(dsafe \<theta> \<Longrightarrow> dterm_sem I (NTsubst \<theta> \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> \<nu>)"
          assume free:"dfree \<theta>"
          assume frees: "(\<And>i. dfree (\<sigma> i))"
          assume sem:"sterm_sem I (NTsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
          have VA:"\<And>\<nu> \<omega>. Vagree \<nu> (x,snd \<nu>) (-UNIV)" unfolding Vagree_def by auto
          show "sterm_sem I (NTsubst \<theta> \<sigma>) x = sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> x"
            using uadmit_sterm_ntadjoint[OF NTU VA frees, OF dfree_is_dsafe[OF free] good_interp, of "(x, snd \<nu>)"] nsubst_sterm[OF free frees, of I "(\<lambda>x. x)"] apply auto
            by (metis NTU VA dfree_is_dsafe free frees good_interp uadmit_sterm_ntadjoint)
        qed
        done
      done
next
  case (NTadmit_Fun \<sigma> args f)
  then show ?case apply auto apply(cases f) unfolding NTadjoint_def by auto
qed (auto)
  
lemma nsubst_ode:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
fixes \<nu>'::"'sz state"
assumes good_interp:"is_interp I"    
shows "osafe ODE \<Longrightarrow> NOUadmit \<sigma> ODE U \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> ODE_sem I (NOsubst ODE \<sigma>) (fst \<nu>)= ODE_sem (NTadjoint I \<sigma> \<nu>) ODE (fst \<nu>)"
proof (induction rule: osafe.induct)
  case (osafe_Var c)
  then show ?case unfolding NOUadmit_def NTadjoint_def by auto
next
  case (osafe_Sing \<theta> x)
  then show ?case apply auto
    apply(rule vec_extensionality)
    apply auto
    using nsubst_sterm' [of \<theta> \<sigma> I "(fst \<nu>)" "(snd \<nu>)"]
    by auto
next
  case (osafe_Prod ODE1 ODE2) then
  have NOU1:"NOUadmit \<sigma> ODE1 U" and NOU2:"NOUadmit \<sigma> ODE2 U" 
    unfolding NOUadmit_def by auto
  have "ODE_sem I (NOsubst ODE1 \<sigma>) (fst \<nu>) = ODE_sem (NTadjoint I \<sigma> \<nu>) ODE1 (fst \<nu>)"
    "ODE_sem I (NOsubst ODE2 \<sigma>) (fst \<nu>) = ODE_sem (NTadjoint I \<sigma> \<nu>) ODE2 (fst \<nu>)" using osafe_Prod.IH osafe_Prod.prems osafe_Prod.hyps
    using NOU1 NOU2 by auto
  then show ?case by auto
qed
    
lemma osubst_preserves_ODE_vars:
shows "ODE_vars (NOsubst ODE \<sigma>) = ODE_vars ODE"
proof (induction "ODE")
qed (auto)

lemma nsubst_mkv:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
fixes \<nu>'::"'sz state"
assumes good_interp:"is_interp I"  
assumes NOU:"NOUadmit \<sigma> ODE U"
assumes osafe:"osafe ODE "
assumes frees:"(\<And>i. dfree (\<sigma> i))"
shows "(mk_v I (NOsubst ODE \<sigma>) \<nu> (fst \<nu>)) 
  = (mk_v (NTadjoint I \<sigma> \<nu>) ODE \<nu> (fst \<nu>))"
    apply(rule agree_UNIV_eq)
    using mk_v_agree[of "NTadjoint I \<sigma> \<nu>" "ODE" \<nu> "(fst \<nu>)"]
    using mk_v_agree[of "I" "NOsubst ODE \<sigma>" \<nu> "(fst \<nu>)"] 
    unfolding Vagree_def osubst_preserves_ODE_vars
    using nsubst_ode[OF good_interp osafe NOU frees]
    apply auto
    subgoal for i
      apply(erule allE[where x=i])+
      apply(cases "Inl i \<in> ODE_vars ODE")
      by auto
    subgoal for i
      apply(erule allE[where x=i])+
      apply(cases "Inr i \<in> ODE_vars ODE")
      using osubst_preserves_ODE_vars[of ODE \<sigma>]
      by auto
    done
        
lemma nsubst_hp_fml:
fixes I::"('sf, 'sc, 'sz) interp"
assumes good_interp:"is_interp I"    
shows " (NPadmit \<sigma> \<alpha> \<longrightarrow> (hpsafe \<alpha> \<longrightarrow> (\<forall>i. dfree (\<sigma> i)) \<longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (NPsubst \<alpha> \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) \<alpha>)))) \<and>
  (NFadmit \<sigma> \<phi> \<longrightarrow> (fsafe \<phi> \<longrightarrow> (\<forall>i. dfree (\<sigma> i)) \<longrightarrow> (\<forall> \<nu>. (\<nu> \<in> fml_sem I (NFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) \<phi>))))"
proof (induction rule: NPadmit_NFadmit.induct)
  case (NPadmit_Pvar \<sigma> a)
  then show ?case unfolding NTadjoint_def by auto
next
  case (NPadmit_ODE \<sigma> ODE \<phi>)
  then show ?case 
    using nsubst_ode[OF good_interp, of ODE \<sigma> "ODE_vars ODE"] nsubst_mkv[OF good_interp, of \<sigma> ODE "ODE_vars ODE"] 
    sorry
next
  case (NPadmit_Assign \<sigma> \<theta> x)
  then show ?case using nsubst_dterm[OF good_interp, of \<sigma> \<theta>] by auto
next
  case (NPadmit_DiffAssign \<sigma> \<theta> x)
  then show ?case using nsubst_dterm[OF good_interp, of \<sigma> \<theta>] by auto
next
  case (NFadmit_Geq \<sigma> \<theta>1 \<theta>2)
  then show ?case 
    using nsubst_dterm[OF good_interp, of \<sigma> \<theta>1] 
    using nsubst_dterm[OF good_interp, of \<sigma> \<theta>2] by auto
next
  case (NFadmit_Prop \<sigma> args f)
  assume NTA:"\<And>i. NTadmit \<sigma> (args i)"
  have "\<And>\<nu>.  fsafe ($\<phi> f args) \<Longrightarrow>  (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<nu> \<in> fml_sem I (NFsubst ($\<phi> f args) \<sigma>)) = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) ($\<phi> f args))"
    proof -
      fix \<nu>
      assume safe:"fsafe ($\<phi> f args)"
      from safe have frees:"\<And>i. dfree (args i)" by (auto dest: fsafe.cases)
      from frees have safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
      assume subFree:"(\<And>i. dfree (\<sigma> i))"
      have vec_eq:"(\<chi> i. dterm_sem (NTadjoint I \<sigma> \<nu>) (args i) \<nu>) = (\<chi> i. dterm_sem I (NTsubst (args i) \<sigma>) \<nu>)"
        apply(rule vec_extensionality)
        using nsubst_dterm[OF good_interp NTA safes subFree] by auto
      then show "?thesis \<nu>" unfolding NTadjoint_def by auto
    qed
  then show ?case by auto 
next
  case (NFadmit_DiffFormula \<sigma> \<phi>)
  then show ?case sorry
next
  case (NPadmit_Sequence \<sigma> a b) then 
  have PUA:"NPUadmit \<sigma> b (BVP (NPsubst a \<sigma>))"
   and PA:"NPadmit \<sigma> a"
   and IH1:"hpsafe a \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (NPsubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) a))"
   and IH2:"hpsafe b \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (NPsubst b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) b))"
    by auto
  have "hpsafe (a ;; b) \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (NPsubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) (a ;; b)))"
    proof -
      assume hpsafe:"hpsafe (a ;; b)"
      assume ssafe:"(\<And>i. dfree (\<sigma> i))"
      from hpsafe have safe1:"hpsafe a" and safe2:"hpsafe b" by (auto dest: hpsafe.cases)
      fix \<nu> \<omega>
      have agree:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (NPsubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(NPsubst a \<sigma>))"
        subgoal for \<mu>
          using bound_effect[OF good_interp, of "(NPsubst a \<sigma>)" \<nu>, OF npsubst_preserves_safe[OF ssafe safe1 PA]] by auto
        done
      have sem_eq:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (NPsubst a \<sigma>) \<Longrightarrow> 
          ((\<mu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) b) =
          ((\<mu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<mu>) b)"
        subgoal for \<mu>
          proof -
            assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (NPsubst a \<sigma>)"
            show "((\<mu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) b) = ((\<mu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<mu>) b)"
              using uadmit_prog_ntadjoint[OF PUA agree[OF assm] ssafe safe2 good_interp] 
              by auto
          qed
        done      
      have "((\<nu>, \<omega>) \<in> prog_sem I (NPsubst (a ;; b) \<sigma>)) = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (NPsubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem I (NPsubst b \<sigma>))"
        by auto
      moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (NPsubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<mu>) b)"
        using IH2[OF safe2 ssafe] by auto
      moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (NPsubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) b)"
        using sem_eq by auto
      moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) a \<and> (\<mu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) b)"
        using IH1[OF safe1 ssafe] by auto
      ultimately
      show "((\<nu>, \<omega>) \<in> prog_sem I (NPsubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) (a ;; b))"
        by auto
    qed
  then show ?case by auto
next
  case (NPadmit_Loop \<sigma> a) then 
    have PA:"NPadmit \<sigma> a"
    and PUA:"NPUadmit \<sigma> a (BVP (NPsubst a \<sigma>))"
    and IH:"hpsafe a \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (NPsubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) a))"
      by auto
    have "hpsafe (a**) \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (NPsubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) (a**)))"
      proof -
        assume "hpsafe (a**)"
        then have hpsafe:"hpsafe a" by (auto dest: hpsafe.cases)
        assume ssafe:"(\<And>i. dfree (\<sigma> i))"
        have agree:"\<And>\<nu> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (NPsubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(NPsubst a \<sigma>))"
        subgoal for \<nu> \<mu>
          using bound_effect[OF good_interp, of "(NPsubst a \<sigma>)" \<nu>, OF npsubst_preserves_safe[OF ssafe hpsafe PA]] by auto
        done
      have sem_eq:"\<And>\<nu> \<mu> \<omega>. (\<nu>, \<mu>) \<in> prog_sem I (NPsubst a \<sigma>) \<Longrightarrow> 
          ((\<mu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) a) =
          ((\<mu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<mu>) a)"
        subgoal for \<nu> \<mu> \<omega> 
          proof -
            assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (NPsubst a \<sigma>)"
            show "((\<mu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) a) = ((\<mu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<mu>) a)"
              using uadmit_prog_ntadjoint[OF PUA agree[OF assm] ssafe hpsafe  good_interp] by auto
          qed
        done 
      fix \<nu> \<omega>
      have UN_rule:"\<And> a S S'. (\<And>n b. (a,b) \<in> S n \<longleftrightarrow> (a,b) \<in> S' n) \<Longrightarrow> (\<And>b. (a,b) \<in> (\<Union>n. S n) \<longleftrightarrow> (a,b) \<in> (\<Union>n. S' n))"
        by auto
      have eqL:"((\<nu>, \<omega>) \<in> prog_sem I (NPsubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (NPsubst a \<sigma>)) ^^ n))"
        using rtrancl_is_UN_relpow by auto
      moreover have eachEq:"\<And>n. ((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (NPsubst a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (NTadjoint I \<sigma> \<nu>) a)^^ n)))"
        proof -
          fix n
          show "((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (NPsubst a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (NTadjoint I \<sigma> \<nu>) a)^^ n)))"
      proof (induct n)
        case 0
        then show ?case by auto
      next
        case (Suc n) then
        have IH2:"\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (NPsubst a \<sigma>) ^^ n) = ((\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) a ^^ n)"
          by auto
        have relpow:"\<And>R n. R ^^ Suc n = R O R ^^ n"
          using relpow.simps(2) relpow_commute by metis
        show ?case 
          apply (simp only: relpow[of n "prog_sem I (NPsubst a \<sigma>)"] relpow[of n "prog_sem (NTadjoint I \<sigma> \<nu>) a"])
          apply(unfold relcomp_unfold)
          apply auto
          subgoal for ab b
             apply(rule exI[where x=ab])
             apply(rule exI[where x=b])
             using IH2 IH[OF hpsafe ssafe] sem_eq[of \<nu> "(ab,b)" \<omega>] apply auto
             using uadmit_prog_ntadjoint[OF PUA agree ssafe hpsafe good_interp] IH[OF hpsafe ssafe]
             apply (metis (no_types, lifting)) 
             using uadmit_prog_ntadjoint[OF PUA agree ssafe hpsafe good_interp] IH[OF hpsafe ssafe]
             apply (metis (no_types, lifting)) 
          done
          subgoal for ab b
             apply(rule exI[where x=ab])
             apply(rule exI[where x=b])
             using IH2 IH[OF hpsafe ssafe] sem_eq[of \<nu> "(ab,b)" \<omega>] apply auto
             using uadmit_prog_ntadjoint[OF PUA agree ssafe hpsafe good_interp] IH[OF hpsafe ssafe]
             apply (metis (no_types, lifting))
             using uadmit_prog_ntadjoint[OF PUA agree ssafe hpsafe good_interp] IH[OF hpsafe ssafe]
             apply (metis (no_types, lifting))
          done
        done
      qed
      qed
     moreover have "((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (NPsubst a \<sigma>)) ^^ n)) = ((\<nu>, \<omega>) \<in> (\<Union> n.(prog_sem (NTadjoint I \<sigma> \<nu>) a)^^ n))"
       apply(rule UN_rule)
       using eachEq by auto
     moreover have eqR:"((\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) (a**)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem (NTadjoint I \<sigma> \<nu>) a) ^^ n))"
        using rtrancl_is_UN_relpow by auto
     ultimately show "((\<nu>, \<omega>) \<in> prog_sem I (NPsubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) (a**))"
       by auto
      qed
  then show ?case by auto
next
  case (NFadmit_Exists \<sigma> \<phi> x)
  then have IH:"fsafe \<phi> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (NFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) \<phi>))"
    and FUA:"NFUadmit \<sigma> \<phi> {Inl x}"
    by blast+
  have fsafe:"fsafe (Exists x \<phi>) \<Longrightarrow> fsafe \<phi>"
    by (auto dest: fsafe.cases)
  have eq:"fsafe (Exists x \<phi>) \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (NFsubst (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>)  (Exists x \<phi>)))"
    proof -
      assume fsafe:"fsafe (Exists x \<phi>)"
      from fsafe have fsafe':"fsafe \<phi>" by (auto dest: fsafe.cases)
      assume ssafe:"(\<And>i. dfree (\<sigma> i))"
      fix \<nu>
      have agree:"\<And>r. Vagree \<nu> (repv \<nu> x r) (- {Inl x})"
        unfolding Vagree_def by auto
      have sem_eq:"\<And>r. ((repv \<nu> x r) \<in> fml_sem (NTadjoint I \<sigma> (repv \<nu> x r)) \<phi>) =
                        ((repv \<nu> x r) \<in> fml_sem (NTadjoint I \<sigma> \<nu>) \<phi>)"
        using uadmit_fml_ntadjoint[OF FUA agree ssafe fsafe' good_interp] by auto
      have "(\<nu> \<in> fml_sem I (NFsubst  (Exists x \<phi>) \<sigma>)) = (\<exists>r. (repv \<nu> x r) \<in> fml_sem I (NFsubst \<phi> \<sigma>))"
        by auto
      moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (NTadjoint I \<sigma> (repv \<nu> x r)) \<phi>)"
        using IH[OF fsafe' ssafe] by auto
      moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (NTadjoint I \<sigma> \<nu>) \<phi>)"
        using sem_eq by auto
      moreover have "... = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) (Exists x \<phi>))"
        by auto
      ultimately show "(\<nu> \<in> fml_sem I (NFsubst  (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) (Exists x \<phi>))"
        by auto
      qed
  then show ?case by auto
next
  case (NFadmit_Diamond \<sigma> \<phi> a) then 
    have PA:"NPadmit \<sigma> a" 
    and FUA:"NFUadmit \<sigma> \<phi> (BVP (NPsubst a \<sigma>))"
    and IH1:"fsafe \<phi> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (NFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) \<phi>))"
    and IH2:"hpsafe a \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (NPsubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) a))"
      by auto
    have "fsafe (\<langle> a \<rangle> \<phi>) \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (NFsubst (\<langle> a \<rangle> \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) (\<langle> a \<rangle> \<phi>)))"
    proof -
      assume fsafe:"fsafe (\<langle> a \<rangle> \<phi>)"
      assume ssafe:"(\<And>i. dfree (\<sigma> i))"
      from fsafe have fsafe':"fsafe \<phi>" and hpsafe:"hpsafe a" by (auto dest: fsafe.cases)
      fix \<nu>
      have agree:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (NPsubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<omega> (-BVP(NPsubst a \<sigma>))"
        using bound_effect[OF good_interp, of "(NPsubst a \<sigma>)" \<nu>, OF npsubst_preserves_safe[OF ssafe hpsafe PA]] by auto
      have sem_eq:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (NPsubst a \<sigma>) \<Longrightarrow> 
          (\<omega> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) \<phi>) =
          (\<omega> \<in> fml_sem (NTadjoint I \<sigma> \<omega>) \<phi>)"
        using uadmit_fml_ntadjoint[OF FUA agree ssafe fsafe' good_interp] by auto
      have "(\<nu> \<in> fml_sem I (NFsubst (\<langle> a \<rangle> \<phi>) \<sigma>)) = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I (NPsubst a \<sigma>) \<and> \<omega> \<in> fml_sem I (NFsubst \<phi> \<sigma>))"
        by auto
      moreover have "... = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) a \<and> \<omega> \<in> fml_sem (NTadjoint I \<sigma> \<omega>) \<phi>)"
        using IH1[OF fsafe' ssafe] IH2[OF hpsafe ssafe, of \<nu>] by auto
      moreover have "... = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem (NTadjoint I \<sigma> \<nu>) a \<and> \<omega> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) \<phi>)"
        using sem_eq IH2 hpsafe ssafe by blast
      moreover have "... = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) (\<langle> a \<rangle> \<phi>))"
        by auto
      ultimately show "?thesis \<nu>" by auto
    qed
  then show ?case by auto
next
  case (NFadmit_Context \<sigma> \<phi> C) then
    have FA:"NFadmit \<sigma> \<phi>"
    and FUA:"NFUadmit \<sigma> \<phi> UNIV"
    and IH:"fsafe \<phi> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (NFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) \<phi>))"
      by auto
    have "fsafe (InContext C \<phi>) \<Longrightarrow>
             (\<And>i. dfree (\<sigma> i))\<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (NFsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) (InContext C \<phi>)))"
      proof -
        assume safe:"fsafe (InContext C \<phi>)"
        then have fsafe:"fsafe \<phi>" by (auto dest: fsafe.cases)
        assume ssafe:"\<And>i. dfree (\<sigma> i)"
        fix \<nu>
        have Ieq:" Contexts (NTadjoint I \<sigma> \<nu>) C = Contexts I C"
          unfolding NTadjoint_def by auto
        have IH':"\<And>\<nu>. (\<nu> \<in> fml_sem I (NFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) \<phi>)"
          using IH[OF fsafe ssafe] by auto
        have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
        have adj_eq:"\<And>\<omega>. fml_sem (NTadjoint I \<sigma> \<nu>) \<phi> = fml_sem (NTadjoint I \<sigma> \<omega>) \<phi>"
          using uadmit_fml_ntadjoint[OF FUA agree ssafe fsafe good_interp] by auto
        then have sem:"fml_sem I (NFsubst \<phi> \<sigma>) =  fml_sem (NTadjoint I \<sigma> \<nu>) \<phi>"
          using IH' agree adj_eq by auto
        show "?thesis \<nu>"  using Ieq sem by auto
      qed
  then show ?case by auto
qed (auto)

lemma nsubst_fml:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"
assumes NFA:"NFadmit \<sigma> \<phi>"
assumes fsafe:"fsafe \<phi>"
assumes frees:"(\<forall>i. dfree (\<sigma> i))"
shows "(\<nu> \<in> fml_sem I (NFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (NTadjoint I \<sigma> \<nu>) \<phi>)"
  using good_interp NFA fsafe frees 
  by (auto simp add: nsubst_hp_fml)

lemma nsubst_hp:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"    
assumes NPA:"NPadmit \<sigma> \<alpha>"
assumes hpsafe:"hpsafe \<alpha>"
assumes frees:"\<And>i. dfree (\<sigma> i)"
shows "((\<nu>, \<omega>) \<in> prog_sem I (NPsubst \<alpha> \<sigma>)) = ((\<nu>, \<omega>) \<in>  prog_sem (NTadjoint I \<sigma> \<nu>) \<alpha>)"
 using good_interp NPA hpsafe frees nsubst_hp_fml by blast

lemma psubst_sterm:
fixes I::"('sf, 'sc, 'sz) interp"
assumes good_interp:"is_interp I"    
shows "(sterm_sem I \<theta> = sterm_sem (PFadjoint I \<sigma>) \<theta>)"
proof (induction \<theta>)
qed (auto simp add: PFadjoint_def)

lemma psubst_dterm:
fixes I::"('sf, 'sc, 'sz) interp"
assumes good_interp:"is_interp I"    
shows "(dsafe \<theta> \<Longrightarrow> dterm_sem I \<theta> = dterm_sem (PFadjoint I \<sigma>) \<theta>)"
proof (induction \<theta>)
  case (Differential \<theta>)
  assume safe:"dsafe (Differential \<theta>)"
  from safe have free:"dfree \<theta>" by auto
  assume sem:"dsafe \<theta> \<Longrightarrow> dterm_sem I \<theta> = dterm_sem (PFadjoint I \<sigma>) \<theta>"
  have "\<And>\<nu>. frechet I \<theta> (fst \<nu>) (snd \<nu>) = frechet (PFadjoint I \<sigma>) \<theta> (fst \<nu>) (snd \<nu>)"
    apply(rule sterm_determines_frechet)
    using good_interp free apply auto
    subgoal unfolding is_interp_def PFadjoint_def by auto
    using psubst_sterm[of I \<theta>] by auto
  then show "?case"
    by (auto simp add: directional_derivative_def)
 qed (auto simp add: PFadjoint_def)
    
lemma psubst_fml:
fixes I::"('sf, 'sc, 'sz) interp"
assumes good_interp:"is_interp I"    
shows "(PPadmit \<sigma> \<alpha>  \<longrightarrow> hpsafe \<alpha> \<longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<longrightarrow> (\<forall> \<nu> \<omega>. (\<nu>,\<omega>) \<in> prog_sem I (PPsubst \<alpha> \<sigma>) = ((\<nu>,\<omega>) \<in> prog_sem (PFadjoint I \<sigma>) \<alpha>))) \<and> 
  (PFadmit \<sigma> \<phi> \<longrightarrow> fsafe \<phi> \<longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<longrightarrow> (\<forall> \<nu>. \<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>)))"
proof (induction rule: PPadmit_PFadmit.induct)
  case (PPadmit_ODE \<sigma> \<phi> ODE)
  then show ?case apply auto sorry
next
  case (PPadmit_Assign \<sigma> x \<theta>)
  have "hpsafe (x := \<theta>) \<Longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (x := \<theta>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (x := \<theta>)))"
    proof -
      assume safe:"hpsafe (x := \<theta>)"
      then have dsafe:"dsafe \<theta>" by auto
      assume safes:"(\<forall>i. fsafe (\<sigma> i))"
      show "?thesis"
        apply(auto)
         apply(rule vec_extensionality)
         subgoal using psubst_dterm[OF good_interp dsafe, of \<sigma>] by auto
         apply(rule vec_extensionality)
         using psubst_dterm[OF good_interp dsafe, of \<sigma>] by auto
    qed
  then show "?case" by auto 
next
  case (PPadmit_DiffAssign \<sigma> x \<theta>)
  have "hpsafe (DiffAssign x \<theta>) \<Longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (DiffAssign x \<theta>) \<sigma>)) = (((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (DiffAssign x \<theta>))))"
    proof -
      assume safe:"hpsafe (DiffAssign x \<theta>)"
      then have dsafe:"dsafe \<theta>" by auto
      assume safes:"(\<forall>i. fsafe (\<sigma> i))"
      show "?thesis"
        apply(auto)
         apply(rule vec_extensionality)
         subgoal using psubst_dterm[OF good_interp dsafe, of \<sigma>] by auto
         apply(rule vec_extensionality)
         using psubst_dterm[OF good_interp dsafe, of \<sigma>] by auto
    qed
  then show ?case by auto
next
  case (PFadmit_Geq \<sigma> \<theta>1 \<theta>2) then 
  have "fsafe (Geq \<theta>1 \<theta>2) \<Longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu>. (\<nu> \<in> fml_sem I (PFsubst (Geq \<theta>1 \<theta>2) \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) (Geq \<theta>1 \<theta>2)))"
    proof -
      assume safe:"fsafe (Geq \<theta>1 \<theta>2)"
      then have safe1:"dsafe \<theta>1" 
        and safe2:"dsafe \<theta>2" by auto
      assume safes:"(\<forall>i. fsafe (\<sigma> i))"
      show "?thesis"
        using psubst_dterm[OF good_interp safe1, of \<sigma>] psubst_dterm[OF good_interp safe2, of \<sigma>] by  auto
    qed
  then show ?case by auto
next
  case (PFadmit_Prop \<sigma> p args) then
    have "fsafe (Prop p args) \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>.(\<nu> \<in> fml_sem I (PFsubst ($\<phi> p args) \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) ($\<phi> p args)))"
    proof -
      assume safe:"fsafe (Prop p args)" and ssafe:" (\<And>i. fsafe (\<sigma> i))"
      fix \<nu>
      from safe have frees:"\<And>i. dfree (args i)" by auto
      hence safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
      have Ieq:"Predicates I p = Predicates (PFadjoint I \<sigma>) p"
        unfolding PFadjoint_def by auto
      have vec:"(\<chi> i. dterm_sem I (args i) \<nu>) = (\<chi> i. dterm_sem (PFadjoint I \<sigma>) (args i) \<nu>)"
        apply(auto simp add: vec_eq_iff)
        subgoal for i using safes[of i] 
          by (metis good_interp psubst_dterm)
        done
      show "?thesis \<nu>" using  Ieq vec by auto
    qed
    then show "?case" by auto
next
  case (PFadmit_DiffFormula \<sigma> \<phi>)
  then show ?case sorry
next
  case (PPadmit_Sequence \<sigma> a b) then 
  have PUA:"PPUadmit \<sigma> b (BVP (PPsubst a \<sigma>))"
   and PA:"PPadmit \<sigma> a"
   and IH1:"hpsafe a \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) a))"
   and IH2:"hpsafe b \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b))"
     by auto
  have "hpsafe (a ;; b) \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a ;; b)))"
    proof -
      assume hpsafe:"hpsafe (a ;; b)"
      assume ssafe:"(\<And>i. fsafe (\<sigma> i))"
      from hpsafe have safe1:"hpsafe a" and safe2:"hpsafe b" by (auto dest: hpsafe.cases)
      fix \<nu> \<omega>
      have agree:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(PPsubst a \<sigma>))"
        subgoal for \<mu>
          using bound_effect[OF good_interp, of "(PPsubst a \<sigma>)" \<nu>, OF ppsubst_preserves_safe[OF ssafe safe1 PA]] by auto
        done
      have sem_eq:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<Longrightarrow> 
          ((\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b) =
          ((\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b)"
        subgoal for \<mu>
          proof -
            assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>)"
            show "((\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b) = ((\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b)"
              using PUA agree[OF assm] safe2 ssafe good_interp by auto
          qed
        done      
      have "((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a ;; b) \<sigma>)) = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem I (PPsubst b \<sigma>))"
        by auto
      moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b)"
        using IH2[OF safe2 ssafe] by blast 
      moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem (PFadjoint I \<sigma>) a \<and> (\<mu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b)"
        using IH1[OF safe1 ssafe] sem_eq by blast
      ultimately
      show "((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a ;; b))"
        by auto
    qed
  then show ?case by auto
next
  case (PPadmit_Loop \<sigma> a) then 
    have PA:"PPadmit \<sigma> a"
    and PUA:"PPUadmit \<sigma> a (BVP (PPsubst a \<sigma>))"
    and IH:"hpsafe a \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) a))"
      by auto
    have "hpsafe (a**) \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a**)))"
      proof -
        assume "hpsafe (a**)"
        then have hpsafe:"hpsafe a" by (auto dest: hpsafe.cases)
        assume ssafe:"\<And>i. fsafe (\<sigma> i)"
        have agree:"\<And>\<nu> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(PPsubst a \<sigma>))"
        subgoal for \<nu> \<mu>
          using bound_effect[OF good_interp, of "(PPsubst a \<sigma>)" \<nu>, OF ppsubst_preserves_safe[OF ssafe hpsafe PA]] by auto
        done
      fix \<nu> \<omega>
      have UN_rule:"\<And> a S S'. (\<And>n b. (a,b) \<in> S n \<longleftrightarrow> (a,b) \<in> S' n) \<Longrightarrow> (\<And>b. (a,b) \<in> (\<Union>n. S n) \<longleftrightarrow> (a,b) \<in> (\<Union>n. S' n))"
        by auto
      have eqL:"((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (PPsubst a \<sigma>)) ^^ n))"
        using rtrancl_is_UN_relpow by auto
      moreover have eachEq:"\<And>n. ((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (PPsubst a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (PFadjoint I \<sigma>) a)^^ n)))"
        proof -
          fix n
          show "((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (PPsubst a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (PFadjoint I \<sigma>) a)^^ n)))"
      proof (induct n)
        case 0
        then show ?case by auto
      next
        case (Suc n) then
        have IH2:"\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst a \<sigma>) ^^ n) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) a ^^ n)"
          by auto
        have relpow:"\<And>R n. R ^^ Suc n = R O R ^^ n"
          using relpow.simps(2) relpow_commute by metis
        show ?case 
          apply (simp only: relpow[of n "prog_sem I (PPsubst a \<sigma>)"] relpow[of n "prog_sem (PFadjoint I \<sigma>) a"])
          apply(unfold relcomp_unfold)
          apply auto
          subgoal for ab b
             apply(rule exI[where x=ab])
             apply(rule exI[where x=b])
             using IH2 IH[OF hpsafe ssafe]  by auto
          subgoal for ab b
             apply(rule exI[where x=ab])
             apply(rule exI[where x=b])
             using IH2 IH[OF hpsafe ssafe] by auto
        done
      qed
      qed
     moreover have "((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (PPsubst a \<sigma>)) ^^ n)) = ((\<nu>, \<omega>) \<in> (\<Union> n.(prog_sem (PFadjoint I \<sigma>) a)^^ n))"
       apply(rule UN_rule)
       using eachEq by auto
     moreover have eqR:"((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a**)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem (PFadjoint I \<sigma>) a) ^^ n))"
        using rtrancl_is_UN_relpow by auto
     ultimately show "((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a**))"
       by auto
      qed
  then show ?case by auto
next
next
case (PFadmit_Context \<sigma> \<phi> C) then
    have FA:"PFadmit \<sigma> \<phi>"
    and FUA:"PFUadmit \<sigma> \<phi> UNIV"
    and IH:"fsafe \<phi> \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>))"
      by auto
    have "fsafe (InContext C \<phi>) \<Longrightarrow>
             (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (PFsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) (InContext C \<phi>)))"
      proof -
        assume safe:"fsafe (InContext C \<phi>)"
        then have fsafe:"fsafe \<phi>" by (auto dest: fsafe.cases)
        assume ssafe:"(\<And>i. fsafe (\<sigma> i))"
        fix \<nu> :: "(real, 'sz) vec \<times> (real, 'sz) vec"
        have IH':"\<And>\<nu>. (\<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>)"
          using IH[OF fsafe ssafe] by auto
        have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
        then have sem:"fml_sem I (PFsubst \<phi> \<sigma>) =  fml_sem (PFadjoint I \<sigma>) \<phi>"
          using IH' agree  by auto
        show "?thesis \<nu>"  using sem 
          apply auto
          apply(cases C)
          unfolding PFadjoint_def apply auto
          apply(cases C)
          by auto
      qed
  then show ?case by auto

qed (auto simp add: PFadjoint_def)

lemma subst_ode:
fixes I:: "('sf, 'sc, 'sz) interp" and \<nu> :: "'sz state"
assumes good_interp:"is_interp I"
shows "osafe ODE \<Longrightarrow> 
       ssafe \<sigma> \<Longrightarrow> 
       Oadmit \<sigma> ODE (ODE_vars ODE) \<Longrightarrow>
       ODE_sem I (Osubst ODE \<sigma>) (fst \<nu>) = ODE_sem (adjoint I \<sigma> \<nu>) ODE (fst \<nu>)"
sorry

lemma subst_fml_hp:
fixes I::"('sf, 'sc, 'sz) interp"
assumes good_interp:"is_interp I"
shows 
"(Padmit \<sigma> \<alpha> \<longrightarrow>
  (hpsafe \<alpha> \<longrightarrow>
   ssafe \<sigma> \<longrightarrow>
  (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst \<alpha> \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) \<alpha>))))
  \<and>
  (Fadmit \<sigma> \<phi> \<longrightarrow>
  (fsafe \<phi> \<longrightarrow>
  ssafe \<sigma> \<longrightarrow>
  (\<forall> \<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))))"
proof (induction rule: Padmit_Fadmit.induct)
  case (Padmit_Pvar \<sigma> a) then
  have "hpsafe ($\<alpha> a) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst ($\<alpha> a) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) ($\<alpha> a)))"
    apply (cases "SPrograms \<sigma> a")
    unfolding adjoint_def by auto
  then show ?case by auto
next
  case (Padmit_Sequence \<sigma> a b) then 
  have PUA:"PUadmit \<sigma> b (BVP (Psubst a \<sigma>))"
   and PA:"Padmit \<sigma> a"
   and IH1:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a))"
   and IH2:"hpsafe b \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) b))"
    by auto
  have "hpsafe (a ;; b) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (a ;; b)))"
    proof -
      assume hpsafe:"hpsafe (a ;; b)"
      assume ssafe:"ssafe \<sigma>"
      from hpsafe have safe1:"hpsafe a" and safe2:"hpsafe b" by (auto dest: hpsafe.cases)
      fix \<nu> \<omega>
      have agree:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(Psubst a \<sigma>))"
        subgoal for \<mu>
          using bound_effect[OF good_interp, of "(Psubst a \<sigma>)" \<nu>, OF psubst_preserves_safe[OF ssafe safe1 PA]] by auto
        done
      have sem_eq:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> 
          ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) b) =
          ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<mu>) b)"
        subgoal for \<mu>
          proof -
            assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>)"
            show "((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) b) = ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<mu>) b)"
              using uadmit_prog_adjoint[OF PUA agree[OF assm] safe2 ssafe good_interp] by auto
          qed
        done      
      have "((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a ;; b) \<sigma>)) = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem I (Psubst b \<sigma>))"
        by auto
      moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<mu>) b)"
        using IH2[OF safe2 ssafe] by auto
      moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) b)"
        using sem_eq by auto
      moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a \<and> (\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) b)"
        using IH1[OF safe1 ssafe] by auto
      ultimately
      show "((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (a ;; b))"
        by auto
    qed
  then show ?case by auto
next
  case (Padmit_Loop \<sigma> a) then 
    have PA:"Padmit \<sigma> a"
    and PUA:"PUadmit \<sigma> a (BVP (Psubst a \<sigma>))"
    and IH:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a))"
      by auto
    have "hpsafe (a**) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (a**)))"
      proof -
        assume "hpsafe (a**)"
        then have hpsafe:"hpsafe a" by (auto dest: hpsafe.cases)
        assume ssafe:"ssafe \<sigma>"
        have agree:"\<And>\<nu> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(Psubst a \<sigma>))"
        subgoal for \<nu> \<mu>
          using bound_effect[OF good_interp, of "(Psubst a \<sigma>)" \<nu>, OF psubst_preserves_safe[OF ssafe hpsafe PA]] by auto
        done
      have sem_eq:"\<And>\<nu> \<mu> \<omega>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> 
          ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a) =
          ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<mu>) a)"
        subgoal for \<nu> \<mu> \<omega> 
          proof -
            assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>)"
            show "((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a) = ((\<mu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<mu>) a)"
              using uadmit_prog_adjoint[OF PUA agree[OF assm] hpsafe ssafe good_interp] by auto
          qed
        done 
      fix \<nu> \<omega>
      have UN_rule:"\<And> a S S'. (\<And>n b. (a,b) \<in> S n \<longleftrightarrow> (a,b) \<in> S' n) \<Longrightarrow> (\<And>b. (a,b) \<in> (\<Union>n. S n) \<longleftrightarrow> (a,b) \<in> (\<Union>n. S' n))"
        by auto
      have eqL:"((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (Psubst a \<sigma>)) ^^ n))"
        using rtrancl_is_UN_relpow by auto
      moreover have eachEq:"\<And>n. ((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (Psubst a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (adjoint I \<sigma> \<nu>) a)^^ n)))"
        proof -
          fix n
          show "((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (Psubst a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (adjoint I \<sigma> \<nu>) a)^^ n)))"
      proof (induct n)
        case 0
        then show ?case by auto
      next
        case (Suc n) then
        have IH2:"\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>) ^^ n) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a ^^ n)"
          by auto
        have relpow:"\<And>R n. R ^^ Suc n = R O R ^^ n"
          using relpow.simps(2) relpow_commute by metis
        show ?case 
          apply (simp only: relpow[of n "prog_sem I (Psubst a \<sigma>)"] relpow[of n "prog_sem (adjoint I \<sigma> \<nu>) a"])
          apply(unfold relcomp_unfold)
          apply auto
          subgoal for ab b
             apply(rule exI[where x=ab])
             apply(rule exI[where x=b])
             using IH2 IH[OF hpsafe ssafe] sem_eq[of \<nu> "(ab,b)" \<omega>] apply auto
             using uadmit_prog_adjoint[OF PUA agree hpsafe ssafe good_interp] IH[OF hpsafe ssafe]
             apply (metis (no_types, lifting)) 
             using uadmit_prog_adjoint[OF PUA agree hpsafe ssafe good_interp] IH[OF hpsafe ssafe]
             apply (metis (no_types, lifting)) 
          done
          subgoal for ab b
             apply(rule exI[where x=ab])
             apply(rule exI[where x=b])
             using IH2 IH[OF hpsafe ssafe] sem_eq[of \<nu> "(ab,b)" \<omega>] apply auto
             using uadmit_prog_adjoint[OF PUA agree hpsafe ssafe good_interp] IH[OF hpsafe ssafe]
             apply (metis (no_types, lifting))
             using uadmit_prog_adjoint[OF PUA agree hpsafe ssafe good_interp] IH[OF hpsafe ssafe]
             apply (metis (no_types, lifting))
          done
        done
      qed
      qed
     moreover have "((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (Psubst a \<sigma>)) ^^ n)) = ((\<nu>, \<omega>) \<in> (\<Union> n.(prog_sem (adjoint I \<sigma> \<nu>) a)^^ n))"
       apply(rule UN_rule)
       using eachEq by auto
     moreover have eqR:"((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (a**)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem (adjoint I \<sigma> \<nu>) a) ^^ n))"
        using rtrancl_is_UN_relpow by auto
     ultimately show "((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (a**))"
       by auto
      qed
  then show ?case by auto
next
  case (Padmit_ODE \<sigma> ODE \<phi>) then
    have OA:"Oadmit \<sigma> ODE (ODE_vars ODE)"
    and FA:"Fadmit \<sigma> \<phi>"
    and FUA:"FUadmit \<sigma> \<phi> (ODE_vars ODE)"
    and IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
      by auto
    have "hpsafe (EvolveODE ODE \<phi>) \<Longrightarrow>
       ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (EvolveODE ODE \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (EvolveODE ODE \<phi>)))"
    proof -
      assume hpsafe:"hpsafe (EvolveODE ODE \<phi>)"
      assume ssafe:"ssafe \<sigma>"
      fix \<nu> \<omega>
      from hpsafe have osafe:"osafe ODE" and fsafe:"fsafe \<phi>" by (auto dest: hpsafe.cases)
      have IH':"(\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
        using IH[OF fsafe ssafe] by auto
      have IH2:"\<And>\<nu>. ODE_sem I (Osubst ODE \<sigma>) (fst \<nu>) = ODE_sem (adjoint I \<sigma> \<nu>) ODE (fst \<nu>)"
        using subst_ode[OF good_interp osafe ssafe OA] by auto
      have IH2':"\<And>\<nu>1 \<nu>2. ODE_sem I (Osubst ODE \<sigma>) \<nu>1 = ODE_sem (adjoint I \<sigma> (\<nu>1,\<nu>2)) ODE \<nu>1"
        using subst_ode[OF good_interp osafe ssafe OA] by auto
      have IH3:"\<And>sol b t. t \<ge> 0 \<Longrightarrow> mk_v I (Osubst ODE \<sigma>) (sol 0, b) (sol t) = mk_v (adjoint I \<sigma> \<nu>) ODE (sol 0, b) (sol t)"
        sorry
      have IH3':"\<And>sol b t. t \<ge> 0 \<Longrightarrow> mk_v (local.adjoint I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol t) = mk_v I (Osubst ODE \<sigma>) (sol 0, b) (sol t)"
        sorry
      have agree:"\<And>sol t b. Vagree \<nu> (sol t, b) (- ODE_vars ODE)"
        sorry
      
      have eq1:"\<And>sol b t. fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> (sol t, b)) \<phi>"
        subgoal for sol b t
          by (rule uadmit_fml_adjoint[OF FUA agree fsafe ssafe good_interp])
        done
      have eq2:"\<And> sol b. (\<lambda>a. ODE_sem (local.adjoint I \<sigma> (sol 0, b)) ODE) = (\<lambda>a. ODE_sem I (Osubst ODE \<sigma>))"
        apply (rule ext)
        sorry
      have eq3:"\<And>sol b. mk_v (local.adjoint I \<sigma> (sol 0, b)) ODE  (sol 0, b) =  mk_v I (Osubst ODE \<sigma>) (sol 0, b)"
        sorry
      have eq4:"\<And>sol b t x. fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, b) x)) \<phi> "
        sorry
      show "?thesis \<nu> \<omega>" 
        apply simp
        apply auto
        subgoal for  b sol t
          apply(rule exI[where x="sol"])
          apply(rule conjI)
          subgoal by auto
          subgoal
            apply(rule exI[where x=t])
            apply(rule conjI)
            subgoal using IH3 by auto
            apply(rule conjI)
            subgoal by auto
            subgoal
              using IH2'[of "sol 0" "b"] eq3[of sol b] eq2[of sol b]  eq1[of sol t b] eq4 IH' IH2' IH3 eq2
              apply(auto)
              by (smt Collect_cong eq4 solves_ode_congI)
            done
          done
        subgoal for  b sol t
          apply(rule exI[where x="sol"])
          apply(rule conjI)
          subgoal by auto
          subgoal
            apply(rule exI[where x=t])
            apply(rule conjI)
            subgoal using IH3' by auto
            apply(rule conjI)
            subgoal by auto
            subgoal
              using IH2'[of "sol 0" "b"] eq3[of sol b] eq2[of sol b] eq1[of sol t b] eq4 IH' IH2' IH3 eq2
              apply(auto)
              by (smt Collect_cong eq4 solves_ode_congI)
            done
          done
        done 
    qed
  then show ?case by auto 
next
  case (Padmit_Choice \<sigma> a b) then 
  have IH1:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) a))"
  and IH2:"hpsafe b \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) b))"
    by blast+
  have hpsafe1:"hpsafe (a \<union>\<union> b) \<Longrightarrow> hpsafe a" 
   and hpsafe2:"hpsafe (a \<union>\<union> b) \<Longrightarrow> hpsafe b" 
      by (auto dest: hpsafe.cases)
  show ?case using IH1[OF hpsafe1] IH2[OF hpsafe2] by auto
next
  case (Padmit_Assign \<sigma> \<theta> x) then
  have TA:"Tadmit \<sigma> \<theta>" by auto
  have "hpsafe (Assign x \<theta>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow>  (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (Assign x \<theta>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (Assign x \<theta>)))"
    proof -
      assume hpsafe:"hpsafe (Assign x \<theta>)"
      assume ssafe:"ssafe \<sigma>"
      from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
          "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
          unfolding ssafe_def by auto
      from hpsafe have dsafe:"dsafe \<theta>" by (auto elim: hpsafe.cases)
      fix \<nu> \<omega>
      show "?thesis \<nu> \<omega>"
        using subst_dterm[OF good_interp TA dsafe ssafes]
        by auto
    qed
  then show ?case by auto
next
  case (Padmit_DiffAssign \<sigma> \<theta> x) then
  have TA:"Tadmit \<sigma> \<theta>" by auto
  have "hpsafe (DiffAssign x \<theta>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow>  (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (DiffAssign x \<theta>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (DiffAssign x \<theta>)))"
    proof -
      assume hpsafe:"hpsafe (DiffAssign x \<theta>)"
      assume ssafe:"ssafe \<sigma>"
      from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
          "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
          unfolding ssafe_def by auto
      from hpsafe have dsafe:"dsafe \<theta>" by (auto elim: hpsafe.cases)
      fix \<nu> \<omega>
      show "?thesis \<nu> \<omega>"
        using subst_dterm[OF good_interp TA dsafe ssafes]
        by auto
    qed
  then show ?case by auto
next
  case (Padmit_Test \<sigma> \<phi>) then
   have IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
     by auto
   have "hpsafe (? \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (? \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (local.adjoint I \<sigma> \<nu>) (? \<phi>)))"
     proof -
       assume hpsafe:"hpsafe (? \<phi>)"
       from hpsafe have fsafe:"fsafe \<phi>" by (auto dest: hpsafe.cases)
       assume ssafe:"ssafe \<sigma>"
       fix \<nu> \<omega>
       show "?thesis \<nu> \<omega>" using IH[OF fsafe ssafe] by auto
     qed
   then show ?case by auto
next
  case (Fadmit_Geq \<sigma> \<theta>1 \<theta>2) then 
    have TA1:"Tadmit \<sigma> \<theta>1" and TA2:"Tadmit \<sigma> \<theta>2"
      by auto
    have "fsafe (Geq \<theta>1 \<theta>2) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (Geq \<theta>1 \<theta>2) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) (Geq \<theta>1 \<theta>2)))"
      proof -
        assume fsafe:"fsafe (Geq \<theta>1 \<theta>2)"
        assume ssafe:"ssafe \<sigma>"
        from fsafe have dsafe1:"dsafe \<theta>1" and dsafe2:"dsafe \<theta>2"
          by (auto dest: fsafe.cases)
        from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
          "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
          unfolding ssafe_def by auto
        fix \<nu>
        show "?thesis \<nu>" using 
          subst_dterm[OF good_interp TA1 dsafe1 ssafes]
          subst_dterm[OF good_interp TA2 dsafe2 ssafes]
          by auto 
      qed
    then show ?case by auto 
  next 
    case (Fadmit_Prop1 \<sigma> args p p') then
      have TA:"\<And>i. Tadmit \<sigma> (args i)"
      and some:"SPredicates \<sigma> p = Some p'"
      and NFA:"NFadmit (\<lambda>i. Tsubst (args i) \<sigma>) p'"
        by auto
      have "fsafe ($\<phi> p args) \<Longrightarrow>
           ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst ($\<phi> p args) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) ($\<phi> p args)))"
        proof -
          assume fsafe:"fsafe ($\<phi> p args)"
          assume ssafe:"ssafe \<sigma>"
          from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
          "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
          unfolding ssafe_def by auto
          fix \<nu>
          from fsafe have frees:"\<And>i. dfree (args i)" by auto
          from frees have safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
          have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
              dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
            using  subst_dterm[OF good_interp TA safes ssafes] by auto
          have eqs:"\<And>i \<nu>'. dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>"
            by (auto simp add: IH safes)
          let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
          have subFree:"(\<And>i. dfree (?sub i))"
            using tsubst_preserves_free[OF frees ssafes(1)]
            by (simp add: frees ssafes tsubst_preserves_free)
          have freef:"fsafe p'" using ssafe some unfolding ssafe_def by auto 
          have IH2:"(\<nu> \<in> fml_sem I (NFsubst p' ?sub)) = (\<nu> \<in> fml_sem (NTadjoint I ?sub \<nu>) p')"
            using nsubst_fml good_interp NFA freef subFree
            by blast
          have vec:"(\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (args i) \<nu>)"
            apply(auto simp add: vec_eq_iff)
            subgoal for i
              using IH[of i, OF safes[of i]] 
              by auto
            done
          show "?thesis \<nu>" 
            using IH safes eqs apply (auto simp add:  IH2  some good_interp)
            using some unfolding adjoint_def NTadjoint_def by auto
          qed
    then show "?case" by auto
next
   case (Fadmit_Prop2 \<sigma> args p) 
    note TA = Fadmit_Prop2.hyps(1)
    and none = Fadmit_Prop2.hyps(2)
    have "fsafe (Prop p args) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>.(\<nu> \<in> fml_sem I (Fsubst ($\<phi> p args) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) ($\<phi> p args)))"
    proof -
      assume safe:"fsafe (Prop p args)" and ssafe:"ssafe \<sigma>"
      from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
          "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
          unfolding ssafe_def by auto
      fix \<nu>
      from safe have frees:"\<And>i. dfree (args i)" by auto
      hence safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
      have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
          dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
      using  subst_dterm[OF good_interp TA safes ssafes] by auto
      have Ieq:"Predicates I p = Predicates (adjoint I \<sigma> \<nu>) p"
        using none unfolding adjoint_def by auto
      have vec:"(\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)"
        apply(auto simp add: vec_eq_iff)
        subgoal for i using IH[of i, OF safes[of i]] by auto
        done
      show "?thesis \<nu>" using none IH Ieq vec by auto
    qed
    then show "?case" by auto
next
  case (Fadmit_Not \<sigma> \<phi>) then 
  have IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
    by blast
  have fsafe:"fsafe (Not \<phi>) \<Longrightarrow> fsafe \<phi>"
    by (auto dest: fsafe.cases)
  show ?case using IH[OF fsafe] by auto
next
  case (Fadmit_And \<sigma> \<phi> \<psi>) then
    have IH1:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
    and IH2:"fsafe \<psi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<psi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<psi>))"
      by (blast)+
    have fsafe1:"fsafe (\<phi> && \<psi>) \<Longrightarrow> fsafe \<phi>" and fsafe2:"fsafe (\<phi> && \<psi>) \<Longrightarrow> fsafe \<psi>" 
      by (auto dest: fsafe.cases)
    show ?case using IH1[OF fsafe1] IH2[OF fsafe2] by auto
next
  case (Fadmit_DiffFormula \<sigma> \<phi>)
  then show ?case sorry
next
  case (Fadmit_Exists \<sigma> \<phi> x)
  then have IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
    and FUA:"FUadmit \<sigma> \<phi> {Inl x}"
    by blast+
  have fsafe:"fsafe (Exists x \<phi>) \<Longrightarrow> fsafe \<phi>"
    by (auto dest: fsafe.cases)
  have eq:"fsafe (Exists x \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst  (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>)  (Exists x \<phi>)))"
    proof -
      assume fsafe:"fsafe (Exists x \<phi>)"
      from fsafe have fsafe':"fsafe \<phi>" by (auto dest: fsafe.cases)
      assume ssafe:"ssafe \<sigma>"
      fix \<nu>
      have agree:"\<And>r. Vagree \<nu> (repv \<nu> x r) (- {Inl x})"
        unfolding Vagree_def by auto
      have sem_eq:"\<And>r. ((repv \<nu> x r) \<in> fml_sem (local.adjoint I \<sigma> (repv \<nu> x r)) \<phi>) =
                        ((repv \<nu> x r) \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>)"
        using uadmit_fml_adjoint[OF FUA agree fsafe' ssafe good_interp] by auto
      have "(\<nu> \<in> fml_sem I (Fsubst  (Exists x \<phi>) \<sigma>)) = (\<exists>r. (repv \<nu> x r) \<in> fml_sem I (Fsubst \<phi> \<sigma>))"
        by auto
      moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (local.adjoint I \<sigma> (repv \<nu> x r)) \<phi>)"
        using IH[OF fsafe' ssafe] by auto
      moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>)"
        using sem_eq by auto
      moreover have "... = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (Exists x \<phi>))"
        by auto
      ultimately show "(\<nu> \<in> fml_sem I (Fsubst  (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>)  (Exists x \<phi>))"
        by auto
      qed
  then show ?case by auto
next
  case (Fadmit_Diamond \<sigma> \<phi> a) then 
    have PA:"Padmit \<sigma> a" 
    and FUA:"FUadmit \<sigma> \<phi> (BVP (Psubst a \<sigma>))"
    and IH1:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
    and IH2:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a))"
      by auto
    have "fsafe (\<langle> a \<rangle> \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (\<langle> a \<rangle> \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) (\<langle> a \<rangle> \<phi>)))"
    proof -
      assume fsafe:"fsafe (\<langle> a \<rangle> \<phi>)"
      assume ssafe:"ssafe \<sigma>"
      from fsafe have fsafe':"fsafe \<phi>" and hpsafe:"hpsafe a" by (auto dest: fsafe.cases)
      fix \<nu>
      have agree:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<omega> (-BVP(Psubst a \<sigma>))"
        using bound_effect[OF good_interp, of "(Psubst a \<sigma>)" \<nu>, OF psubst_preserves_safe[OF ssafe hpsafe PA]] by auto
      have sem_eq:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> 
          (\<omega> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>) =
          (\<omega> \<in> fml_sem (local.adjoint I \<sigma> \<omega>) \<phi>)"
        using uadmit_fml_adjoint[OF FUA agree fsafe' ssafe good_interp] by auto
      have "(\<nu> \<in> fml_sem I (Fsubst (\<langle> a \<rangle> \<phi>) \<sigma>)) = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>) \<and> \<omega> \<in> fml_sem I (Fsubst \<phi> \<sigma>))"
        by auto
      moreover have "... = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a \<and> \<omega> \<in> fml_sem (adjoint I \<sigma> \<omega>) \<phi>)"
        using IH1[OF fsafe' ssafe] IH2[OF hpsafe ssafe, of \<nu>] by auto
      moreover have "... = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a \<and> \<omega> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>)"
        using sem_eq IH2 hpsafe ssafe by blast
      moreover have "... = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (\<langle> a \<rangle> \<phi>))"
        by auto
      ultimately show "?thesis \<nu>" by auto
    qed
  then show ?case by auto
next
   case (Fadmit_Prop1 \<sigma> args p p') 
       have "fsafe(Prop p args) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>.(\<nu> \<in> fml_sem I (Fsubst ($\<phi> p args) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) ($\<phi> p args)))"
      proof -
        assume fsafe:"fsafe (Prop p args)"
        and ssafe:"ssafe \<sigma>"
        from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
          "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
          unfolding ssafe_def by auto
        fix \<nu>
        note TA = Fadmit_Prop1.hyps(1)
        and some = Fadmit_Prop1.hyps(2) and NFA = Fadmit_Prop1.hyps(3)
        from fsafe have frees:"\<And>i. dfree (args i)" by auto
        from frees have safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
        have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
            dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
          using  subst_dterm[OF good_interp TA safes ssafes] by auto
        have eqs:"\<And>i \<nu>'. dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>"
          by (auto simp add: IH safes)
        let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
        have subFree:"(\<And>i. dfree (?sub i))"
          using tsubst_preserves_free[OF frees ssafes(1)]
          by (simp add: frees ssafes tsubst_preserves_free)
        have freef:"fsafe p'" using ssafe some unfolding ssafe_def by auto 
        have IH2:"(\<nu> \<in> fml_sem I (NFsubst p' ?sub)) = (\<nu> \<in> fml_sem (NTadjoint I ?sub \<nu>) p')"
          by (simp add: nsubst_fml [OF good_interp NFA freef subFree])
        have vec:"(\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (local.adjoint I \<sigma> \<nu>) (args i) \<nu>)"
          apply(auto simp add: vec_eq_iff)
          subgoal for i
            using IH[of i, OF safes[of i]] 
            by auto
          done
        show "?thesis \<nu>" 
          using IH safes eqs apply (auto simp add:  IH2  some good_interp)
          using some unfolding adjoint_def NTadjoint_def by auto
      qed    
next
  case (Fadmit_Context1 \<sigma> \<phi> C C') then
   have FA:"Fadmit \<sigma> \<phi>"
   and FUA:"FUadmit \<sigma> \<phi> UNIV"
   and some:"SContexts \<sigma> C = Some C'"
   and PFA:"PFadmit (\<lambda>(). Fsubst \<phi> \<sigma>) C'"
   and IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
     by auto
   have "fsafe (InContext C \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) (InContext C \<phi>)))"
     proof -
       assume safe:"fsafe (InContext C \<phi>)"
       from safe have fsafe:"fsafe \<phi>" by (auto dest: fsafe.cases)
       assume ssafe:"ssafe \<sigma>"
       fix \<nu> :: "'sz state"
       have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
       have adj_eq:"\<And>\<omega>. fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
         using uadmit_fml_adjoint[OF FUA agree fsafe ssafe good_interp] by auto
       have eq:"(\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>)"
         using adj_eq IH[OF fsafe ssafe] by auto
       let ?sub = "(\<lambda>(). Fsubst \<phi> \<sigma>)"
       let ?R1 = "fml_sem I (Fsubst \<phi> \<sigma>)"
       let ?R2 = "fml_sem (adjoint I \<sigma> \<nu>) \<phi>"
       have eq':"?R1 = ?R2"
         using adj_eq IH[OF fsafe ssafe] by auto
       have subSafe:"(\<And>i. fsafe (?sub i))"
         using fsubst_preserves_safe[OF ssafe fsafe FA]
         by (simp add: case_unit_Unity)
       have freef:"fsafe C'" using ssafe some unfolding ssafe_def by auto 
       have IH2:"(\<nu> \<in> fml_sem I (PFsubst C' ?sub)) = (\<nu> \<in> fml_sem (PFadjoint I ?sub) C')"
         using psubst_fml good_interp PFA fsafe subSafe freef by blast 
       have IH':"(\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
         using IH[OF fsafe ssafe] by auto
       then have IH:"fml_sem I (Fsubst \<phi> \<sigma>) = fml_sem (adjoint I \<sigma> \<nu>) \<phi>"
         using eq' by blast
       have duh:" (\<lambda>f' _. fml_sem I (case () of () \<Rightarrow> Fsubst \<phi> \<sigma>)) = (\<lambda> x (). fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>)"
         by (simp add: case_unit_Unity eq' ext)
       have extend_PF:"(PFadjoint I ?sub) = (extendc I ?R2)"
         unfolding PFadjoint_def using IH apply (simp)
         by (metis old.unit.case old.unit.exhaust)
       have "(\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem I (PFsubst C' (\<lambda>(). Fsubst \<phi> \<sigma>)))"
         using some by simp
       moreover have "... = (\<nu> \<in> fml_sem (PFadjoint I ?sub) C')"
         using IH2 by auto
       moreover have "... = (\<nu> \<in> fml_sem (extendc I ?R2) C')"
         using extend_PF by simp
       moreover have "... = (\<nu> \<in> fml_sem (extendc I ?R1) C')"
         using eq' by auto
       moreover have "... = (\<nu> \<in> Contexts (adjoint I \<sigma> \<nu>) C (fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
         using some unfolding adjoint_def apply auto
         apply (simp add: eq' local.adjoint_def)
         by (simp add: eq' local.adjoint_def)
       moreover have "... = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (InContext C \<phi>))"
         by auto
       ultimately
       show "(\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) (InContext C \<phi>))"
         by blast
     qed
   then show ?case by auto
next
  case (Fadmit_Context2 \<sigma> \<phi> C) then
    have FA:"Fadmit \<sigma> \<phi>"
    and FUA:"FUadmit \<sigma> \<phi> UNIV"
    and none:"SContexts \<sigma> C = None"
    and IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>))"
      by auto
    have "fsafe (InContext C \<phi>) \<Longrightarrow>
             ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) (InContext C \<phi>)))"
      proof -
        assume safe:"fsafe (InContext C \<phi>)"
        then have fsafe:"fsafe \<phi>" by (auto dest: fsafe.cases)
        assume ssafe:"ssafe \<sigma>"
        fix \<nu>
        have Ieq:" Contexts (local.adjoint I \<sigma> \<nu>) C = Contexts I C"
          using none unfolding adjoint_def by auto
        have IH':"\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>)"
          using IH[OF fsafe ssafe] by auto
        have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
        have adj_eq:"\<And>\<omega>. fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
          using uadmit_fml_adjoint[OF FUA agree fsafe ssafe good_interp] by auto
        then have sem:"fml_sem I (Fsubst \<phi> \<sigma>) =  fml_sem (local.adjoint I \<sigma> \<nu>) \<phi>"
          using IH' agree adj_eq by auto
        show "?thesis \<nu>"  using none Ieq sem by auto
      qed
  then show ?case by auto
qed

  
subsection \<open>Unused, unproven lemmas\<close>
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

end end