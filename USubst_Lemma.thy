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

lemma uadmit_sterm_adjoint:"TUadmit \<sigma> \<theta> U \<Longrightarrow> Vagree \<nu> \<omega> (-U) \<Longrightarrow> sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
  sorry

lemma uadmit_dterm_adjoint:"TUadmit \<sigma> \<theta> U \<Longrightarrow> Vagree \<nu> \<omega> (-U) \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
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

lemma nsubst_frechet:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"
shows "dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> frechet I (NTsubst \<theta> \<sigma>) (fst \<nu>) = frechet (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induct rule: dfree.induct)    
  case (dfree_Fun args f) then
  show "?case"
    unfolding NTsubst.simps NTadjoint_def
     apply (cases "f")
     apply (auto simp add:  NTadjoint_free nsubst_sterm good_interp)
    
  subgoal
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
    sorry
  done
qed (auto  simp add: nsubst_sterm)

lemma subst_frechet:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"
shows "dfree \<theta> \<Longrightarrow> (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> frechet I (Tsubst \<theta> \<sigma>) (fst \<nu>) = frechet (adjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
sorry

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
fixes \<nu>'::"'sz state"
assumes good_interp:"is_interp I"    
shows "NTadmit \<sigma> \<theta> \<Longrightarrow> dfree \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dterm_sem I (NTsubst \<theta> \<sigma>) \<nu>' = dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> \<nu>'"
  sorry

(*proof (induction rule: NTadmit.induct)
  case (NTadmit_Fun \<sigma> args f) 
    thus "?case" (*by (cases "f") (auto simp add: vec_extensionality  NTadjoint_def)*)
      sorry
next
    case (NTadmit_Diff \<sigma> \<theta>) 
    hence admit:"NTadmit \<sigma> \<theta>"
      and admitU:"NTUadmit \<sigma> \<theta> UNIV"
      and IH : "dsafe \<theta> \<Longrightarrow>
            (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dterm_sem I (NTsubst \<theta> \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> \<nu>"
      and safe: "dsafe (Differential \<theta>)" 
      and freeSub:"\<And>i. dfree (\<sigma> i)"
      (*by auto*) sorry
    have free:"dfree \<theta>" using safe by auto
    have sem:"sterm_sem I (NTsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
      using nsubst_sterm[OF free freeSub] by auto
    then show "dterm_sem I (NTsubst (Differential \<theta>) \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) (Differential \<theta>) \<nu>"
      (*by (auto simp add: directional_derivative_def frechet_correctness nsubst_frechet[OF good_interp free freeSub])*)
      sorry
qed (auto simp add: NTadmit.cases)
*)

lemma ntsubst_preserves_free:
"dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dfree(NTsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case"
    by (cases "i") (auto intro:dfree.intros)
qed (auto intro: dfree.intros)

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

lemma tsubst_preserves_free:
"dfree \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dfree(Tsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case" 
    by (cases "SFunctions \<sigma> i") (auto intro:dfree.intros ntsubst_preserves_free)
qed (auto intro: dfree.intros)

lemma tsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dsafe(Tsubst \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Fun args i) then show "?case" 
    sorry 
    (* by (cases "SFunctions \<sigma> i") (auto intro:dsafe.intros ntsubst_preserves_safe tsubst_preserves_free dfree_is_dsafe)*)
qed (auto intro: dsafe.intros tsubst_preserves_free)

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

lemma extendf_safe:
assumes good_interp:"is_interp I"
shows "is_interp (extendf I R)"
  sorry

lemma extendc_safe:
assumes good_interp:"is_interp I"
shows "is_interp (extendc I R)"
  sorry

lemma extendf_deriv:
  fixes f'::"('sf + 'sz,'sz) trm" and I::"('sf,'sc,'sz) interp"
  assumes free:"dfree f'"
  assumes good_interp:"is_interp I"
  assumes some:"SFunctions \<sigma> i = Some f'"
  shows "\<exists>f''. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) f' \<nu>) has_derivative f'' x) (at x)"
  using free apply (induction rule: dfree.induct)
  apply(auto)+
  subgoal for i 
    apply(rule exI)
    apply(rule allI)
    apply(subst has_derivative_const)
    by auto
  subgoal for r
    apply(rule exI)
    apply(rule allI)
    apply(subst has_derivative_const)
    by auto
  prefer 2
  subgoal for t1 t2 f'1 f'2
    apply(rule exI)
    apply(rule allI)
    apply(subst has_derivative_add)
    by auto
  prefer 2
  subgoal for t1 t2 f'1 f'2
    apply(rule exI)
    apply(rule allI)
    apply(subst has_derivative_mult)
    by auto
    subgoal for args i apply(cases "i")
    proof -
    fix a::"'sf"
    (*fix args::"'sz \<Rightarrow> ('sf + 'sz,'sz) trm" and i::"'sf + 'sz"*)
    assume dfrees:"(\<And>i. dfree (args i))"
    assume IH:"(\<And>i. \<exists>f''. \<forall>x. ((\<lambda>R. dterm_sem
                                     \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I,
                                        Programs = Programs I, ODEs = ODEs I\<rparr>
                                     (args i) \<nu>) has_derivative
                               f'' x)
                               (at x))"
    from IH have IH':"(\<And>i x. \<exists>f''.((\<lambda>R. dterm_sem
                                     \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I,
                                        Programs = Programs I, ODEs = ODEs I\<rparr>
                                     (args i) \<nu>) has_derivative
                               f'' i x)
                               (at x))"
      sorry
      (*sledgehammer*)
    then have IHvec:"\<exists> f. (\<forall> x. ((\<lambda> R. \<chi> i. dterm_sem (extendf I R) (args i) \<nu>) has_derivative f x) (at x))"
      sorry
    assume a:"i = Inl a"
    (*obtain f''' where allX:"\<forall>x. ((\<lambda>R. dterm_sem
                                     \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I,
                                        Programs = Programs I, ODEs = ODEs I\<rparr>
                                     (args a) \<nu>) has_derivative
                               f''' x)
                               (at x)"
        using IH by auto*)
    note chain = Deriv.derivative_intros(105)
    let ?f = "(\<lambda>x. Functions I a x)"
    let ?g = "(\<lambda> R. (\<chi> i. dterm_sem
                       \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I,
                          Programs = Programs I, ODEs = ODEs I\<rparr>
                       (args i) \<nu>))"
    have fg_eq:"(\<lambda>R. Functions I a
                (\<chi> i. dterm_sem
                       \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I,
                          Programs = Programs I, ODEs = ODEs I\<rparr>
                       (args i) \<nu>)) = (?f \<circ> ?g)"
      by auto
    (*((\<lambda>x. \<chi> i. f i x) has_derivative (\<lambda>h. \<chi> i. f' i h)) F*)
    let ?ff = "(\<lambda>x. \<chi> i. (\<lambda>R. \<chi> i. dterm_sem
                    \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                       ODEs = ODEs I\<rparr>
                    (args i) \<nu>) x $ i)"
    have f4:"\<exists> f4. \<forall>x. (?ff has_derivative (f4 x)) (at x)"
      using IHvec by auto
    have "\<exists>f''. \<forall>x. ((?f o ?g) has_derivative f'' x) (at x)"
      apply (rule exI)
      apply (rule allI)
      apply (rule chain)
      using f4 apply (auto)
      apply(auto)
      subgoal for x
        
      apply (rule f4)
        sorry
        (*apply (auto intro: derivative_eq_intros)*)
        (*using IH has_derivative_vec sledgehammer*)
      using good_interp unfolding is_interp_def by auto
    show "\<exists>f''. \<forall>x. ((\<lambda>R. (case i of Inl x \<Rightarrow> Functions I x | Inr f' \<Rightarrow> \<lambda>_. R $ f')
                               (\<chi> i. dterm_sem
                                      \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I,
                                         Programs = Programs I, ODEs = ODEs I\<rparr>
                                      (args i) \<nu>)) has_derivative
                         f'' x)
                         (at x)"
      using a apply auto
        apply(rule exI)
        apply(rule allI)
        using chain apply(auto)
        sorry
      apply(rule exI[where x= f'''])
      using a allX apply (auto)
      subgoal for x
        apply (erule allE[where x=x])
        apply auto
  qed
  subgoal for args i
    subgoal for a
      apply(auto)
      sorry
    apply(auto)
    subgoal for b
      apply(rule allI)
      using has_derivative_proj'[of i] apply auto
      sledgehammer
        apply(rule allI)
        apply auto
      apply(rule has_derivative_proj')
      using  apply auto
      apply(rule exI[where x= "undefined"])
    sorry
  done
    (*proof -
      fix a
      assume frees:"(\<And>i. dfree (args i))"
      assume existss:"(\<And>i. \<exists>f''. \<forall>x. ((\<lambda>R. dterm_sem
                           \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I,
                              Programs = Programs I, ODEs = ODEs I\<rparr>
                           (args i) \<nu>) has_derivative
                     f'' x)
                     (at x))"
      assume inr:"i = Inr a"
      from frees have free:"dfree (args a)" by auto
      from existss have exists:"\<exists>f''. \<forall>x. ((\<lambda>R. dterm_sem
                         \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I,
                            Programs = Programs I, ODEs = ODEs I\<rparr>
                         (args a) \<nu>) has_derivative
                   f'' x)
                   (at x)"
        by auto
      then obtain f'' where f''d:"\<And>x. ((\<lambda>R. dterm_sem
                         \<lparr>Functions = case_sum (Functions I) (\<lambda>f' _. R $ f'), Predicates = Predicates I, Contexts = Contexts I,
                            Programs = Programs I, ODEs = ODEs I\<rparr>
                         (args a) \<nu>) has_derivative
                   f'' x)
                   (at x)"
          by auto
      have blah:"\<And>x. ((\<lambda>R. R $ a) has_derivative (\<lambda>x. axis a 1)) (at x)"
        sorry
      show "\<exists>f'''. \<forall>x. ((\<lambda>R. R $ a) has_derivative f''' x) (at x)"
        sorry 
      qed
    apply(rule allI)*)
  oops
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
        obtain f'' where Pf:"?Poo f''"
            using extendf_deriv[OF good_subst[of i f'] good_interp, of \<sigma> i "\<nu>", OF some some]
            by auto
        have "(THE G. (?f has_derivative G) (at x)) = f'' x"
          apply(rule the_deriv)
          using Pf by auto
        then have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = f''"
          using Pf the_all_deriv by auto
        show "((\<lambda>R. dterm_sem (extendf I R) f' \<nu>) has_derivative (THE f'a. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) f' \<nu>) has_derivative f'a x) (at x)) x) (at x)"
          using the_eq Pf by blast
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
      using tsubst_preserves_safe[OF safes sfree] by simp
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
        by auto
      have VA:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
      have dsem:"\<And>\<nu> \<omega>. dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
        using uadmit_dterm_adjoint[OF TUA VA] by auto 
      have ssem:"\<And>\<nu> \<omega>. sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
        using uadmit_sterm_adjoint[OF TUA VA] by auto 
      from safe have free:"dfree \<theta>" by (auto dest: dsafe.cases intro: dfree.intros)
      from free have tsafe:"dsafe \<theta>" using dfree_is_dsafe by auto
      have freeSubst:"dfree (Tsubst \<theta> \<sigma>)" 
        using tsubst_preserves_free[OF free sfree]
        by auto 
      have IH':"\<And>\<nu>. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> \<nu>"
        using IH[OF tsafe sfree] by auto
      have IH'':"\<And>\<nu>'. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu>' = dterm_sem (local.adjoint I \<sigma> \<nu>) \<theta> \<nu>'"
        subgoal for \<nu>'
        using uadmit_dterm_adjoint[OF TUA VA, of I \<nu> \<nu>'] IH'[of \<nu>'] by auto
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
      have frech:"frechet I (Tsubst \<theta> \<sigma>) (fst \<nu>) = frechet (adjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
        using subst_frechet[OF good_interp free sfree] by auto
    show "?case"
      apply (auto simp add: directional_derivative_def fun_eq_iff)
        using sterm_determines_frechet[of I "(adjoint I \<sigma> \<nu>)" "(Tsubst \<theta> \<sigma>)" \<theta> "\<nu>", 
            OF good_interp adjoint_safe[OF good_interp sfree] tsubst_preserves_free[OF free sfree] 
            free sem_eq]
        by auto
  qed auto
end end