theory "USubst_Lemma"
imports
  Ordinary_Differential_Equations.ODE_Analysis
  "./Ids"
  "./Lib"
  "./Syntax"
  "./Denotational_Semantics"
  "./Frechet_Correctness"
  "./Static_Semantics"
  "./Coincidence"
  "./Bound_Effect"
  "./Differential_Axioms"
  "./USubst"
begin
section \<open>Soundness proof for uniform substitution rule\<close>
lemma interp_eq:
  "f = f' \<Longrightarrow> F = F' \<Longrightarrow> p = p' \<Longrightarrow> c = c' \<Longrightarrow> PP = PP' \<Longrightarrow> ode = ode' \<Longrightarrow> odebv = odebv' \<Longrightarrow>
   \<lparr>Functions = f, Funls = F, Predicates = p, Contexts = c, Programs = PP, ODEs = ode, ODEBV = odebv\<rparr> =
   \<lparr>Functions = f', Funls = F', Predicates = p', Contexts = c', Programs = PP', ODEs = ode', ODEBV = odebv'\<rparr>"
  by auto

subsection \<open>Lemmas about well-formedness of (adjoint) interpretations.\<close>

text \<open>When adding a function to an interpretation with {\tt extendf}, we need to show it's C1 continuous.
  We do this by explicitly constructing the derivative {\tt extendf\_deriv} and showing it's continuous.\<close>
primrec extendf_deriv :: " interp \<Rightarrow> ident \<Rightarrow> trm \<Rightarrow> state \<Rightarrow> Rvec \<Rightarrow> (Rvec \<Rightarrow> real)"
where
  "extendf_deriv I _ (Var i) \<nu> x = (\<lambda>_. 0)"
| "extendf_deriv I _ (Const r) \<nu> x = (\<lambda>_. 0)"
| "extendf_deriv I g (Function f args) \<nu> x =
  (case args_to_id f of 
    Some (Inl ff) \<Rightarrow> (THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y))
              (\<chi> i. dterm_sem
                     \<lparr>Functions = (\<lambda> z. case args_to_id z of Some (Inl a) \<Rightarrow> Functions I z | Some (Inr b) \<Rightarrow>  (\<lambda>f' _. x $ f') b | None \<Rightarrow> Functions I z), 
                      Funls =     (\<lambda> z. case args_to_id z of Some (Inl a) \<Rightarrow> Funls I z | Some (Inr b) \<Rightarrow>  (\<lambda>f' _. x $ f') b | None \<Rightarrow> Funls I z), 
                      Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                      ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                     (args i) \<nu>) \<circ>
             (\<lambda>\<nu>'. \<chi> ia. extendf_deriv I g (args ia) \<nu> x \<nu>')
  | Some (Inr ff) \<Rightarrow> (\<lambda> \<nu>'. \<nu>' $ ff))"
| "extendf_deriv I g (Plus t1 t2) \<nu> x = (\<lambda>\<nu>'. (extendf_deriv I g t1 \<nu> x \<nu>') + (extendf_deriv I g t2 \<nu> x \<nu>'))"
| "extendf_deriv I g (Neg t1 ) \<nu> x = (\<lambda>\<nu>'. - (extendf_deriv I g t1 \<nu> x \<nu>'))"
| "extendf_deriv I g (Times t1 t2) \<nu> x = 
   (\<lambda>\<nu>'. ((dterm_sem (extendf I x) t1 \<nu> * (extendf_deriv I g t2 \<nu> x \<nu>'))) 
       + (extendf_deriv I g t1 \<nu> x \<nu>') * (dterm_sem (extendf I x) t2 \<nu>))"
| "extendf_deriv I g ($$F _) \<nu> = undefined"
| "extendf_deriv I g ($' _) \<nu> = undefined"
| "extendf_deriv I g (Differential _) \<nu> = undefined"

lemma extendf_dterm_sem_continuous:
  fixes f'::"trm" and I::"interp"
  assumes free:"dfree f'"
  assumes good_interp:"is_interp I"
  shows "continuous_on UNIV (\<lambda>x. dterm_sem (extendf I x) f' \<nu>)"
proof(induction rule: dfree.induct[OF free])
  case (3 f args) then have
    nb:"nonbase f"
    and l:"ilength f < MAX_STR"
    and f:"\<And>j. dfree (args j)"
    and co:" \<And>j. continuous_on UNIV (\<lambda>x. dterm_sem (extendf I x) (args j) \<nu>)" by auto
  then 
  obtain inj where some:"args_to_id f = Some inj" using nonbase_some[OF nb] by auto
    show ?case 
    apply(cases "inj")
      using some  apply (auto simp add: some continuous_intros simp del: args_to_id.simps)
    subgoal for a
      apply (rule continuous_on_compose2[of UNIV "Functions I f" UNIV "(\<lambda> x. (\<chi> i. dterm_sem
               \<lparr>Functions = (\<lambda> f. case args_to_id f of Some (Inl x) \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow>  (\<lambda> _. x $ f') | None \<Rightarrow> Functions I f), 
                Funls = (\<lambda> f. case args_to_id f of Some (Inl x) \<Rightarrow> (Funls I) f | Some (Inr f') \<Rightarrow>  (\<lambda>_. x $ f') | None \<Rightarrow> Funls I f),
                Predicates = Predicates I, Contexts = Contexts I,
                          Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                       (args i) \<nu>))"])
      subgoal
        using is_interpD[OF good_interp]
        using has_derivative_continuous_on[of UNIV "(Functions I f)" "(THE f'. \<forall>x. (Functions I f has_derivative f' x) (at x))"] 
        by auto
       apply(rule continuous_on_vec_lambda)
      using some co by (auto simp add: some simp del: args_to_id.simps)
    done
qed (auto simp add: continuous_intros)

lemma extendf_deriv_bounded:
  fixes f'::"trm" and I::"interp"
  assumes free:"dfree f'"
  assumes good_interp:"is_interp I"
  shows "bounded_linear (extendf_deriv I i f' \<nu> x)"
proof(induction rule: dfree.induct[OF free])
  case (1 i)
  then show ?case by auto
next
  case (2 r)
  then show ?case by auto
next
  case (3 f args) then have
    nb:"nonbase f"
    and l:"ilength f < MAX_STR"
    and f:"\<And>j. dfree (args j)"
    and bl:" \<And>j. bounded_linear (extendf_deriv I i (args j) \<nu> x)" by auto
  obtain inj where some:"args_to_id f = Some inj" using nonbase_some[OF nb] by auto
  then show ?case apply (auto simp del: args_to_id.simps)
    apply(cases "inj")
     using some apply (auto simp add: some simp del: args_to_id.simps)
    subgoal for a
      apply(rule bounded_linear_compose[of "(THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y))
           (\<chi> i. dterm_sem
                 \<lparr>Functions = (\<lambda> z. case args_to_id z of Some (Inl a) \<Rightarrow> Functions I z | Some (Inr b) \<Rightarrow>  (\<lambda> _. x $ b) | None \<Rightarrow> Functions I z), 
                  Funls = (\<lambda> z. case args_to_id z of Some (Inl a) \<Rightarrow> Funls I z | Some (Inr b) \<Rightarrow>  (\<lambda>_. x $ b) | None \<Rightarrow> Funls I z), 
                  Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                     ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                  (args i) \<nu>)"])
       subgoal using good_interp unfolding is_interp_def  using has_derivative_bounded_linear by fastforce
      apply(rule bounded_linear_vec)
      using some  by (auto simp add: some bl)
    done
next
  case (4 \<theta>\<^sub>1 \<theta>\<^sub>2)
  then show ?case apply auto
    using bounded_linear_add by blast
  case (5 \<theta>\<^sub>1)
  then show ?case apply auto
    using bounded_linear_minus by blast
next
  case (6 \<theta>\<^sub>1 \<theta>\<^sub>2)
  then show ?case apply auto
    apply(rule bounded_linear_add)
     apply(rule bounded_linear_const_mult)
     subgoal by auto
    apply(rule bounded_linear_mult_const)
    subgoal by auto
    done
qed

lemma extendf_deriv_continuous:
  fixes f'::"trm" and I::"interp"
  assumes free:"dfree f'"
  assumes good_interp:"is_interp I"
  shows "continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i f' \<nu> x))"
proof (induction rule: dfree.induct[OF free])
  case (3 f args)
then have
      nb:"nonbase f"
    and l:"ilength f < MAX_STR"
    and f:"\<And>j. dfree (args j)"
    and co:" \<And>j.  continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i (args j) \<nu> x))" by auto
  obtain inj where some:"args_to_id f = Some inj" using nonbase_some[OF nb] by auto
  have dfrees:"\<And>i. dfree (args i)"
   and const:"\<And>j. continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i (args j) \<nu> x))"
    using 3 by auto
  then show ?case 
(*    unfolding extendf_deriv.simps*)
    apply(cases "inj")
    using some apply(auto simp add: some simp del: args_to_id.simps extendf_deriv.simps)
    subgoal for a 
(*      apply (simp del: args_to_id.simps extendf_deriv.simps)*)
    proof -
      assume injs:"inj = Inl a"
      then have cs:"args_to_id f = Some (Inl a)" using some by auto
      let ?f = "\<lambda> x. ((THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y))
                        (\<chi> i. dterm_sem (extendf I x) (args i) \<nu>) )"
      let ?g = "\<lambda>x b . (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b)"
      let ?h = "\<lambda>x b . (?f x) (?g x b)"
      have boundedF:"\<And>x. bounded_linear (?f x)"
        using blinfun.bounded_linear_right using good_interp unfolding is_interp_def 
        by auto
      have boundedG:"\<And>x. bounded_linear (?g x)"
        by (simp add: bounded_linear_vec dfrees extendf_deriv_bounded good_interp)
      have boundedGG:"\<And>x. bounded_linear (\<lambda> b. (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b))"
          by (simp add: bounded_linear_vec dfrees extendf_deriv_bounded good_interp)
      have boundedH:"\<And>x. bounded_linear (?h x)"
        using bounded_linear_compose  boundedG boundedF by blast
      have freq:"(\<lambda>x. blinfun_compose(Blinfun((THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y))
                        (\<chi> i. dterm_sem (extendf I x)
                               (args i) \<nu>) )) (Blinfun(\<lambda> b. (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b))))
                = (\<lambda>x. Blinfun (extendf_deriv I i ($f f args) \<nu> x))"
          apply(rule ext)
          apply(rule blinfun_eqI)
          subgoal for x ia
            using boundedGG[of x]  blinfun_apply_blinfun_compose bounded_linear_Blinfun_apply
          proof -
            have f1: "bounded_linear (\<lambda>v. FunctionFrechet I f (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>) (\<chi> s. extendf_deriv I i (args s) \<nu> x v))"
              using FunctionFrechet.simps \<open>bounded_linear (\<lambda>b. (THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y)) (\<chi> i. dterm_sem (extendf I x) (args i) \<nu>) (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b))\<close>
              by fastforce          
            have bl:"bounded_linear (FunctionFrechet I f (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>))"
              using good_interp is_interp_def by blast
            have bl2:"bounded_linear 
               (Blinfun ((THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y)) (\<chi> i. dterm_sem (extendf I x) (args i) \<nu>)) o\<^sub>L
                Blinfun (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b))"
              using blinfun.bounded_linear_right by blast
            from bl have "blinfun_apply (Blinfun (FunctionFrechet I f (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>))) (\<chi> s. extendf_deriv I i (args s) \<nu> x ia) = blinfun_apply (Blinfun (\<lambda>v. FunctionFrechet I f (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>) (\<chi> s. extendf_deriv I i (args s) \<nu> x v))) ia"
              using f1 by (simp add: bounded_linear_Blinfun_apply)
            then have app:"blinfun_apply (Blinfun (FunctionFrechet I f (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>))) (\<chi> s. extendf_deriv I i (args s) \<nu> x ia) = blinfun_apply (Blinfun (\<lambda>v. FunctionFrechet I f (\<chi> s. dterm_sem (extendf I x) (args s) \<nu>) (\<chi> s. extendf_deriv I i (args s) \<nu> x v))) ia \<and> bounded_linear (\<lambda>v. \<chi> s. extendf_deriv I i (args s) \<nu> x v)"
              by (metis \<open>bounded_linear (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)\<close>)
            have bb:"bounded_linear (extendf_deriv I i ($f f args) \<nu> x)"
              using dfree_Fun dfrees extendf_deriv_bounded good_interp 
              using "3.hyps"(1) "3.hyps"(2) "3.hyps" by blast
            have hm:"( (Blinfun ((THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y)) (\<chi> i. dterm_sem (extendf I x) (args i) \<nu>))) 
                       o\<^sub>L(Blinfun (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)))
                  =   (Blinfun 
                        (((THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y)) (\<chi> i. dterm_sem (extendf I x) (args i) \<nu>)) 
                       \<circ>  (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b))) "
              apply(rule Bounded_Linear_Function.blinfun_compose.abs_eq)
               apply(simp only: eq_onp_def)
               apply(rule conjI)
                apply (metis FunctionFrechet.simps eq_onp_live_step good_interp has_derivative_bounded_linear is_interpD)
              apply(rule refl)
               apply(simp only: eq_onp_def)
              apply(rule conjI)
              subgoal
              using FunctionFrechet.simps eq_onp_live_step good_interp has_derivative_bounded_linear is_interpD
            proof -
              show "bounded_linear (\<lambda>v. \<chi> ia. extendf_deriv I i (args ia) \<nu> x v)"
                by (metis \<open>bounded_linear (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)\<close>) 
            qed
            by(rule refl)
          have hrm:"blinfun_apply
     (Blinfun
       ((THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y)) (\<chi> i. dterm_sem (extendf I x) (args i) \<nu>) \<circ>
        (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)))
      = ((THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y)) (\<chi> i. dterm_sem (extendf I x) (args i) \<nu>) \<circ>
        (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)) "
            apply(rule bounded_linear_Blinfun_apply)
            using f1 bl bb bl2
            by (simp add: blinfun_compose.rep_eq boundedGG bounded_linear_Blinfun_apply)
          show ?thesis 
              apply(simp only: bounded_linear_Blinfun_apply[OF bb] hm hrm)
            apply(unfold comp_def)
            using cs
              by(simp add: cs del: args_to_id.simps)
          qed
        done       
      have bounds:"\<And>ia x. bounded_linear (extendf_deriv I i (args ia) \<nu> x)" 
        by (simp add: dfrees extendf_deriv_bounded good_interp)
      have vec_bound:"\<And>x. bounded_linear (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)" 
        by (simp add: boundedG)
      have blinfun_vec:"(\<lambda>x. Blinfun (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)) = (\<lambda>x. blinfun_vec (\<lambda> ia.  Blinfun(\<lambda>b. extendf_deriv I i (args ia) \<nu> x b)))"
        apply(rule ext)
        apply(rule blinfun_eqI)
        apply(rule vec_extensionality)
        subgoal for x y ia
        proof -
          have "(\<chi> s. extendf_deriv I i (args s) \<nu> x y) $ ia = blinfun_apply (blinfun_vec (\<lambda>s. Blinfun (extendf_deriv I i (args s) \<nu> x))) y $ ia"
            by (simp add: bounded_linear_Blinfun_apply bounds)
          then have "(\<chi> s. extendf_deriv I i (args s) \<nu> x y) $ ia = blinfun_apply (blinfun_vec (\<lambda>s. Blinfun (extendf_deriv I i (args s) \<nu> x))) y $ ia \<and> bounded_linear (\<lambda>v. \<chi> s. extendf_deriv I i (args s) \<nu> x v)"
            by (metis \<open>bounded_linear (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)\<close>)
          then show ?thesis
            by (simp add: bounded_linear_Blinfun_apply)
        qed
        done
      have vec_cont:"continuous_on UNIV (\<lambda>x. blinfun_vec (\<lambda> ia.  Blinfun(\<lambda>b. extendf_deriv I i (args ia) \<nu> x b)))"
        apply(rule continuous_blinfun_vec')
        using "3.IH" by blast
      have cont_intro:"\<And> f g s. continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f x  o\<^sub>L  g x)"
        by(auto intro: continuous_intros)
      have cont:"continuous_on UNIV (\<lambda>x. blinfun_compose(Blinfun((THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y))
                        (\<chi> i. dterm_sem (extendf I x)
                               (args i) \<nu>) )) (Blinfun(\<lambda> b. (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b))))"
        apply(rule cont_intro)
         defer
         subgoal using blinfun_vec vec_cont by presburger
        apply(rule continuous_on_compose2[of UNIV "(\<lambda>x. Blinfun ((THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y)) x))"])
          subgoal using good_interp unfolding is_interp_def by simp
         apply(rule continuous_on_vec_lambda)
         subgoal for i using extendf_dterm_sem_continuous[OF dfrees[of i] good_interp] by auto
        by auto
      then show "?thesis"
          using freq  some cs  by metis
      qed
    proof -
      fix a
      assume "inj = Inr a"
      then have cs:"args_to_id f = Some (Inr a)" using some by auto
      let ?f = "\<lambda> x. ((THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y))
                        (\<chi> i. dterm_sem (extendf I x) (args i) \<nu>) )"
      let ?g = "\<lambda>x b . (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b)"
      let ?h = "\<lambda>x b . (?f x) (?g x b)"
      have boundedF:"\<And>x. bounded_linear (?f x)"
        using blinfun.bounded_linear_right using good_interp unfolding is_interp_def 
        by auto
      have boundedG:"\<And>x. bounded_linear (?g x)"
        by (simp add: bounded_linear_vec dfrees extendf_deriv_bounded good_interp)
      have boundedGG:"\<And>x. bounded_linear (\<lambda> b. (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b))"
          by (simp add: bounded_linear_vec dfrees extendf_deriv_bounded good_interp)
      have boundedH:"\<And>x. bounded_linear (?h x)"
        using bounded_linear_compose  boundedG boundedF by blast
      have freq:"\<And>x. (\<lambda> \<nu>'. \<nu>' $ a)
                = (extendf_deriv I i ($f f args) \<nu> x)"
        by (auto simp add: cs simp del: extendf.simps args_to_id.simps)
      then have freak:"(\<lambda>x. Blinfun (\<lambda> \<nu>'. \<nu>' $ a)) = (\<lambda>x. Blinfun(extendf_deriv I i ($f f args) \<nu> x))"
        by auto
      have bounds:"\<And>ia x. bounded_linear (extendf_deriv I i (args ia) \<nu> x)" 
        by (simp add: dfrees extendf_deriv_bounded good_interp)
      have vec_bound:"\<And>x. bounded_linear (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)" 
        by (simp add: boundedG)
      have blinfun_vec:"(\<lambda>x. Blinfun (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)) = (\<lambda>x. blinfun_vec (\<lambda> ia.  Blinfun(\<lambda>b. extendf_deriv I i (args ia) \<nu> x b)))"
        apply(rule ext)
        apply(rule blinfun_eqI)
        apply(rule vec_extensionality)
        subgoal for x y ia
        proof -
          have "(\<chi> s. extendf_deriv I i (args s) \<nu> x y) $ ia = blinfun_apply (blinfun_vec (\<lambda>s. Blinfun (extendf_deriv I i (args s) \<nu> x))) y $ ia"
            by (simp add: bounded_linear_Blinfun_apply bounds)
          then have "(\<chi> s. extendf_deriv I i (args s) \<nu> x y) $ ia = blinfun_apply (blinfun_vec (\<lambda>s. Blinfun (extendf_deriv I i (args s) \<nu> x))) y $ ia \<and> bounded_linear (\<lambda>v. \<chi> s. extendf_deriv I i (args s) \<nu> x v)"
            by (metis \<open>bounded_linear (\<lambda>b. \<chi> ia. extendf_deriv I i (args ia) \<nu> x b)\<close>)
          then show ?thesis
            by (simp add: bounded_linear_Blinfun_apply)
        qed
        done
      have vec_cont:"continuous_on UNIV (\<lambda>x. blinfun_vec (\<lambda> ia.  Blinfun(\<lambda>b. extendf_deriv I i (args ia) \<nu> x b)))"
        apply(rule continuous_blinfun_vec')
        using "3.IH" by blast
      have cont_intro:"\<And> f g s. continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f x  o\<^sub>L  g x)"
        by(auto intro: continuous_intros)
      have cont:"continuous_on UNIV (\<lambda>x. blinfun_compose(Blinfun((THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y))
                        (\<chi> i. dterm_sem (extendf I x)
                               (args i) \<nu>) )) (Blinfun(\<lambda> b. (\<chi> ia. extendf_deriv I i (args ia) \<nu> x b))))"
        apply(rule cont_intro)
         defer
         subgoal using blinfun_vec vec_cont by presburger
        apply(rule continuous_on_compose2[of UNIV "(\<lambda>x. Blinfun ((THE f'. \<forall>y. (Functions I a has_derivative f' y) (at y)) x))"])
          subgoal using good_interp unfolding is_interp_def by simp
         apply(rule continuous_on_vec_lambda)
         subgoal for i using extendf_dterm_sem_continuous[OF dfrees[of i] good_interp] by auto
        by auto
      then show "continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i ($f f args) \<nu> x))"
          using freak by(auto simp add: cs simp del: args_to_id.simps extendf.simps)
      qed
next
  case (4 \<theta>\<^sub>1 \<theta>\<^sub>2)
  assume free1:"dfree \<theta>\<^sub>1"
  assume free2:"dfree \<theta>\<^sub>2"
  assume IH1:"continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i \<theta>\<^sub>1 \<nu> x))"
  assume IH2:"continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i \<theta>\<^sub>2 \<nu> x))"
  have bound:"\<And>x. bounded_linear  (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a + extendf_deriv I i \<theta>\<^sub>2 \<nu> x a)"
    using extendf_deriv_bounded[OF free1 good_interp] extendf_deriv_bounded[OF free2 good_interp]
    by (simp add: bounded_linear_add)
  have eq:"(\<lambda>x. Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a + extendf_deriv I i \<theta>\<^sub>2 \<nu> x a)) = (\<lambda>x. Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a) + Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>2 \<nu> x a))"
    apply(rule ext)
    apply(rule blinfun_eqI)
    subgoal for x j
      using bound[of x] extendf_deriv_bounded[OF free1 good_interp] 
      extendf_deriv_bounded[OF free2 good_interp] 
      blinfun.add_left[of "Blinfun (extendf_deriv I i \<theta>\<^sub>1 \<nu> x)" "Blinfun (extendf_deriv I i \<theta>\<^sub>2 \<nu> x)"]
      bounded_linear_Blinfun_apply[of "(extendf_deriv I i \<theta>\<^sub>1 \<nu> x)"]
      bounded_linear_Blinfun_apply[of "(extendf_deriv I i \<theta>\<^sub>2 \<nu> x)"]
      by (simp add: bounded_linear_Blinfun_apply)
    done
  have "continuous_on UNIV (\<lambda>x. Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a) + Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>2 \<nu> x a))"
    apply(rule continuous_intros)
    using IH1 IH2 by auto
  then show ?case apply auto
    using eq by presburger
next
  case (5 \<theta>\<^sub>1)
  assume free1:"dfree \<theta>\<^sub>1"
  assume IH1:"continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i \<theta>\<^sub>1 \<nu> x))"
  have bound:"\<And>x. bounded_linear  (\<lambda>a. - extendf_deriv I i \<theta>\<^sub>1 \<nu> x a )"
    using extendf_deriv_bounded[OF free1 good_interp]
    by (simp add: bounded_linear_minus)
  have eq:"(\<lambda>x. Blinfun (\<lambda>a. - extendf_deriv I i \<theta>\<^sub>1 \<nu> x a )) = (\<lambda>x. - Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a) )"
    apply(rule ext)
    apply(rule blinfun_eqI)
    subgoal for x j
      using bound[of x] extendf_deriv_bounded[OF free1 good_interp] 
      bounded_linear_Blinfun_apply[of "(extendf_deriv I i \<theta>\<^sub>1 \<nu> x)"]
      using  bounded_linear_Blinfun_apply
      by (simp add: bounded_linear_Blinfun_apply uminus_blinfun.rep_eq)
    done
  have "continuous_on UNIV (\<lambda>x. - Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a) )"
    apply(rule continuous_intros)
    using IH1  by auto
  then show ?case
    apply simp
    using eq by presburger
next
  case (6 \<theta>\<^sub>1 \<theta>\<^sub>2)
  assume free1:"dfree \<theta>\<^sub>1"
  assume free2:"dfree \<theta>\<^sub>2"
  assume IH1:"continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i \<theta>\<^sub>1 \<nu> x))"
  assume IH2:"continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i \<theta>\<^sub>2 \<nu> x))"
  have bounded:"\<And>x. bounded_linear (\<lambda>a. dterm_sem (extendf I x) \<theta>\<^sub>1 \<nu> * extendf_deriv I i \<theta>\<^sub>2 \<nu> x a +
                       extendf_deriv I i \<theta>\<^sub>1 \<nu> x a * dterm_sem (extendf I x) \<theta>\<^sub>2 \<nu>)"
    using extendf_deriv_bounded[OF free1 good_interp] extendf_deriv_bounded[OF free2 good_interp]
    by (simp add: bounded_linear_add bounded_linear_const_mult bounded_linear_mult_const)
  have eq:"(\<lambda>x. Blinfun (\<lambda>a. dterm_sem (extendf I x) \<theta>\<^sub>1 \<nu> * extendf_deriv I i \<theta>\<^sub>2 \<nu> x a +
                       extendf_deriv I i \<theta>\<^sub>1 \<nu> x a * dterm_sem (extendf I x) \<theta>\<^sub>2 \<nu>)) = 
           (\<lambda>x. dterm_sem (extendf I x) \<theta>\<^sub>1 \<nu> *\<^sub>R Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>2 \<nu> x a) +
           dterm_sem (extendf I x) \<theta>\<^sub>2 \<nu> *\<^sub>R Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a))"
    apply(rule ext)
    apply(rule blinfun_eqI)
    subgoal for x j
      using extendf_deriv_bounded[OF free1 good_interp] extendf_deriv_bounded[OF free2 good_interp] bounded[of x]
      blinfun.scaleR_left 
      bounded_linear_Blinfun_apply[of "Blinfun (extendf_deriv I i \<theta>\<^sub>2 \<nu> x)"]
      bounded_linear_Blinfun_apply[of "Blinfun (extendf_deriv I i \<theta>\<^sub>1 \<nu> x)"]
      mult.commute 
      plus_blinfun.rep_eq[of "dterm_sem (extendf I x) \<theta>\<^sub>1 \<nu> *\<^sub>R Blinfun (extendf_deriv I i \<theta>\<^sub>2 \<nu> x)" "dterm_sem (extendf I x) \<theta>\<^sub>2 \<nu> *\<^sub>R Blinfun (extendf_deriv I i \<theta>\<^sub>1 \<nu> x)"]
      real_scaleR_def
      by (simp add: blinfun.scaleR_left bounded_linear_Blinfun_apply)
    done
  have "continuous_on UNIV (\<lambda>x. dterm_sem (extendf I x) \<theta>\<^sub>1 \<nu> *\<^sub>R Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>2 \<nu> x a) +
           dterm_sem (extendf I x) \<theta>\<^sub>2 \<nu> *\<^sub>R Blinfun (\<lambda>a. extendf_deriv I i \<theta>\<^sub>1 \<nu> x a))"
    apply(rule continuous_intros)+
      apply(rule extendf_dterm_sem_continuous[OF free1 good_interp])
     apply(rule IH2)
    apply(rule continuous_intros)+
     apply(rule extendf_dterm_sem_continuous[OF free2 good_interp])
    by(rule IH1)
  then show ?case
    unfolding extendf_deriv.simps
    using eq by presburger
qed (auto intro: continuous_intros)

lemma extendf_deriv:
  fixes f'::"trm" and I::"interp"
  assumes free:"dfree f'"
  assumes good_interp:"is_interp I"
  shows "\<exists>f''. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) f' \<nu>) has_derivative (extendf_deriv I i_f f' \<nu> x)) (at x)"
  using free proof (induction rule: dfree.induct)
  case (dfree_Fun f args) then have
    nb:"nonbase f"
    and l:"ilength f < MAX_STR"
    and dfrees:"\<And>j. dfree (args j)"
    and IHs:"\<And>j. (\<exists>f''. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) (args j) \<nu>) has_derivative extendf_deriv I i_f (args j) \<nu> x) (at x))"
    by auto
  obtain inj where some:"args_to_id f = Some inj" using nonbase_some[OF nb] by auto
  show ?case
  proof (cases inj)
    case (Inl a) then have inj:"inj = Inl a" and a:"args_to_id f = Some (Inl a)" using some by auto
    from IHs have IH1':"(\<And>ia. \<And>x. ((\<lambda>R. dterm_sem
                      \<lparr>Functions = \<lambda>f. case args_to_id f of Some (Inl x) \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> \<lambda>_. R $ f' | None \<Rightarrow> Functions I f, 
                      Funls = \<lambda>f. case args_to_id f of Some (Inl x) \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> \<lambda>_. R $ f' | None \<Rightarrow> Funls I f, Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                         ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                      (args ia) \<nu>) has_derivative
                  extendf_deriv I i_f (args ia) \<nu> x)
                (at x))" by auto
     have chain:"\<And>f f' x s g g'. (f has_derivative f') (at x within s) \<Longrightarrow>
      (g has_derivative g') (at (f x) within f ` s) \<Longrightarrow> (g \<circ> f has_derivative g' \<circ> f') (at x within s)"
       by (auto intro: derivative_intros)
     let ?f = "(\<lambda>x. Functions I f x)"
     let ?g = "(\<lambda> R. (\<chi> i. dterm_sem
                       \<lparr>Functions = \<lambda>f. case args_to_id f of Some (Inl x) \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> \<lambda>_. R $ f' | None \<Rightarrow> Functions I f, 
                        Funls = \<lambda>f. case args_to_id f of Some (Inl x) \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> \<lambda>_. R $ f' | None \<Rightarrow> Funls I f, 
                        Predicates = Predicates I, Contexts = Contexts I,
                          Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                       (args i) \<nu>))"
     let ?myf' = "(\<lambda>x. (THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y)) (?g x))"
     let ?myg' = "(\<lambda>x. (\<lambda>\<nu>'. \<chi> ia. extendf_deriv I i_f (args ia) \<nu> x \<nu>'))"
     have fg_eq:"(\<lambda>R. Functions I f
           (\<chi> i. dterm_sem
                  \<lparr>Functions = \<lambda>f. case args_to_id f of Some (Inl x) \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> \<lambda>_. R $ f' | None \<Rightarrow> Functions I f, 
                   Funls = \<lambda>f. case args_to_id f of Some (Inl x) \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> \<lambda>_. R $ f' | None \<Rightarrow> Funls I f, 
                   Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I,
                     ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
                  (args i) \<nu>)) = (?f \<circ> ?g)"
       by auto
     have "\<And>x. ((?f o ?g) has_derivative (?myf' x \<circ> ?myg' x)) (at x)"
       apply (rule diff_chain_at)
       subgoal for xa
         apply (rule has_derivative_vec)
         subgoal for i 
           using IH1'[of i xa] 
           by(auto)
         done
       subgoal for xa 
       proof -
         have deriv:"\<And>x. (Functions I f has_derivative FunctionFrechet I f x) (at x)"
         and cont:"continuous_on UNIV (\<lambda>x. Blinfun (FunctionFrechet I f x))"
           using good_interp[unfolded is_interp_def] by auto
         show ?thesis
           apply(rule has_derivative_at_withinI)
           using deriv by auto
       qed
      done
    then have "\<And>x. ((?f o ?g) has_derivative (?myf' x \<circ> ?myg' x)) (at x)" by auto
    then show "?thesis"
      apply(cases "inj")
      subgoal for aa
        apply(simp del: args_to_id.simps)
        using fg_eq a some  has_derivative_proj' by auto
      using some a by(auto)
  next
    case (Inr b) then have inj:"inj = Inr b" and a:"args_to_id f = Some (Inr b)" using some by auto
    from IHs have IH1':"(\<And>ia. \<And>x. ((\<lambda>R. dterm_sem (extendf I R) (args ia) \<nu>) has_derivative extendf_deriv I i_f (args ia) \<nu> x) (at x))"
      by auto
     have chain:"\<And>f f' x s g g'. (f has_derivative f') (at x within s) \<Longrightarrow>
      (g has_derivative g') (at (f x) within f ` s) \<Longrightarrow> (g \<circ> f has_derivative g' \<circ> f') (at x within s)"
       by (auto intro: derivative_intros)
     let ?f = "(\<lambda>x. Functions I f x)"
     let ?g = "(\<lambda> R. (\<chi> i. dterm_sem (extendf I R) (args i) \<nu>))"
     let ?myf' = "(\<lambda>x. (THE f'. \<forall>y. (Functions I f has_derivative f' y) (at y)) (?g x))"
     let ?myg' = "(\<lambda>x. (\<lambda>\<nu>'. \<chi> ia. extendf_deriv I i_f (args ia) \<nu> x \<nu>'))"
     have fg_eq:"(\<lambda>R. Functions I f (\<chi> i. dterm_sem (extendf I R)(args i) \<nu>)) = (?f \<circ> ?g)"
       by auto
     have "\<And>x. ((?f o ?g) has_derivative (?myf' x \<circ> ?myg' x)) (at x)"
       apply (rule diff_chain_at)
       subgoal for xa
         apply (rule has_derivative_vec)
         subgoal for i 
           using IH1'[of i xa] by auto
         done
       subgoal for xa 
       proof -
         have deriv:"\<And>x. (Functions I f has_derivative FunctionFrechet I f x) (at x)"
         and cont:"continuous_on UNIV (\<lambda>x. Blinfun (FunctionFrechet I f x))"
           using good_interp[unfolded is_interp_def] by auto
         show ?thesis
           apply(rule has_derivative_at_withinI)
           using deriv some a by auto
       qed
      done
    then have der:"\<And>x. ((?f o ?g) has_derivative (?myf' x \<circ> ?myg' x)) (at x)" by auto
    show "?thesis"
      using fg_eq a der  has_derivative_proj' by auto
  qed
next
  case (dfree_Times  \<theta>1 \<theta>2)
  then have df1:"dfree \<theta>1" and df2:"dfree \<theta>2"
    and IH1:"\<exists>f''. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) \<theta>1 \<nu>) has_derivative extendf_deriv I i_f \<theta>1 \<nu> x) (at x)"
    and IH2:"\<exists>f''. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) \<theta>2 \<nu>) has_derivative extendf_deriv I i_f \<theta>2 \<nu> x) (at x)" by auto
  from IH1 have ed1:"\<And>x. ((\<lambda>R. dterm_sem (extendf I R) \<theta>1 \<nu>) has_derivative extendf_deriv I i_f \<theta>1 \<nu> x) (at x)"
    by(auto)
  from IH2 have ed2:"\<And>x. ((\<lambda>R. dterm_sem (extendf I R) \<theta>2 \<nu>) has_derivative extendf_deriv I i_f \<theta>2 \<nu> x) (at x)"
    by(auto)
  show ?case using has_derivative_mult[OF ed1 ed2] by(auto)
qed (auto)


lemma ODE_vars_sub_BVO_inl:
  assumes good_interp:"is_interp I"
  shows "Inl ` ODE_vars I a \<subseteq> BVO a"
  apply(induction a,auto)
  subgoal for x1 x2 xa
    apply(cases x2,auto)
    using good_interp unfolding is_interp_def by auto done

lemma ODE_vars_sub_BVO_inr:
  assumes good_interp:"is_interp I"
  shows "Inr ` ODE_vars I a \<subseteq> BVO a"
  apply(induction a,auto)
  subgoal for x1 x2 xa
    apply(cases x2,auto)
    using good_interp unfolding is_interp_def by auto done

lemma extendf_safe:
  fixes I::"interp"
  assumes good_interp:"is_interp I"
  shows "is_interp (extendf I R)"
proof (auto simp add: is_interp_def simp del: args_to_id.simps)
  fix x::"Rvec" and   i::"ident"
  have the_eq:"\<And>b.  (THE f'. \<forall>x. ((\<lambda>_. R $ b) has_derivative f' x) (at x)) = (\<lambda>_ _. 0)"
    apply(rule the_all_deriv)
    by (auto intro: derivative_eq_intros) 
  have has_der:"\<And>b.  ((\<lambda>_. R $ b) has_derivative (\<lambda>_. 0)) (at x)"
    by (auto intro: derivative_eq_intros)
(*  obtain inj where some:"args_to_id i = Some inj" 
    using nonbase_some by auto*)
  show "((case args_to_id i of Some (Inl xa) \<Rightarrow> Functions I i | Some (Inr f') \<Rightarrow> \<lambda>_. R $ f' | None \<Rightarrow> Functions I i) has_derivative
            (THE f'. \<forall>x. ((case args_to_id i of Some (Inl xa) \<Rightarrow> Functions I i | Some (Inr f') \<Rightarrow> \<lambda>_. R $ f' | None \<Rightarrow> Functions I i) has_derivative f' x) (at x))
             x)
            (at x)"
    apply(cases "ident_expose i",auto) 
    using is_interpD[OF good_interp] apply (auto intro: derivative_eq_intros)
    subgoal for b unfolding SSENT_def SSENTINEL_def FSENT_def FSENTINEL_def by auto
    subgoal for b
    proof -
        let ?f = " (\<lambda> _ . R $ b)"
        let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
        let ?f''="(\<lambda>_ _. 0)"
        have Pf:"?Pred ?f'' "
(*          using extendf_deriv[OF good_subst[of i f'] good_interp, of \<nu> i, OF some]*)
          by auto
        have onePf:"((\<lambda>_. R $ b) has_derivative (\<lambda>_. 0)) (at x)" using Pf by auto
        have pre_eq:"\<And>x. (THE G. (?f has_derivative G) (at x)) = ?f'' x"
          apply(rule the_deriv)
          using Pf by auto
        have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
          apply(rule the_all_deriv)
          using Pf the_all_deriv by auto
         have the_eq_app:"(THE G. \<forall>x. ((\<lambda>_. R $ b) has_derivative G x) (at x)) x = (\<lambda>_ . 0)"
           using the_eq by (auto simp add: fun_eq_iff)
         show "((\<lambda>_. R $ b) has_derivative (THE G. \<forall>x. ((\<lambda>_. R $ b) has_derivative G x) (at x)) x) (at x)"
          using Pf the_eq the_eq_app pre_eq onePf by auto
      qed
      done
  next
    fix i
    show "continuous_on UNIV(\<lambda>x. Blinfun ((THE f'. \<forall>x. ((case args_to_id i of None \<Rightarrow> Functions I i | Some (Inl xa) \<Rightarrow> Functions I i  | Some (Inr f') \<Rightarrow> \<lambda>_. R $ f') has_derivative f' x) (at x)) x))"
      apply(cases "ident_expose i",auto)
(*      apply(cases "args_to_id i",auto)*)
      subgoal using good_interp unfolding is_interp_def by auto
      subgoal for b
    proof -
        let ?f = " (\<lambda> _ . R $ b)"
        let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
        let ?f''="(\<lambda>_ _. 0)"
        have Pf:"?Pred ?f'' "
(*          using extendf_deriv[OF good_subst[of i f'] good_interp, of \<nu> i, OF some]*)
          by auto
        have onePf:"\<And>x. ((\<lambda>_. R $ b) has_derivative (\<lambda>_. 0)) (at x)" using Pf by auto
        have pre_eq:"\<And>x. (THE G. (?f has_derivative G) (at x)) = ?f'' x"
          apply(rule the_deriv)
          using Pf by auto
        have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
          apply(rule the_all_deriv)
          using Pf the_all_deriv by auto
         have the_eq_app:"\<And>x. (THE G. \<forall>x. ((\<lambda>_. R $ b) has_derivative G x) (at x)) x = (\<lambda>_ . 0)"
           using the_eq by (auto simp add: fun_eq_iff)
         have zero_eq:"blinfun_apply (Blinfun (\<lambda>_. 0))  = (\<lambda>_. 0) "
           apply(rule bounded_linear_Blinfun_apply)
           by (rule bounded_linear_zero)
         have blineq:"(\<lambda>x. Blinfun ((THE f'. \<forall>x. ((\<lambda>_. R $ b) has_derivative f' x) (at x)) x)) = (\<lambda>x. Blinfun (\<lambda>_ . 0))"
           apply(rule ext)
           apply(rule blinfun_eqI)
           apply(subst bounded_linear_Blinfun_apply)
           subgoal for x i using Pf the_eq the_eq_app[of x] pre_eq[of x] onePf[of x] by auto
           subgoal for x i using Pf the_eq the_eq_app[of x] pre_eq[of x] onePf[of x] zero_eq by(auto simp add: fun_eq_iff)
           done
         have conZ:"continuous_on UNIV (\<lambda>x. Blinfun (\<lambda>_ . 0))"
           by(rule continuous_on_const)
         show "continuous_on UNIV (\<lambda>x. Blinfun ((THE f'. \<forall>x. ((\<lambda>_. R $ b) has_derivative f' x) (at x)) x))"
           using blineq conZ  
          by (metis (mono_tags, lifting) continuous_on_cong)
      qed
      using good_interp unfolding is_interp_def SSENT_def SSENTINEL_def FSENT_def FSENTINEL_def apply auto
      subgoal for b
    proof -
        let ?f = " (\<lambda> _ . R $ b)"
        let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
        let ?f''="(\<lambda>_ _. 0)"
        have Pf:"?Pred ?f'' "
(*          using extendf_deriv[OF good_subst[of i f'] good_interp, of \<nu> i, OF some]*)
          by auto
        have onePf:"\<And>x. ((\<lambda>_. R $ b) has_derivative (\<lambda>_. 0)) (at x)" using Pf by auto
        have pre_eq:"\<And>x. (THE G. (?f has_derivative G) (at x)) = ?f'' x"
          apply(rule the_deriv)
          using Pf by auto
        have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
          apply(rule the_all_deriv)
          using Pf the_all_deriv by auto
         have the_eq_app:"\<And>x. (THE G. \<forall>x. ((\<lambda>_. R $ b) has_derivative G x) (at x)) x = (\<lambda>_ . 0)"
           using the_eq by (auto simp add: fun_eq_iff)
         have zero_eq:"blinfun_apply (Blinfun (\<lambda>_. 0))  = (\<lambda>_. 0) "
           apply(rule bounded_linear_Blinfun_apply)
           by (rule bounded_linear_zero)
         have blineq:"(\<lambda>x. Blinfun ((THE f'. \<forall>x. ((\<lambda>_. R $ b) has_derivative f' x) (at x)) x)) = (\<lambda>x. Blinfun (\<lambda>_ . 0))"
           apply(rule ext)
           apply(rule blinfun_eqI)
           apply(subst bounded_linear_Blinfun_apply)
           subgoal for x i using Pf the_eq the_eq_app[of x] pre_eq[of x] onePf[of x] by auto
           subgoal for x i using Pf the_eq the_eq_app[of x] pre_eq[of x] onePf[of x] zero_eq by(auto simp add: fun_eq_iff)
           done
         have conZ:"continuous_on UNIV (\<lambda>x. Blinfun (\<lambda>_ . 0))"
           by(rule continuous_on_const)
         show "continuous_on UNIV (\<lambda>x. Blinfun ((THE f'. \<forall>x. ((\<lambda>_. R $ b) has_derivative f' x) (at x)) x))"
           using blineq conZ  
          by (metis (mono_tags, lifting) continuous_on_cong)
      qed
      done
  next
    fix ode x
    assume elem:"x \<in> ODEBV I ode (Some x)"
    show False
      using elem good_interp unfolding is_interp_def by auto
  qed

lemma adjoint_safe:
  assumes good_interp:"is_interp I"
  assumes good_subst:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') "    
  assumes good_ode:"(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"    
  shows "is_interp (adjoint I \<sigma> \<nu>)"
  apply(unfold adjoint_def)
  apply(unfold is_interp_def)
  apply(auto simp del: extendf.simps extendc.simps FunctionFrechet.simps)
   subgoal for x i
     apply(cases "SFunctions \<sigma> i = None")
      subgoal
        apply(auto simp del: extendf.simps extendc.simps)
        using good_interp unfolding is_interp_def by simp
      apply(auto  simp del: extendf.simps extendc.simps)
      subgoal for f'
        using good_subst[of i f'] apply (auto  simp del: extendf.simps extendc.simps)
      proof -
        assume some:"SFunctions \<sigma> i = Some f'"
        assume free:"dfree f'"
        let ?f = "(\<lambda>R. dterm_sem (extendf I R) f' \<nu>)"
        let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
        let ?f''="extendf_deriv I i f' \<nu>"
        have Pf:"?Pred ?f''"
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
    subgoal for i
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
        let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
        let ?f''="extendf_deriv I i f' \<nu>"
        have Pf:"?Pred ?f''"
          using extendf_deriv[OF good_subst[of i f'] good_interp, of \<nu> i, OF some]
          by auto
        have "\<And>x. (THE G. (?f has_derivative G) (at x)) = ?f'' x"
          apply(rule the_deriv)
          using Pf by auto
        then have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
          using Pf the_all_deriv by auto
        have "continuous_on UNIV (\<lambda>x. Blinfun (?f'' x))"
          by(rule extendf_deriv_continuous[OF free good_interp])
        show "continuous_on UNIV (\<lambda>x. Blinfun ((THE f'a. \<forall>x. ((\<lambda>R. dterm_sem (extendf I R) f' \<nu>
) has_derivative f'a x) (at x)) x))"
          using the_eq Pf 
          by (simp add: \<open>continuous_on UNIV (\<lambda>x. Blinfun (extendf_deriv I i f' \<nu> x))\<close>)
      qed
      done 
    subgoal for ode x apply(cases " SODEs \<sigma> ode (Some x)",auto)
      subgoal using good_interp unfolding is_interp_def by auto
      subgoal for ODE
      using good_ode[of ode x ODE] ODE_vars_sub_BVO_inl[OF good_interp, of ODE] by auto
    done 
  done
lemma adjointFO_safe:
  assumes good_interp:"is_interp I"
  assumes good_subst:"(\<And>i. dsafe (\<sigma> i))"
  shows "is_interp (adjointFO I \<sigma> \<nu>)"
  apply(unfold adjointFO_def)
  apply(unfold is_interp_def)
  apply(auto simp del: extendf.simps extendc.simps FunctionFrechet.simps args_to_id.simps)
   subgoal for x i
     apply(cases "args_to_id i")
      subgoal
        apply(auto  simp del: extendf.simps extendc.simps)
        using good_interp unfolding is_interp_def 
        by(auto  simp del: extendf.simps extendc.simps)
      subgoal for a
      apply(cases a)
     subgoal for f'
     proof (simp del: args_to_id.simps)
       assume some:"args_to_id i = Some (Inl f')" 
       have free:"dsafe (\<sigma> f')" using good_subst by auto
       let ?f = "(\<lambda>_. dterm_sem I (\<sigma> f') \<nu>)"
       let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
       let ?f''="(\<lambda>_ _. 0)"
       have Pf:"?Pred ?f''"
       proof (induction "\<sigma> f'")
       qed (auto)
       have "(THE G. (?f has_derivative G) (at x)) = ?f'' x"
         apply(rule the_deriv)
         using Pf by auto
       then have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
         using Pf the_all_deriv[of ?f ?f''] by auto
       have another_eq:"(THE f'a. \<forall>x. ((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative f'a x) (at x)) x = (\<lambda> _. 0)"
         using Pf by (simp add: the_eq) 
       then show "(Functions I i has_derivative (THE f'a. \<forall>x. (Functions I i has_derivative f'a x) (at x)) x) (at x)"
         using the_eq Pf 
       proof -
         have "\<forall>v i. (\<lambda>ia. case args_to_id ia of Some(Inl x) \<Rightarrow> Functions i ia | Some(Inr i) \<Rightarrow> \<lambda>va. v $ i | None \<Rightarrow> Functions i ia) = Functions (extendf i v)"
           by simp
         then show ?thesis
           using UNIV_I extendf.simps extendf_safe good_interp is_interpD vec_lambda_inverse by simp
       qed
     qed
    proof (simp del: args_to_id.simps)
      fix f'
      assume some:"args_to_id i = Some (Inr f')"
      have free:"dsafe (\<sigma> f')" using good_subst by auto
      let ?f = "(\<lambda>R. dterm_sem I (\<sigma> f') \<nu>)"
      let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
      let ?f''="(\<lambda>_ _. 0)" (* *)
      have Pf:"?Pred ?f''" by simp
      have "\<And>x. (THE G. (?f has_derivative G) (at x)) = ?f'' x"
        apply(rule the_deriv)
        using Pf by auto
      then have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
        using Pf the_all_deriv[of "(\<lambda>R. dterm_sem I (\<sigma> f') \<nu>)" "(\<lambda>_ _. 0)"]
        by blast
      then have blin_cont:"continuous_on UNIV (\<lambda>x.  (?f'' x))"
        by (simp add: continuous_on_const)
      have truth:"(\<lambda>x.  ((THE f'a. \<forall>x. ((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative f'a x) (at x)) x))
        = (\<lambda>x.  (\<lambda> _. 0))"
        apply(rule ext)
        by (simp add: local.the_eq)
      then show "((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative (THE f'a. \<forall>x. ((\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) has_derivative f'a x) (at x)) x) (at x)"
        using truth blin_cont continuous_on_eq
        by (simp add: truth)
      qed
      done
    subgoal for f'
      apply(cases "args_to_id f'")
       apply(auto)
      apply(cases "ident_expose f'")
        apply(auto)
      using good_interp is_interp_def apply auto[1]
      subgoal for a b
        apply(cases "a = FSENT")
        using good_interp is_interp_def by auto
      subgoal for g'
      apply(cases "ident_expose f'")
         apply(auto)
        subgoal for a b
          apply(cases "a = FSENT")
           apply(auto)
          subgoal
            proof -
            let ?f = "(\<lambda>R. dterm_sem I (\<sigma> b) \<nu>)"
            let ?Pred = "(\<lambda>fd. (\<forall>x. (?f has_derivative (fd x)) (at x)))"
            let ?f''="(\<lambda>_ _. 0)" (* *)
            have Pf:"?Pred ?f''" by simp
            have "\<And>x. (THE G. (?f has_derivative G) (at x)) = ?f'' x"
              apply(rule the_deriv)
              using Pf by auto
            then have the_eq:"(THE G. \<forall> x. (?f has_derivative G x) (at x)) = ?f''"
              using Pf the_all_deriv[of "(\<lambda>R. dterm_sem I (\<sigma> b) \<nu>)" "(\<lambda>_ _. 0)"]
              by blast
            then have blin_cont:"continuous_on UNIV (\<lambda>x. Blinfun (?f'' x))"
              by (simp add: continuous_on_const)
            then have it_cont:"continuous_on UNIV ((THE G. \<forall> x. (?f has_derivative G x) (at x)))"
              by (simp add: local.the_eq)
            then show "continuous_on UNIV (\<lambda>x. Blinfun ((THE f'. \<forall>x. ((\<lambda>_. dterm_sem I (\<sigma> b) \<nu>) has_derivative f' x) (at x)) x))" 
              by (metis (mono_tags) continuous_on_const continuous_on_eq has_derivative_const the_all_deriv)
          qed

          apply(cases "a = SSENT") apply (auto simp add: SSENT_def SSENTINEL_def FSENT_def FSENTINEL_def)
              using good_interp is_interp_def by auto
        done
      done
    using good_interp is_interp_def by auto

subsection \<open>Lemmas about adjoint interpretations\<close>
lemma adjoint_consequence:
  shows "(\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f') \<Longrightarrow> 
 (\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f') \<Longrightarrow> 
 (\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f') \<Longrightarrow> 
  Vagree \<nu> \<omega> (FVS \<sigma>) \<Longrightarrow> 
          is_interp I \<Longrightarrow> adjoint I \<sigma> \<nu> = adjoint I \<sigma> \<omega>"
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
        assume safesF:"(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
        assume agrees:"Vagree \<nu> \<omega> (\<Union>x. SFV \<sigma> x)"
        assume some:"SFunctions \<sigma> xa = Some a"
        from safes some have safe:"dsafe a" by auto
        have sub:"SFV \<sigma> (Inl xa) \<subseteq> (\<Union>x. SFV \<sigma> x)"
          by blast
        from agrees 
        have "Vagree \<nu> \<omega> (SFV \<sigma> (Inl xa))"
          using agree_sub[OF sub agrees] by auto
        then have agree:"Vagree \<nu> \<omega> (FVT a)"
          using some by (auto simp add: Vagree_def)
        show "?thesis"
          using coincidence_dterm[of a, OF safes[of xa a, OF some] agree] by auto
      qed
      done
(*
  subgoal for xa xaa 
      apply(cases "SFunls \<sigma> xa")
       apply(auto)
      subgoal for a 
      proof -
        assume safes:"(\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
        assume safesF:"(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
        assume agrees:"Vagree \<nu> \<omega> (\<Union>x. SFV \<sigma> x)"
        assume some:"SFunls \<sigma> xa = Some a"
        from safesF some have safe:"dsafe a" by auto
        have sub:"SFV \<sigma> (Inl xa) \<subseteq> (\<Union>x. SFV \<sigma> x)"
          by blast
        from agrees 
        have "Vagree \<nu> \<omega> (SFV \<sigma> (Inl xa))"
          using agree_sub[OF sub agrees] by auto
        then have agree:"Vagree \<nu> \<omega> (FVT a)"
          using some by (simp add: Vagree_def)
        show "?thesis"
          using coincidence_dterm[of a, OF safesF[of xa a, OF some] agree] by auto
      qed
      done*)
    subgoal for xa  xaa
    apply(cases "SPredicates \<sigma> xa")
     apply(auto)
    subgoal for a 
    proof -
      assume good_interp:"is_interp I"
      assume safes:"(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      assume agrees:"Vagree \<nu> \<omega> (\<Union>x. SFV \<sigma> x)"
      assume some:"SPredicates \<sigma> xa = Some a"
      assume sem:"\<nu> \<in> fml_sem
          \<lparr>Functions =
             \<lambda>f. case case ident_expose f of Inl x \<Rightarrow> Map.empty x
                      | Inr (xa, xs) \<Rightarrow> if xa = FSENT then Some (Inr xs) else if xa = SSENT then Some (Inl xs) else None of
                 None \<Rightarrow> Functions I f | Some (Inl xa) \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> \<lambda>_. xaa $ f',
             Funls =
               \<lambda>f. case case ident_expose f of Inl x \<Rightarrow> Map.empty x
                        | Inr (xa, xs) \<Rightarrow> if xa = FSENT then Some (Inr xs) else if xa = SSENT then Some (Inl xs) else None of
                   None \<Rightarrow> Funls I f | Some (Inl xa) \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> \<lambda>_. xaa $ f',
             Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr> a"
      from safes some have safe:"fsafe a" by auto
      have sub:"SFV \<sigma> (Inr (Inr xa)) \<subseteq> (\<Union>x. SFV \<sigma> x)"
        by blast
      from agrees 
      have "Vagree \<nu> \<omega> (SFV \<sigma> (Inr (Inr xa)))"
        using agree_sub[OF sub agrees] by auto
      then have agree:"Vagree \<nu> \<omega> (FVF a)"
        using some by auto
      let ?I' = "\<lparr>Functions = \<lambda>f. case args_to_id f of None \<Rightarrow> Functions I f | Some (Inl xa) \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> \<lambda>_. xaa $ f',
        Funls = \<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl xa) \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> \<lambda>_. xaa $ f',
        Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>"
      have good_interp':"is_interp ?I'"  using extendf_safe[OF good_interp, of xaa] by (auto simp del: args_to_id.simps)
      have IA:"\<And>S. Iagree ?I' ?I' (SIGF a)" using Iagree_refl by auto 
      show "?thesis"
        using coincidence_formula[of a, OF safes[of xa a, OF some], OF good_interp' good_interp'] IA agree sem by auto
    qed
    done
   subgoal for xa xaa 
    apply(cases "SPredicates \<sigma> xa")
     apply(auto)
    subgoal for a 
    proof -
      assume good_interp:"is_interp I"
      assume safes:"(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      assume agrees:"Vagree \<nu> \<omega> (\<Union> (range (SFV \<sigma>)))"
      assume some:"SPredicates \<sigma> xa = Some a"
      assume sem:"\<omega> \<in> fml_sem \<lparr>Functions =
             \<lambda>f. case case ident_expose f of Inl x \<Rightarrow> Map.empty x
                      | Inr (xa, xs) \<Rightarrow> if xa = FSENT then Some (Inr xs) else if xa = SSENT then Some (Inl xs) else None of
                 None \<Rightarrow> Functions I f | Some (Inl xa) \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> \<lambda>_. xaa $ f',
             Funls =
               \<lambda>f. case case ident_expose f of Inl x \<Rightarrow> Map.empty x
                        | Inr (xa, xs) \<Rightarrow> if xa = FSENT then Some (Inr xs) else if xa = SSENT then Some (Inl xs) else None of
                   None \<Rightarrow> Funls I f | Some (Inl f') \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> \<lambda>_. xaa $ f',
             Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr> a
        "
      from safes some have safe:"fsafe a" by auto
      have sub:"SFV \<sigma> (Inr (Inr xa)) \<subseteq> (\<Union>x. SFV \<sigma> x)"
        by blast
      from agrees 
      have "Vagree \<nu> \<omega> (SFV \<sigma> (Inr (Inr xa)))"
        using agree_sub[OF sub agrees] by auto
      then have agree:"Vagree \<nu> \<omega> (FVF a)"
        using some by auto
      let ?I' = "\<lparr>Functions =
             \<lambda>f. case case ident_expose f of Inl x \<Rightarrow> Map.empty x
                      | Inr (xa, xs) \<Rightarrow> if xa = FSENT then Some (Inr xs) else if xa = SSENT then Some (Inl xs) else None of
                 None \<Rightarrow> Functions I f | Some (Inl xa) \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> \<lambda>_. xaa $ f',
             Funls =
               \<lambda>f. case case ident_expose f of Inl x \<Rightarrow> Map.empty x
                        | Inr (xa, xs) \<Rightarrow> if xa = FSENT then Some (Inr xs) else if xa = SSENT then Some (Inl xs) else None of
                   None \<Rightarrow> Funls I f | Some (Inl xa) \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> \<lambda>_. xaa $ f',
             Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>"
      have IA:"\<And>S. Iagree ?I' ?I' (SIGF a)" using Iagree_refl by auto
      have good_interp':"is_interp ?I'" using good_interp using extendf_safe by auto
      show "?thesis"
        using coincidence_formula[of a, OF safes[of xa a, OF some]  good_interp' good_interp' IA agree] sem by auto
    qed
  done    
done

definition SigSet where
 "SigSet = (\<lambda>\<sigma> t1. (\<Union>i\<in>SIGT t1. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}))"
(* \<union> (\<Union>i\<in>SIGT t1. case SFunls \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})*)
definition OSigSet where
 "OSigSet = (\<lambda>\<sigma> ODE. (\<Union>i\<in>{ l | l. Inl l \<in>(SIGO ODE)}. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})
 )"

(*\<union> (\<Union>i\<in>{l | l. Inl l \<in>(SIGO ODE)} . case SFunls \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})  *)

lemma SIGT_plus1:"Vagree \<nu> \<omega> (SigSet \<sigma> (Plus t1 t2)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t1)"
  unfolding Vagree_def SigSet_def by auto

lemma SIGT_plus2:"Vagree \<nu> \<omega> (SigSet \<sigma> (Plus t1 t2)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t2)"
  unfolding Vagree_def SigSet_def by auto

lemma SIGT_neg:"Vagree \<nu> \<omega> (SigSet \<sigma> (Neg t1)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t1)"
  unfolding Vagree_def SigSet_def by auto

lemma SIGT_times1:"Vagree \<nu> \<omega> (SigSet \<sigma> (Times t1 t2)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t1)"
  unfolding Vagree_def SigSet_def by auto

lemma SIGT_times2:"Vagree \<nu> \<omega> (SigSet \<sigma> (Times t1 t2)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t2)"
  unfolding Vagree_def SigSet_def by auto


lemma SIGT_max1:"Vagree \<nu> \<omega> (SigSet \<sigma>(Max t1 t2)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t1)"
  unfolding Vagree_def SigSet_def by auto

lemma SIGT_max2:"Vagree \<nu> \<omega> (SigSet \<sigma> (Max t1 t2)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t2)"
  unfolding Vagree_def SigSet_def by auto

lemma SIGT_div1:"Vagree \<nu> \<omega> (SigSet \<sigma>(Div t1 t2)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t1)"
  unfolding Vagree_def SigSet_def by auto

lemma SIGT_div2:"Vagree \<nu> \<omega> (SigSet \<sigma>(Div t1 t2)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t2)"
  unfolding Vagree_def SigSet_def by auto

lemma SIGT_min1:"Vagree \<nu> \<omega> (SigSet \<sigma>(Min t1 t2)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t1)"
  unfolding Vagree_def SigSet_def by auto

lemma SIGT_min2:"Vagree \<nu> \<omega> (SigSet \<sigma> (Min t1 t2)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t2)"
  unfolding Vagree_def SigSet_def by auto

lemma SIGT_abs:"Vagree \<nu> \<omega> (SigSet \<sigma>(Abs t1)) \<Longrightarrow> Vagree \<nu> \<omega> (SigSet \<sigma> t1)"
  unfolding Vagree_def SigSet_def by auto

lemma uadmit_sterm_adjoint':
(* ((\<Union>i\<in>SIGT \<theta>. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})\<union>(\<Union>i\<in>SIGT \<theta>. case SFunls \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}))*)
  assumes dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f'"
  shows  "Vagree \<nu> \<omega> (SigSet \<sigma> \<theta>) \<Longrightarrow> 
    sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  let ?Set = "SigSet \<sigma>"
(*(\<lambda> t. ((\<Union>i\<in>SIGT t. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})\<union>(\<Union>i\<in>SIGT t. case SFunls \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {})))"*)
  case (Plus \<theta>1 \<theta>2)
  assume IH1:"Vagree \<nu> \<omega> (?Set \<theta>1) \<Longrightarrow> sterm_sem (adjoint I \<sigma> \<nu>) \<theta>1 = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>1"
  assume IH2:"Vagree \<nu> \<omega> (?Set \<theta>2) \<Longrightarrow> sterm_sem (adjoint I \<sigma> \<nu>) \<theta>2 = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (?Set (Plus \<theta>1 \<theta>2))"
  then show ?case
    using IH1[OF SIGT_plus1[OF VA]] IH2[OF SIGT_plus2[OF VA]] by auto
next
  let ?Set = "SigSet \<sigma>"
  case (Times \<theta>1 \<theta>2)
  assume IH1:"Vagree \<nu> \<omega> (?Set \<theta>1) \<Longrightarrow> sterm_sem (adjoint I \<sigma> \<nu>) \<theta>1 = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>1"
  assume IH2:"Vagree \<nu> \<omega> (?Set \<theta>2) \<Longrightarrow> sterm_sem (adjoint I \<sigma> \<nu>) \<theta>2 = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (?Set (Times \<theta>1 \<theta>2))"    
  then show ?case
    using IH1[OF SIGT_times1[OF VA]] IH2[OF SIGT_times2[OF VA]] by auto
next
  let ?Set = "SigSet \<sigma>"
  case (Neg t)
  assume IH1:"Vagree \<nu> \<omega> (?Set t) \<Longrightarrow> sterm_sem (adjoint I \<sigma> \<nu>) t = sterm_sem (adjoint I \<sigma> \<omega>) t"
  assume VA:"Vagree \<nu> \<omega> (?Set (Neg t))"    
  then show ?case
    using IH1[OF SIGT_neg[OF VA]]  by auto
next
  let ?Set = "SigSet \<sigma>"
  case (Function x1a x2a)
  assume IH:"\<And>x. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (?Set x) \<Longrightarrow>
    sterm_sem (adjoint I \<sigma> \<nu>) x = sterm_sem (adjoint I \<sigma> \<omega>) x"
  from IH have IH':"\<And>j. Vagree \<nu> \<omega> (?Set (x2a j)) \<Longrightarrow>
    sterm_sem (adjoint I \<sigma> \<nu>) (x2a j) = sterm_sem (adjoint I \<sigma> \<omega>) (x2a j)"
    using rangeI by auto
  assume VA:"Vagree \<nu> \<omega> (?Set ($f x1a x2a))"
  from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (?Set(x2a j))"
    unfolding Vagree_def SIGT.simps SigSet_def  using rangeI SigSet_def
    apply(auto)
    by blast+
  have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
  have VAsub:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> (FVT a) \<subseteq> (?Set ($f x1a x2a))"
    using SIGT unfolding SigSet_def by(auto)
  have VAf:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a)"
    using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "SFunctions \<sigma> x1a")
     defer
     subgoal for x a
     proof -
       assume VA:"(\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a))"
       assume sems:"(\<And>j. \<forall>x. sterm_sem (adjoint I \<sigma> \<nu>) (x2a j) x = sterm_sem (adjoint I \<sigma> \<omega>) (x2a j) x)"
       assume some:"SFunctions \<sigma> x1a = Some a"
       note FVT = VAf[OF some]
       have dsem:"\<And>R . dterm_sem (extendf I R) a \<nu> = dterm_sem (extendf I R) a \<omega>"
         using coincidence_dterm[OF dsafe[OF some] FVT] by auto
       have "\<And>R. Functions (adjoint I \<sigma> \<nu>) x1a R = Functions (adjoint I \<sigma> \<omega>) x1a R"
         using dsem some unfolding adjoint_def by auto
       then show "Functions (adjoint I \<sigma> \<nu>) x1a (\<chi> i. sterm_sem (adjoint I \<sigma> \<omega>) (x2a i) x) =
                 Functions (adjoint I \<sigma> \<omega>) x1a (\<chi> i. sterm_sem (adjoint I \<sigma> \<omega>) (x2a i) x)"
         by auto
     qed
    unfolding adjoint_def apply auto    
    done
qed (auto)  

lemma arg_rebaseL:
  assumes nb:"nonbase f"
  assumes ai:"args_to_id f = Some (Inl a)"
  shows "rebase f = a"
proof -
  from nb have ne:"f \<noteq> ident_empty"
    using nonbase_nonemp by auto
  have c1: "ident_expose f = Inl () \<Longrightarrow> False"
    using ne apply (auto simp add: ident_expose_def ident_empty_def)
    apply(cases "string_expose (Rep_ident f)")
     apply(auto)
    apply(cases "(Rep_ident f)")
     apply(auto)
    by (metis Rep_ident_inverse)
  have c2:"\<And> c cs. ident_expose f = Inr (c,cs) \<Longrightarrow> cs = a"
    using ai apply(auto)
    subgoal for c cs
    apply(cases "c = FSENT") apply(auto)
      apply(cases "c = SSENT") by(auto)
    done      
  show ?thesis
    apply auto
    apply(cases "ident_expose f")
    subgoal  using c1 by auto
    using c2  by auto
qed

lemma arg_rebaseR:
  assumes nb:"nonbase f"
  assumes ai:"args_to_id f = Some (Inr a)"
  shows "rebase f = a"
proof -
  from nb have ne:"f \<noteq> ident_empty"
    using nonbase_nonemp by auto
  have c1: "ident_expose f = Inl () \<Longrightarrow> False"
    using ne apply (auto simp add: ident_expose_def ident_empty_def)
    apply(cases "string_expose (Rep_ident f)")
     apply(auto)
    apply(cases "(Rep_ident f)")
     apply(auto)
    by (metis Rep_ident_inverse)
  have c2:"\<And> c cs. ident_expose f = Inr (c,cs) \<Longrightarrow> cs = a"
    using ai apply(auto)
    subgoal for c cs
    apply(cases "c = FSENT") apply(auto)
      apply(cases "c = SSENT") by(auto)
    done      
  show ?thesis
    apply auto
    apply(cases "ident_expose f")
    subgoal  using c1 by auto
    using c2  by auto
qed


(* Not used, but good practice for dterm adjoint *)
lemma uadmit_sterm_adjoint:
  assumes TUA:"TUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f'"
  assumes Fsafe:"\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
  shows  "sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof -
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have "\<And>x. x \<in> (SigSet \<sigma> \<theta>) \<Longrightarrow> x \<in> (-U)"
    using TUA unfolding TUadmit_def SigSet_def by auto
  then have sub1:"(SigSet \<sigma> \<theta>) \<subseteq> -U"
    by auto
  then have VA':"Vagree \<nu> \<omega> (SigSet \<sigma> \<theta>)"
    using agree_sub[OF sub1 VA] unfolding SigSet_def by auto
  then show "?thesis" using uadmit_sterm_adjoint'[OF dsafe fsafe VA'] by auto
qed

lemma uadmit_sterm_ntadjoint':
  assumes dsafe:"\<And>i. dsafe (\<sigma> i)"
(*  assumes safet:"dsafe \<theta>"*)
  shows  "dsafe \<theta> \<Longrightarrow> Vagree \<nu> \<omega> ((\<Union> i\<in>{i. debase i \<in> SIGT \<theta>}. FVT (\<sigma> i))) \<Longrightarrow> sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  case (Neg \<theta>1)
  assume IH1:"dsafe \<theta>1 \<Longrightarrow> Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume safet:"dsafe (Neg \<theta>1)"
  assume VA:"Vagree \<nu> \<omega> ((\<Union> i\<in>{i. debase i \<in> SIGT (Neg \<theta>1)}. FVT (\<sigma> i)))"
  from VA 
    have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"unfolding Vagree_def by auto
  then show ?case
    using IH1 safet VA1  by auto
next
  case (Plus \<theta>1 \<theta>2)
  assume IH1:"dsafe \<theta>1 \<Longrightarrow> Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume IH2:"dsafe \<theta>2 \<Longrightarrow> Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (adjointFO I \<sigma> \<nu>) \<theta>2 = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> ((\<Union> i\<in>{i. debase i \<in> SIGT (Plus \<theta>1 \<theta>2)}. FVT (\<sigma> i)))"
  assume safet:"dsafe (Plus \<theta>1 \<theta>2)"
  from VA 
    have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
    and  VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i))" unfolding Vagree_def by auto
  then show ?case
    using IH1 safet VA1 IH2 VA2 by auto
next
  case (Times \<theta>1 \<theta>2)
  assume IH1:"dsafe \<theta>1 \<Longrightarrow> Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume IH2:"dsafe \<theta>2 \<Longrightarrow> Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> sterm_sem (adjointFO I \<sigma> \<nu>) \<theta>2 = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> ((\<Union> i\<in>{i. debase i \<in> SIGT (Times \<theta>1 \<theta>2)}. FVT (\<sigma> i)))"
  assume safet:"dsafe (Times \<theta>1 \<theta>2)"
  from VA 
  have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
  and  VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i))" unfolding Vagree_def by auto
  then show ?case
    using IH1 VA1 IH2 VA2 safet by auto
next
  case (Function x1a x2a) 
  assume safet:"dsafe (Function x1a x2a)"
  from safet have nb:"nonbase x1a" by auto
  assume IH:"\<And>x. x \<in> range x2a \<Longrightarrow> dsafe x \<Longrightarrow> Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT x}. FVT (\<sigma> i)) \<Longrightarrow>
    sterm_sem (adjointFO I \<sigma> \<nu>) x = sterm_sem (adjointFO I \<sigma> \<omega>) x"
  from IH have IH':"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT (x2a j)}. FVT (\<sigma> i)) \<Longrightarrow>
    sterm_sem (adjointFO I \<sigma> \<nu>) (x2a j) = sterm_sem (adjointFO I \<sigma> \<omega>) (x2a j)"
    using rangeI safet by auto
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i)) "
  from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT (x2a j)}. FVT (\<sigma> i))"
    unfolding Vagree_def SIGT.simps using rangeI by blast
  have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
  have VAsub:"\<And>a. x1a = debase a \<Longrightarrow> (FVT (\<sigma> a)) \<subseteq> (\<Union> i\<in>{i. debase i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i))"
    using SIGT by auto
  have VAf:"\<And>a. x1a = debase a \<Longrightarrow>Vagree \<nu> \<omega> (FVT (\<sigma> a))"
    using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "args_to_id x1a")
     defer
    subgoal for x inj
    apply(cases "inj")
       defer
      subgoal for a
     proof -
       assume VA:"(\<And>a.  x1a = ident_cons FSENT a \<Longrightarrow> Vagree \<nu> \<omega> (FVT (\<sigma> a)))"
       assume sems:"(\<And>j. \<forall>x. sterm_sem (adjointFO I \<sigma> \<nu>) (x2a j) x = sterm_sem (adjointFO I \<sigma> \<omega>) (x2a j) x)"
       assume a:"args_to_id x1a = Some inj" and b:"inj = Inr a"
       from a b have some:"args_to_id x1a = Some(Inr a)" by auto
       have it:"nonbase x1a"  
         using safet  by auto
       have ach:"ilength a < ilength x1a" using arg_lengthR[OF some] by auto
       have that:"ilength a < MAX_STR" using safet some ach by auto
       have base:"x1a = debase a" 
         using arg_debaseR  it  that
         using some by blast
       note FVT = VAf[OF base]
       from dsafe have dsafer:"\<And>i. dsafe (\<sigma> i)" using dfree_is_dsafe by auto
       have dsem:"dterm_sem I (\<sigma> a) \<nu> = dterm_sem I (\<sigma> a) \<omega>"
         using coincidence_dterm[OF dsafer FVT] some by auto
       then have "\<And>R. Functions (adjointFO I \<sigma> \<nu>) x1a R = Functions (adjointFO I \<sigma> \<omega>) x1a R"
         using some unfolding adjoint_def unfolding adjointFO_def by auto
       then show "Functions (adjointFO I \<sigma> \<nu>) x1a (\<chi> i. sterm_sem (adjointFO I \<sigma> \<omega>) (x2a i) x) =
                  Functions (adjointFO I \<sigma> \<omega>) x1a (\<chi> i. sterm_sem (adjointFO I \<sigma> \<omega>) (x2a i) x)"
         by auto
     qed
     unfolding adjointFO_def by auto
   using nonbase_some nb by fastforce
qed (auto) 
  
lemma uadmit_sterm_ntadjoint:
  assumes TUA:"NTUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dsafe:"\<And>i . dsafe (\<sigma> i)"
  assumes safet:"dsafe \<theta>"
  assumes good_interp:"is_interp I"
  shows  "sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
proof -
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have "\<And>x. x \<in> ((\<Union> i\<in>{i. debase i \<in> SIGT \<theta>}. FVT (\<sigma> i))) \<Longrightarrow> x \<in> (-U)"
    using TUA unfolding NTUadmit_def by auto
  then have sub1:"(\<Union>i\<in>{i. debase i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<subseteq> -U"
    by auto
  then have VA':"Vagree \<nu> \<omega> (\<Union>i\<in>{i. debase i \<in> SIGT \<theta>}. FVT (\<sigma> i))"
    using agree_sub[OF sub1 VA] by auto
  then show "?thesis" using uadmit_sterm_ntadjoint'[OF  dsafe safet VA'] by auto
qed

lemma uadmit_dterm_adjoint':
  assumes dfree:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dfree f'"
  assumes Fsafe:"\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f'"
  assumes ode_bvo_safe:"\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE"
  assumes good_interp:"is_interp I"
  shows  "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (SigSet \<sigma> \<theta>) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> 
         dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  let ?Set = "SigSet \<sigma>"
  case (Neg \<theta>1)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>1) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>1"
  assume VA:"Vagree \<nu> \<omega> (?Set (Neg \<theta>1))"
  assume safe:"dsafe (Neg \<theta>1)"
  then show ?case
    using IH1[OF SIGT_neg[OF VA]] by auto
next
  let ?Set = "SigSet \<sigma>"
  case (Plus \<theta>1 \<theta>2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>1) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>2) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (?Set (Plus \<theta>1 \<theta>2))"
  assume safe:"dsafe (Plus \<theta>1 \<theta>2)"
  then show ?case
    using IH1[OF SIGT_plus1[OF VA]] IH2[OF SIGT_plus2[OF VA]] by auto
next
  let ?Set = "SigSet \<sigma>"
  case (Times \<theta>1 \<theta>2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>1) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>2) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (?Set (Times \<theta>1 \<theta>2))"
  assume safe:"dsafe (Times \<theta>1 \<theta>2)"
  then show ?case
    using IH1[OF SIGT_times1[OF VA]] IH2[OF SIGT_times2[OF VA]] by auto
next
  let ?Set = "SigSet \<sigma>"
  case (Max \<theta>1 \<theta>2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>1) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>2) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (?Set (Max \<theta>1 \<theta>2))"
  assume safe:"dsafe (Max \<theta>1 \<theta>2)"
  then show ?case      
    using IH1[OF SIGT_max1[OF VA]] IH2[OF SIGT_max2[OF VA]] by auto
next
  let ?Set = "SigSet \<sigma>"
  case (Div \<theta>1 \<theta>2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>1) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>2) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (?Set (Div \<theta>1 \<theta>2))"
  assume safe:"dsafe (Div \<theta>1 \<theta>2)"
  then show ?case      
    using IH1[OF SIGT_div1[OF VA]] IH2[OF SIGT_div2[OF VA]] by auto
next
  let ?Set = "SigSet \<sigma>"
  case (Min \<theta>1 \<theta>2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>1) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>2) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (?Set (Min \<theta>1 \<theta>2))"
  assume safe:"dsafe (Min \<theta>1 \<theta>2)"
  then show ?case
    using IH1[OF SIGT_min1[OF VA]] IH2[OF SIGT_min2[OF VA]] by auto
next
  let ?Set = "SigSet \<sigma>"
  case (Abs \<theta>1)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>1) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>1"
  assume VA:"Vagree \<nu> \<omega> (?Set (Abs \<theta>1))"
  assume safe:"dsafe (Abs \<theta>1)"
  then show ?case
    using IH1[OF SIGT_abs[OF VA]]by auto
next 
  let ?Set = "SigSet \<sigma>"
  case (Functional f)
  assume VA:"Vagree \<nu> \<omega> (?Set ($$F f))"
  assume safe:"dsafe ($$F f)"
  show ?case
    apply(cases "SFunls \<sigma> f")
    subgoal
      using VA safe  using VA[unfolded Vagree_def] unfolding SigSet_def 
      by (auto simp add: fun_eq_iff adjoint_def)
    subgoal for a
      using VA safe  using VA[unfolded Vagree_def] unfolding SigSet_def 
      by (auto simp add: fun_eq_iff adjoint_def)

     done

 next
  let ?Set = "SigSet \<sigma>"
  case (Function x1a x2a)
  assume IH:"\<And>x. \<And>\<nu> \<omega>. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (?Set x) \<Longrightarrow>
    dsafe x \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) x = dterm_sem (adjoint I \<sigma> \<omega>) x"
  assume safe:"dsafe (Function x1a x2a)"
  from safe have safes:"\<And>j. dsafe (x2a j)" by auto
  from IH have IH':"\<And>j. Vagree \<nu> \<omega> (?Set (x2a j)) \<Longrightarrow>
    dterm_sem (adjoint I \<sigma> \<nu>) (x2a j) = dterm_sem (adjoint I \<sigma> \<omega>) (x2a j)"
    using rangeI safes by auto
  assume VA:"Vagree \<nu> \<omega> (?Set($f x1a x2a))"
  from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (?Set(x2a j))"
    using rangeI unfolding Vagree_def SIGT.simps  SigSet_def apply auto
    subgoal for j i x
      apply(cases "SFunctions \<sigma> x")
      using rangeI unfolding Vagree_def SIGT.simps  SigSet_def apply auto
      by (metis option.simps(5))
    done
  have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
  have VAsub:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> (FVT a) \<subseteq> (?Set($f x1a x2a))"
    using SIGT unfolding SigSet_def by auto
  have VAf:"\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a)"
    using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "SFunctions \<sigma> x1a")
     defer
     subgoal for x1 x2 a
     proof -
       assume VA:"(\<And>a. SFunctions \<sigma> x1a = Some a \<Longrightarrow> Vagree \<nu> \<omega> (FVT a))"
       assume sems:"(\<And>j. \<forall>x1 x2. dterm_sem (adjoint I \<sigma> \<nu>) (x2a j) (x1,x2) = dterm_sem (adjoint I \<sigma> \<omega>) (x2a j) (x1,x2))"
       assume some:"SFunctions \<sigma> x1a = Some a"
       note FVT = VAf[OF some]
       have dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
         using dfree dfree_is_dsafe by auto
       have dsem:"\<And>R . dterm_sem (extendf I R) a \<nu> = dterm_sem (extendf I R) a \<omega>"
         using coincidence_dterm[OF dsafe[OF some] FVT] by auto
       have "\<And>R. Functions (adjoint I \<sigma> \<nu>) x1a R = Functions (adjoint I \<sigma> \<omega>) x1a R"
         using dsem some unfolding adjoint_def by auto
       then show "Functions (adjoint I \<sigma> \<nu>) x1a (\<chi> i. dterm_sem (adjoint I \<sigma> \<omega>) (x2a i) (x1,x2)) =
                  Functions (adjoint I \<sigma> \<omega>) x1a (\<chi> i. dterm_sem (adjoint I \<sigma> \<omega>) (x2a i) (x1,x2))"
         by auto
      qed
  unfolding adjoint_def apply auto    
  done
next
  let ?Set = "SigSet \<sigma>"
  case (Differential \<theta>)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (?Set \<theta>) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
  assume VA:"Vagree \<nu> \<omega> (?Set(Differential \<theta>))"
  assume safe:"dsafe (Differential \<theta>)"
  then have free:"dfree \<theta>" by (auto dest: dsafe.cases)
  from VA have VA':"Vagree \<nu> \<omega> (?Set(\<theta>))"
    by (auto simp add: SigSet_def)
  have dsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
    using dfree dfree_is_dsafe by auto
  have sem:"sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
    using uadmit_sterm_adjoint'[OF dsafe fsafe VA', of "\<lambda> x y. x" "\<lambda> x y. x" I] by auto
  have good1:"is_interp (adjoint I \<sigma> \<nu>)" using adjoint_safe[OF good_interp dfree ode_bvo_safe] by auto
  have good2:"is_interp (adjoint I \<sigma> \<omega>)" using adjoint_safe[OF good_interp dfree ode_bvo_safe] by auto
  have frech:"frechet (adjoint I \<sigma> \<nu>) \<theta> = frechet (adjoint I \<sigma> \<omega>) \<theta>"
    apply (auto simp add: fun_eq_iff)
    subgoal for a b
      using sterm_determines_frechet [OF good1 good2 free free sem, of "(a,b)"] by auto
    done
  then show "dterm_sem (adjoint I \<sigma> \<nu>) (Differential \<theta>) = dterm_sem (adjoint I \<sigma> \<omega>) (Differential \<theta>)"
    by (auto simp add: directional_derivative_def)
qed (auto)  

lemma uadmit_dterm_adjoint:
  assumes TUA:"TUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dfree f'"
  assumes Fsafe:"\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
  assumes fsafe:"\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow>  fsafe f'"
  assumes ode_bvo_safe:"\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE"
  assumes dsafe:"dsafe \<theta>"
  assumes good_interp:"is_interp I"
  shows  "dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof -
  let ?Set = "SigSet \<sigma>"
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have "\<And>x. x \<in> (?Set \<theta>) \<Longrightarrow> x \<in> (-U)"
    using TUA unfolding TUadmit_def SigSet_def by auto
  then have sub1:"(?Set \<theta>) \<subseteq> -U"
    by auto
  then have VA':"Vagree \<nu> \<omega> (?Set \<theta>)"
    using agree_sub[OF sub1 VA] by auto
  then show "?thesis" 
    using uadmit_dterm_adjoint'[OF dfree Fsafe fsafe ode_bvo_safe good_interp VA' dsafe] 
    by auto
qed

lemma uadmit_dterm_ntadjoint':
  assumes dfree:"\<And>i. dsafe (\<sigma> i)"
  assumes good_interp:"is_interp I"
  shows  "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta> \<or> Debase i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
proof (induct "\<theta>")
  case (Plus \<theta>1 \<theta>2 \<nu> \<omega>)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2 \<or> Debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT (Plus \<theta>1 \<theta>2) \<or> Debase i \<in> SIGT (Plus \<theta>1 \<theta>2)}. FVT (\<sigma> i))"
  then have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
    and VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2 \<or> Debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i))"
    unfolding Vagree_def by auto
  assume safe:"dsafe (Plus \<theta>1 \<theta>2)"
  show ?case 
    using IH1[OF VA1] IH2[OF VA2] safe by auto
next
  case (Times \<theta>1 \<theta>2 \<nu> \<omega>)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2 \<or> Debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT (Times \<theta>1 \<theta>2) \<or> Debase i \<in> SIGT (Times \<theta>1 \<theta>2)}. FVT (\<sigma> i))"
  then have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
    and VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2 \<or> Debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i))"
    unfolding Vagree_def by auto
  assume safe:"dsafe (Times \<theta>1 \<theta>2)"
  show ?case 
    using IH1[OF VA1] IH2[OF VA2] safe by auto
next
  case (Max \<theta>1 \<theta>2 \<nu> \<omega>)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2 \<or> Debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT (Max \<theta>1 \<theta>2) \<or> Debase i \<in> SIGT (Max \<theta>1 \<theta>2)}. FVT (\<sigma> i))"
  then have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
    and VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2 \<or> Debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i))"
    unfolding Vagree_def by auto
  assume safe:"dsafe (Max \<theta>1 \<theta>2)"
  show ?case 
    using IH1[OF VA1] IH2[OF VA2] safe by auto
next
  case (Min \<theta>1 \<theta>2 \<nu> \<omega>)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2 \<or> Debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT (Min \<theta>1 \<theta>2) \<or> Debase i \<in> SIGT (Min \<theta>1 \<theta>2)}. FVT (\<sigma> i))"
  then have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
    and VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2 \<or> Debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i))"
    unfolding Vagree_def by auto
  assume safe:"dsafe (Min \<theta>1 \<theta>2)"
  show ?case 
    using IH1[OF VA1] IH2[OF VA2] safe by auto
next
  case (Div \<theta>1 \<theta>2 \<nu> \<omega>)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2 \<or> Debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>2 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>2 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>2"
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT (Div \<theta>1 \<theta>2) \<or> Debase i \<in> SIGT (Div \<theta>1 \<theta>2)}. FVT (\<sigma> i))"
  then have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
    and VA2:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>2 \<or> Debase i \<in> SIGT \<theta>2}. FVT (\<sigma> i))"
    unfolding Vagree_def by auto
  assume safe:"dsafe (Div \<theta>1 \<theta>2)"
  show ?case 
    using IH1[OF VA1] IH2[OF VA2] safe by auto
next
  case (Abs \<theta>1 \<nu> \<omega>)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta>1 \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta>1 = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>1"
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT (Abs \<theta>1) \<or> Debase i \<in> SIGT (Abs \<theta>1)}. FVT (\<sigma> i))"
  then have VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta>1 \<or> Debase i \<in> SIGT \<theta>1}. FVT (\<sigma> i))"
    unfolding Vagree_def by auto
  assume safe:"dsafe (Abs \<theta>1)"
  show ?case 
    using IH1[OF VA1] safe by auto
next
  case (Functional F)
  assume safe:"dsafe ($$F F)"
  then have nb:"nonbase F" 
    and l:"ilength F < MAX_STR" by auto
  then obtain inj where inj:"args_to_id F = Some inj" using nb nonbase_some by auto
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT ($$F F) \<or> Debase i \<in> SIGT ($$F F)}. FVT (\<sigma> i))"
  then have  VA1:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT ($$F F)}. FVT (\<sigma> i))" by(auto simp add: Vagree_def)
  show ?case                                                              
  proof (cases inj)                                            
    case (Inl a) assume a:"inj = Inl a" then have cs:"args_to_id F = Some (Inl a)" using inj by auto
    have lb:"ilength a < MAX_STR" using l \<open>args_to_id F = Some (Inl a)\<close> arg_lengthL by fastforce
    have subset:"(FVT (\<sigma> a)) \<subseteq> (\<Union> i\<in>{i. debase i \<in> SIGT ($$F F) \<or> Debase i \<in> SIGT ($$F F)}. FVT (\<sigma> i))"
      apply(auto simp add: ident_cons_def)
      subgoal for v
        apply(rule exI[where x=a])
        apply(rule conjI)
         using lb unfolding ilength_def apply(auto simp add: Rep_ident_inverse[of a])
         by (metis Debase.simps  Rep_ident_inverse  \<open>args_to_id F = Some (Inl a)\<close> arg_debaseL  ident_cons.rep_eq lb not_less string_cons.elims) 
       done        
     have VAsub:"Vagree \<nu> \<omega> (FVT (\<sigma> a))"
       using VA subset 
       by (simp add: Vagree_def subset_eq)   
    then show ?thesis using cs by (auto simp add: adjointFO_def)
  next                                   
    case (Inr b) assume b:"inj = Inr b" then have cs:"args_to_id F = Some (Inr b)" using inj by auto
    have lb:"ilength b < MAX_STR" using l \<open>args_to_id F = Some (Inr b)\<close> arg_lengthR by fastforce
    have subset:"(FVT (\<sigma> b)) \<subseteq> (\<Union> i\<in>{i. debase i \<in> SIGT ($$F F) \<or> Debase i \<in> SIGT ($$F F)}. FVT (\<sigma> i))"
      apply(auto simp add: ident_cons_def)
      subgoal for v
        apply(rule exI[where x=b])
        apply(rule conjI)
         using lb unfolding ilength_def apply(auto simp add: Rep_ident_inverse[of b])
         by (metis Rep_ident_inverse \<open>args_to_id F = Some (Inr b)\<close> arg_debaseR debase.elims ident_cons.rep_eq lb not_less string_cons.elims)
       done        
     have VAsub:"Vagree \<nu> \<omega> (FVT (\<sigma> b))"
       using VA subset 
       by (simp add: Vagree_def subset_eq)   
     show "dterm_sem (adjointFO I \<sigma> \<nu>) ($$F F) = dterm_sem (adjointFO I \<sigma> \<omega>) ($$F F)"
       using cs apply(auto simp add: adjointFO_def simp del: args_to_id.simps)
       using VAsub coincidence_dterm dfree by blast
   qed
next
  case (Function x1a x2a)
    assume IH:"\<And>x. \<And>\<nu> \<omega>. x \<in> range x2a \<Longrightarrow> Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT x \<or> Debase i \<in> SIGT x}. FVT (\<sigma> i)) \<Longrightarrow>
      dsafe x \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) x = dterm_sem (adjointFO I \<sigma> \<omega>) x"
    assume safe:"dsafe (Function x1a x2a)"
    from safe have safes:"\<And>j. dsafe (x2a j)" by auto
    from safe have nb:"nonbase x1a" by auto
    from safe have l:"ilength x1a < MAX_STR" by auto
    from IH have IH':"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT (x2a j) \<or> Debase i \<in> SIGT (x2a j)}. FVT (\<sigma> i)) \<Longrightarrow>
      dterm_sem (adjointFO I \<sigma> \<nu>) (x2a j) = dterm_sem (adjointFO I \<sigma> \<omega>) (x2a j)"
      using rangeI safes by auto
    assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT ($f x1a x2a) \<or> Debase i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i))"
    from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT (x2a j)\<or> Debase i \<in> SIGT (x2a j)}. FVT (\<sigma> i))"
      unfolding Vagree_def SIGT.simps using rangeI apply(auto) 
      by blast+
    have SIGT:"x1a \<in> SIGT ($f x1a x2a)" by auto
    have VAsub:"\<And>a. args_to_id x1a = Some (Inr a) \<Longrightarrow> (FVT (\<sigma> a)) \<subseteq> (\<Union> i\<in>{i. debase i \<in> SIGT ($f x1a x2a) \<or> Debase i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i))"
    proof -
      fix a assume cs:"args_to_id x1a = Some (Inr a)"
      show"(FVT (\<sigma> a)) \<subseteq> (\<Union> i\<in>{i.  debase i \<in> SIGT ($f x1a x2a) \<or>  Debase i \<in> SIGT ($f x1a x2a)}. FVT (\<sigma> i))" 
        apply (auto simp add: ident_cons_def)
        subgoal for x
          apply(rule exI[where x=a]) apply(rule conjI) using l apply(auto simp add: Rep_ident_inverse Abs_ident_inverse ilength_def)
         using arg_lengthR[OF cs] l unfolding ilength_def apply(auto simp add: Rep_ident_inverse[of a]) 
         using Rep_ident_inverse  arg_debaseR debase.elims ident_cons.rep_eq l not_less string_cons.elims 
         by (metis Suc_lessD cs ilength.rep_eq) done
   qed
   have VAf:"\<And>a. args_to_id x1a = Some (Inr a) \<Longrightarrow> Vagree \<nu> \<omega> (FVT (\<sigma> a))"
      using agree_sub[OF VAsub VA] by auto
  then show ?case 
    using IH'[OF VAs] apply (auto simp add: fun_eq_iff)
    apply(cases "args_to_id x1a")
     defer
    subgoal for x1 x2 b
      apply(cases b)
      defer
      subgoal for a
     proof -
       assume "(\<And>a. (case ident_expose x1a of Inl x \<Rightarrow> Map.empty x
           | Inr (xa, xs) \<Rightarrow> if xa = FSENT then Some (Inr xs) else if xa = SSENT then Some (Inl xs) else None) =
          Some (Inr a) \<Longrightarrow>
          Vagree \<nu> \<omega> (FVT (\<sigma> a)))" 
       then have  VA:"(\<And>a. args_to_id x1a = Some(Inr a) \<Longrightarrow> Vagree \<nu> \<omega> (FVT (\<sigma> a)))" by auto
       assume sems:"(\<And>j. \<forall>x1 x2. dterm_sem (adjointFO I \<sigma> \<nu>) (x2a j) (x1,x2) = dterm_sem (adjointFO I \<sigma> \<omega>) (x2a j) (x1,x2))"
       assume a:"args_to_id x1a = Some b" and b:"b = Inr a"
       from a b have some:"args_to_id x1a = Some (Inr a)" by auto
       note FVT = VAf[OF some]
       have dsafe:"\<And>i. dsafe (\<sigma> i)"
         using dfree dfree_is_dsafe by auto
       have dsem:"\<And>R . dterm_sem I (\<sigma> a) \<nu> = dterm_sem I (\<sigma> a) \<omega>"
         using coincidence_dterm[OF dsafe FVT] by auto
       have "\<And>R. Functions (adjointFO I \<sigma> \<nu>) x1a R = Functions (adjointFO I \<sigma> \<omega>) x1a R"
         using dsem some unfolding adjointFO_def by auto
       then show "Functions (adjointFO I \<sigma> \<nu>) x1a (\<chi> i. dterm_sem (adjointFO I \<sigma> \<omega>) (x2a i) (x1,x2)) =
                  Functions (adjointFO I \<sigma> \<omega>) x1a (\<chi> i. dterm_sem (adjointFO I \<sigma> \<omega>) (x2a i) (x1,x2))"
         by auto
     qed
    unfolding adjointFO_def apply auto    
    done
  using  nonbase_some[OF nb] by fastforce
next
  case (Differential \<theta>)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta> \<or> Debase i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<Longrightarrow> dsafe \<theta> \<Longrightarrow> dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
  assume VA:"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT (Differential \<theta>) \<or> Debase i \<in> SIGT (Differential \<theta>)}. FVT (\<sigma> i))"
  assume safe:"dsafe (Differential \<theta>)"
  then have free:"dfree \<theta>" by (auto dest: dsafe.cases)
  from VA have VA':"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase  i \<in> SIGT \<theta> \<or> Debase i \<in> SIGT \<theta>}. FVT (\<sigma> i))"
    by auto
  from VA have VA'':"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase  i \<in> SIGT (Differential \<theta>) }. FVT (\<sigma> i))"
    by (auto simp add: Vagree_def)
  have dsafe:"\<And>i. dsafe (\<sigma> i)"
    using dfree dfree_is_dsafe by auto
  have sem:"sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = sterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
    using uadmit_sterm_ntadjoint'[OF dsafe safe VA'']
    using VA'' dfree_is_dsafe dsafe free uadmit_sterm_ntadjoint' by auto
  have good1:"is_interp (adjointFO I \<sigma> \<nu>)" using adjointFO_safe[OF good_interp dsafe, of "\<lambda>i. i"] by auto
  have good2:"is_interp (adjointFO I \<sigma> \<omega>)" using adjointFO_safe[OF good_interp dsafe, of "\<lambda>i. i"] by auto
  have frech:"frechet (adjointFO I \<sigma> \<nu>) \<theta> = frechet (adjointFO I \<sigma> \<omega>) \<theta>"
    apply (auto simp add: fun_eq_iff)
    subgoal for a b
      using sterm_determines_frechet [OF good1 good2 free free sem, of "(a,b)"] by auto
    done
  then show "dterm_sem (adjointFO I \<sigma> \<nu>) (Differential \<theta>) = dterm_sem (adjointFO I \<sigma> \<omega>) (Differential \<theta>)"
    by (auto simp add: directional_derivative_def)
qed (auto)  

lemma uadmit_dterm_ntadjoint:
  assumes TUA:"NTUadmit \<sigma> \<theta> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>i . dsafe (\<sigma> i)"
  assumes dsafe:"dsafe \<theta>"
  assumes good_interp:"is_interp I"
  shows  "dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> = dterm_sem (adjointFO I \<sigma> \<omega>) \<theta>"
proof -
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have duh:"\<And>A B. A \<inter> B = {} \<Longrightarrow> A \<subseteq> -B"
    by auto
  have "\<And>x. x \<in> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta> \<or> Debase i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<Longrightarrow> x \<in> (-U)"
    using TUA unfolding NTUadmit_def by auto
  then have sub1:"(\<Union> i\<in>{i. debase i \<in> SIGT \<theta> \<or> Debase i \<in> SIGT \<theta>}. FVT (\<sigma> i)) \<subseteq> -U"
    by auto
  then have VA':"Vagree \<nu> \<omega> (\<Union> i\<in>{i. debase i \<in> SIGT \<theta> \<or> Debase i \<in> SIGT \<theta>}. FVT (\<sigma> i))"
    using agree_sub[OF sub1 VA] by auto
  then show "?thesis" 
    using uadmit_dterm_ntadjoint'[OF dfree good_interp VA' dsafe] 
    by auto
qed

definition ssafe ::"subst \<Rightarrow> bool"
where "ssafe \<sigma> \<equiv>
  (\<forall> i. case SFunctions \<sigma> i  of Some f' \<Rightarrow> dfree f' | None \<Rightarrow> True) \<and> 
  (\<forall> f. case SPredicates \<sigma> f of Some f' \<Rightarrow> fsafe f' | None \<Rightarrow> True) \<and>
  (\<forall> F. case SFunls \<sigma> F of Some f' \<Rightarrow> dsafe f' | None \<Rightarrow> True) \<and>
  (\<forall> f. case SPrograms \<sigma> f   of Some f' \<Rightarrow> hpsafe f'| None \<Rightarrow> True) \<and>
  (\<forall> f sp. case SODEs \<sigma> f sp  of Some f' \<Rightarrow> osafe f' | None \<Rightarrow> True) \<and>
  (\<forall> f x. case SODEs \<sigma> f (Some x)  of Some f' \<Rightarrow> Inl x \<notin> BVO f' | None \<Rightarrow> True) \<and>
  (\<forall> C. case SContexts \<sigma> C   of Some C' \<Rightarrow> fsafe C' | None \<Rightarrow> True)"

lemma uadmit_dterm_adjointS:
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  fixes \<nu> \<omega>
  assumes VA:"Vagree \<nu> \<omega> (SigSet \<sigma> \<theta>)"
  assumes dsafe:"dsafe \<theta>"
  shows  "dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
proof -
  show "?thesis" 
    apply(rule uadmit_dterm_adjoint')
    subgoal  using  ssafe[unfolded ssafe_def] by (metis option.simps(5))
    subgoal  using  ssafe[unfolded ssafe_def] by (metis option.simps(5))
    subgoal  using  ssafe[unfolded ssafe_def] by (metis option.simps(5))
    subgoal  using  ssafe[unfolded ssafe_def] by (metis option.simps(5))
    apply(rule good_interp)
    apply(rule VA)
    apply(rule dsafe)
    done
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

lemma adj_sub_assign:"\<And>e \<sigma> x. (SigSet \<sigma> e) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
  subgoal for e \<sigma> x
    unfolding SDom_def apply (auto simp add: SigSet_def)
    subgoal for i j
      apply (cases "SFunctions \<sigma> j")
       apply auto
      subgoal for a
      proof -
        assume sigt:"j \<in> SIGT e"
        assume fvt:"i \<in> FVT a"
        assume some:"SFunctions \<sigma> j = Some a"
        have inBigSet:"(Inl j)\<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inl x |x. x \<in> dom (SFunls \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
        {Inl x |x. x \<in> SIGT e}" by(auto simp add: sigt fvt some)
        have sfv:"i \<in> SFV \<sigma> (Inl j)"  by(auto simp add: sigt fvt some)
        show ?thesis by(rule bexI,rule sfv, rule inBigSet) qed done
 done done


lemma adj_sub_diff_assign:"\<And>e \<sigma> x. (SigSet \<sigma> e) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (DiffAssign x e). SFV \<sigma> a)"
  subgoal for e \<sigma> x
    unfolding SDom_def apply (auto simp add: SigSet_def)
    subgoal for i j
      apply (cases "SFunctions \<sigma> j")
       apply auto
      subgoal for a
      proof -
        assume sigt:"j \<in> SIGT e"
        assume fvt:"i \<in> FVT a"
        assume some:"SFunctions \<sigma> j = Some a"
        have inBigSet:"(Inl j)\<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inl x |x. x \<in> dom (SFunls \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
         {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
        {Inl x |x. x \<in> SIGT e}" by(auto simp add: sigt fvt some)
        have sfv:"i \<in> SFV \<sigma> (Inl j)"  by(auto simp add: sigt fvt some)
        show ?thesis by(rule bexI,rule sfv, rule inBigSet) qed done
 done done

   
lemma adj_sub_geq1:"\<And>\<sigma> x1 x2. (SigSet \<sigma> x1) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
 subgoal for \<sigma> x1 x2
    unfolding SDom_def apply (auto simp add: SigSet_def)
    subgoal for x i
      apply (cases "SFunctions \<sigma> i")
       apply auto
      subgoal for a
      proof -
        assume sig:"i \<in> SIGT x1"
        assume fvt:"x \<in> FVT a"
        assume some:"SFunctions \<sigma> i = Some a"
        have inBigSet:"Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inl x |x. x \<in> dom (SFunls \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union>
          {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
          {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
         {Inl x |x. x \<in> SIGT x1 \<or> x \<in> SIGT x2}"
          by(auto simp add: sig fvt some)
        have sfv:"x \<in> SFV \<sigma> (Inl i)" by(auto simp add: sig fvt some)
        show ?thesis by(rule bexI, rule sfv, rule inBigSet) qed done
 done done

lemma adj_sub_geq2:"\<And>\<sigma> x1 x2. (SigSet \<sigma> x2) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
  subgoal for \<sigma> x1 x2
    unfolding SDom_def apply (auto simp add: SigSet_def)
    subgoal for x i
      apply (cases "SFunctions \<sigma> i")
       apply auto
      subgoal for a
      proof -
        assume sig:"i \<in> SIGT x2"
        assume fvt:"x \<in> FVT a"
        assume some:"SFunctions \<sigma> i = Some a"
        have inBigSet:"Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inl x |x. x \<in> dom (SFunls \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union>
          {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
          {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
         {Inl x |x. x \<in> SIGT x1 \<or> x \<in> SIGT x2}"
          by(auto simp add: sig fvt some)
        have sfv:"x \<in> SFV \<sigma> (Inl i)" by(auto simp add: sig fvt some)
        show ?thesis by(rule bexI, rule sfv, rule inBigSet) qed done
    done done

lemma adj_sub_prop:"\<And>\<sigma> x1 x2 j . (SigSet \<sigma> (x2 j)) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> a)"
  subgoal for \<sigma> x1 x2 j
    unfolding SDom_def apply (auto simp add: SigSet_def)
    subgoal for x i
      apply (cases "SFunctions \<sigma> i")
       apply auto
      subgoal for a
    proof -
       assume sig:"i \<in> SIGT (x2 j)"
       assume fvt:"x \<in> FVT a"
       assume some:"SFunctions \<sigma> i = Some a"
       have sfv:"x \<in> SFV \<sigma> (Inl i)" by (auto simp add: some sig fvt)
       have inBigSet:"(Inl i) \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inl x |x. x \<in> dom (SFunls \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union>
               {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
               {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
              insert (Inr (Inr x1)) {Inl x |x. \<exists>xa. x \<in> SIGT (x2 xa)}"
         apply(auto simp add: some sig fvt) using sig by blast
       show ?thesis
         apply(rule bexI) apply(rule sfv) by(rule inBigSet)
     qed  done 
    done done


lemma adj_sub_ode:"\<And>\<sigma> x1 x2. (OSigSet \<sigma> x1)  \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
 subgoal for \<sigma> x1 x2
    unfolding SDom_def apply (auto simp add: OSigSet_def)
    subgoal for x i
      apply (cases "SFunctions \<sigma> i")
       apply auto
      subgoal for a
      proof -
        assume fvt:" x \<in> FVT a"
        assume sigo:"Inl i \<in> SIGO x1"
        assume some:"SFunctions \<sigma> i = Some a"
      have inBigSet:"Inl i \<in>({Inl x |x. x \<in> dom (SFunctions \<sigma>)} \<union> {Inl x |x. x \<in> dom (SFunls \<sigma>)} \<union> {Inr (Inl x) |x. x \<in> dom (SContexts \<sigma>)} \<union>
          {Inr (Inr x) |x. x \<in> dom (SPredicates \<sigma>)} \<union>
          {Inr (Inr x) |x. x \<in> dom (SPrograms \<sigma>)}) \<inter>
         (SIGF x2 \<union> {Inl x |x. Inl x \<in> SIGO x1} \<union> {Inr (Inr x) |x. Inr x \<in> SIGO x1})"
        by(auto simp add: some sigo)
      have inSfv:"    x \<in> SFV \<sigma> (Inl i) "
        by (auto simp add: sigo fvt some)
      show ?thesis 
        apply(rule bexI)
         apply(rule inSfv)
        by(rule inBigSet)
    qed
    done
   done done

lemma uadmit_ode_adjoint':
  fixes \<sigma> I
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
(* Vagree \<nu> \<omega> (\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)*)
  shows"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (OSigSet \<sigma> ODE)\<Longrightarrow> osafe ODE \<Longrightarrow> ODE_sem (adjoint I \<sigma> \<nu>) ODE = ODE_sem (adjoint I \<sigma> \<omega>) ODE"
proof (induction ODE)
  case (OVar x sp)
  then show ?case apply(cases sp)unfolding adjoint_def apply auto apply(rule ext) apply(rule vec_extensionality) 
     apply(auto) 
    apply(rule ext, rule vec_extensionality)
    by(auto)
next
  case (OSing x1a x2) then
    have VA:"Vagree \<nu> \<omega> (OSigSet \<sigma> (OSing x1a x2))"
    and osafe:"osafe (OSing x1a x2)"
      by auto
    then have dfree:"dfree x2" by (auto dest: osafe.cases)
    have safes:"(\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      using ssafe unfolding ssafe_def using dfree_is_dsafe 
      by (metis option.simps(5))+
    have sem:"sterm_sem (adjoint I \<sigma> \<nu>) x2 = sterm_sem (adjoint I \<sigma> \<omega>) x2"
      using uadmit_sterm_adjoint'[of \<sigma> \<nu> \<omega> x2 I, OF safes, of "(\<lambda> x y. x)" "(\<lambda> x y. x)"] VA
      by(auto simp add: OSigSet_def SigSet_def Vagree_def)
    show ?case 
      apply auto
      apply (rule ext)
      subgoal for x
        apply (rule vec_extensionality)
        using sem by auto
      done
next
  case (OProd ODE1 ODE2)
    assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (OSigSet \<sigma> ODE1) \<Longrightarrow>      osafe ODE1 \<Longrightarrow> ODE_sem (adjoint I \<sigma> \<nu>) ODE1 = ODE_sem (adjoint I \<sigma> \<omega>) ODE1"
    assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (OSigSet \<sigma> ODE2) \<Longrightarrow>
    osafe ODE2 \<Longrightarrow> ODE_sem (adjoint I \<sigma> \<nu>) ODE2 = ODE_sem (adjoint I \<sigma> \<omega>) ODE2"
    assume VA:"Vagree \<nu> \<omega> (OSigSet \<sigma> (OProd ODE1 ODE2))"
    assume safe:"osafe (OProd ODE1 ODE2)"
    from safe have safe1:"osafe ODE1" and safe2:"osafe ODE2" 
       by (auto dest: osafe.cases)
    have sub1:"(OSigSet \<sigma> ODE1) \<subseteq> (OSigSet \<sigma> (OProd ODE1 ODE2))"
      by (auto simp add: OSigSet_def)
    have sub2:"(OSigSet \<sigma> ODE2) \<subseteq> (OSigSet \<sigma> (OProd ODE1 ODE2))"
      by (auto simp add: OSigSet_def)
    then show ?case 
      using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
qed

lemma uadmit_ode_ntadjoint':
  fixes \<sigma> I
  assumes ssafe:"\<And>i. dsafe (\<sigma> i)"
  assumes good_interp:"is_interp I"
  shows"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGO ODE}. FVT (\<sigma> y)) \<Longrightarrow> osafe ODE \<Longrightarrow> ODE_sem (adjointFO I \<sigma> \<nu>) ODE = ODE_sem (adjointFO I \<sigma> \<omega>) ODE"
proof (induction ODE)
  case (OVar x sp)
  then show ?case unfolding adjointFO_def 
    apply(cases sp,auto)
    apply(rule ext, rule vec_extensionality,auto)
    by(rule ext, rule vec_extensionality,auto)
next
  case (OSing x1a x2)
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGO (OSing x1a x2)}. FVT (\<sigma> y))"
  assume osafe:"osafe (OSing x1a x2)"
  then have dfree:"dfree x2" by (auto dest: osafe.cases)
  then have dsafe:"dsafe x2" using dfree_is_dsafe by auto
  have sem:"sterm_sem (adjointFO I \<sigma> \<nu>) x2 = sterm_sem (adjointFO I \<sigma> \<omega>) x2"
     using uadmit_sterm_ntadjoint'[OF ssafe dsafe] VA
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
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGO ODE1}. FVT (\<sigma> y)) \<Longrightarrow>
    osafe ODE1 \<Longrightarrow> ODE_sem (adjointFO I \<sigma> \<nu>) ODE1 = ODE_sem (adjointFO I \<sigma> \<omega>) ODE1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGO ODE2}. FVT (\<sigma> y)) \<Longrightarrow>
    osafe ODE2 \<Longrightarrow> ODE_sem (adjointFO I \<sigma> \<nu>) ODE2 = ODE_sem (adjointFO I \<sigma> \<omega>) ODE2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGO (OProd ODE1 ODE2)}. FVT (\<sigma> y))"
  assume safe:"osafe (OProd ODE1 ODE2)"
  from safe have safe1:"osafe ODE1" and safe2:"osafe ODE2" 
    using osafe_assoc
    by (auto dest: osafe.cases) 
  have sub1:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGO ODE1}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGO (OProd ODE1 ODE2)}. FVT (\<sigma> y))"
    using SIGO_assoc by auto
  have sub2:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGO ODE2}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGO (OProd ODE1 ODE2)}. FVT (\<sigma> y))"
    using SIGO_assoc by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
qed

lemma adjoint_ode_vars:
  shows "ODE_vars (adjoint I \<sigma> \<nu>) ODE = ODE_vars (adjoint I \<sigma> \<omega>) ODE"
  apply(induction ODE)
  unfolding adjoint_def by auto

lemma uadmit_mkv_adjoint:
  assumes ssafe:"ssafe \<sigma>"
  assumes good_interp:"is_interp I"
  assumes VA:"Vagree \<nu> \<omega> (OSigSet \<sigma> ODE)"
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
       subgoal for i
         apply (cases "Inl i \<in> Inl ` ODE_vars (adjoint I \<sigma> \<omega>) ODE")
       proof -
         assume sem_eq:"ODE_sem (adjoint I \<sigma> \<nu>) ODE = ODE_sem (adjoint I \<sigma> \<omega>) ODE"
         have vars_eq:"ODE_vars (adjoint I \<sigma> \<nu>) ODE = ODE_vars (adjoint I \<sigma> \<omega>) ODE"
           apply(induction ODE)
           unfolding adjoint_def by auto
         assume thing1:" 
           \<forall>i. (Inl i \<in> Inl ` ODE_vars (adjoint I \<sigma> \<nu>) ODE \<longrightarrow> fst (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = solt $ i) \<and>
             (Inl i \<in> Inr ` ODE_vars (adjoint I \<sigma> \<nu>) ODE \<longrightarrow> fst (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = solt $ i)"
         assume thing2:" 
           \<forall>i. (Inl i \<in> Inl ` ODE_vars (adjoint I \<sigma> \<omega>) ODE \<longrightarrow> fst (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i = solt $ i) \<and>
             (Inl i \<in> Inr ` ODE_vars (adjoint I \<sigma> \<omega>) ODE \<longrightarrow> fst (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i = solt $ i)"
         assume inl:"Inl i \<in> Inl ` ODE_vars (adjoint I \<sigma> \<omega>) ODE"
          from thing1 and inl have eq1: "fst (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = solt $ i"
            using vars_eq by auto
          from thing2 and inl have eq2: "fst (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i = solt $ i"
            using vars_eq by auto
         show "fst (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = fst (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i"
           using eq1 eq2 by auto
       next
         assume sem_eq:"ODE_sem (adjoint I \<sigma> \<nu>) ODE = ODE_sem (adjoint I \<sigma> \<omega>) ODE"
         assume thing1:"\<forall>i. Inl i \<notin> Inl ` ODE_vars (adjoint I \<sigma> \<nu>) ODE \<and> Inl i \<notin> Inr ` ODE_vars (adjoint I \<sigma> \<nu>) ODE \<longrightarrow>
        fst (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = fst R $ i"
         assume thing2:"\<forall>i. Inl i \<notin> Inl ` ODE_vars (adjoint I \<sigma> \<omega>) ODE \<and> Inl i \<notin> Inr ` ODE_vars (adjoint I \<sigma> \<omega>) ODE \<longrightarrow>
        fst (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i = fst R $ i"
         assume inl:"Inl i \<notin> Inl ` ODE_vars (adjoint I \<sigma> \<omega>) ODE"
         have vars_eq:"ODE_vars (adjoint I \<sigma> \<nu>) ODE = ODE_vars (adjoint I \<sigma> \<omega>) ODE"
           apply(induction ODE)
             unfolding adjoint_def by auto
         from thing1 and inl have eq1: "fst (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = fst R $ i"
           using vars_eq by auto
         from thing2 and inl have eq2: "fst (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i = fst R $ i"
           using vars_eq by auto
         show "fst (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = fst (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i"
           using eq1 eq2 by auto
       qed
      subgoal for i
        apply (cases "Inr i \<in> Inr ` ODE_vars (adjoint I \<sigma> \<omega>) ODE")
       proof -
         assume sem_eq:"ODE_sem (adjoint I \<sigma> \<nu>) ODE = ODE_sem (adjoint I \<sigma> \<omega>) ODE"
         assume thing1:"\<forall>i. (Inr i \<in> Inl ` ODE_vars (adjoint I \<sigma> \<nu>) ODE \<longrightarrow>
             snd (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = ODE_sem (adjoint I \<sigma> \<omega>) ODE solt $ i) \<and>
            (Inr i \<in> Inr ` ODE_vars (adjoint I \<sigma> \<nu>) ODE \<longrightarrow>
              snd (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = ODE_sem (adjoint I \<sigma> \<omega>) ODE solt $ i)"
         assume thing2:"\<forall>i. (Inr i \<in> Inl ` ODE_vars (adjoint I \<sigma> \<omega>) ODE \<longrightarrow>
              snd (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i = ODE_sem (adjoint I \<sigma> \<omega>) ODE solt $ i) \<and>
             (Inr i \<in> Inr ` ODE_vars (adjoint I \<sigma> \<omega>) ODE \<longrightarrow>
          snd (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i = ODE_sem (adjoint I \<sigma> \<omega>) ODE solt $ i)"
         assume inr:"Inr i \<in> Inr ` ODE_vars (adjoint I \<sigma> \<omega>) ODE"
         have vars_eq:"ODE_vars (adjoint I \<sigma> \<nu>) ODE = ODE_vars (adjoint I \<sigma> \<omega>) ODE"
          apply(induction ODE)
            unfolding adjoint_def by auto
         show "snd (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = snd (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i"
           using thing1 thing2 vars_eq inr by auto
       next
         assume sem_eq:"ODE_sem (adjoint I \<sigma> \<nu>) ODE = ODE_sem (adjoint I \<sigma> \<omega>) ODE"
         assume thing1:"\<forall>i. Inr i \<notin> Inl ` ODE_vars (adjoint I \<sigma> \<nu>) ODE \<and> Inr i \<notin> Inr ` ODE_vars (adjoint I \<sigma> \<nu>) ODE \<longrightarrow>
             snd (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = snd R $ i"
         assume thing2:"\<forall>i. Inr i \<notin> Inl ` ODE_vars (adjoint I \<sigma> \<omega>) ODE \<and> Inr i \<notin> Inr ` ODE_vars (adjoint I \<sigma> \<omega>) ODE \<longrightarrow>
             snd (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i = snd R $ i"
         assume inr:"Inr i \<notin> Inr ` ODE_vars (adjoint I \<sigma> \<omega>) ODE"
         have vars_eq:"ODE_vars (adjoint I \<sigma> \<nu>) ODE = ODE_vars (adjoint I \<sigma> \<omega>) ODE"
          apply(induction ODE)
            unfolding adjoint_def by auto
         have eq1:"snd (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = snd R $ i"
           using thing1 sem_eq vars_eq inr by auto
         have eq2:"snd (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i = snd R $ i"
           using thing2 sem_eq vars_eq inr by auto
         show "snd (mk_v (adjoint I \<sigma> \<nu>) ODE R solt) $ i = snd (mk_v (adjoint I \<sigma> \<omega>) ODE R solt) $ i"
           using eq1 eq2 by auto
       qed
      done
    done
  done

lemma adjointFO_ode_vars:
  shows "ODE_vars (adjointFO I \<sigma> \<nu>) ODE = ODE_vars (adjointFO I \<sigma> \<omega>) ODE"
  apply(induction ODE)
    unfolding adjointFO_def by auto

lemma uadmit_mkv_ntadjoint:
  assumes ssafe:"\<And>i. dsafe (\<sigma> i)"
  assumes good_interp:"is_interp I"
  assumes VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGO ODE}. FVT (\<sigma> y))"
  assumes osafe:"osafe ODE"
  shows "mk_v (adjointFO I \<sigma> \<nu>) ODE = mk_v (adjointFO I \<sigma> \<omega>) ODE"
  apply(rule ext)
  subgoal for R
    apply(rule ext)
    subgoal for solt
      apply(rule agree_UNIV_eq)
      using mk_v_agree[of "(adjointFO I \<sigma> \<nu>)" ODE "R" solt]
      using mk_v_agree[of "(adjointFO I \<sigma> \<omega>)" ODE "R" solt]
      using uadmit_ode_ntadjoint'[OF ssafe good_interp VA osafe]
      unfolding Vagree_def
      apply auto
      using adjointFO_ode_vars by metis+
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
  case (AssignAny x)
  then show ?case by (auto simp add: vec_eq_iff)
next
  case (Assign x e)
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
  assume safe:"hpsafe (x := e)"
  from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
(*  have sub:"(\<Union>i\<in>SIGT e. case SFunctions \<sigma> i of Some x \<Rightarrow> FVT x | None \<Rightarrow> {}) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
    using adj_sub_assign[of \<sigma> e x] by auto*)
  have sub:"(SigSet \<sigma> e) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (x := e). SFV \<sigma> a)"
    using adj_sub_assign[of \<sigma> e x] by auto
  have "dterm_sem (adjoint I \<sigma> \<nu>) e = dterm_sem (adjoint I \<sigma> \<omega>) e"
    by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub VA] dsafe])
  then show ?case by (auto simp add: vec_eq_iff)
next
  case (DiffAssign x e)
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (DiffAssign x e). SFV \<sigma> a)"
  assume safe:"hpsafe (DiffAssign x e)"
  from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
  have sub:"(SigSet \<sigma> e) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (DiffAssign x e). SFV \<sigma> a)"
    using adj_sub_diff_assign[of \<sigma> e] by auto
  have "dterm_sem (adjoint I \<sigma> \<nu>) e = dterm_sem (adjoint I \<sigma> \<omega>) e"
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
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) x2 = fml_sem (adjoint I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
  assume safe:"hpsafe (EvolveODE x1 x2)"
  then have osafe:"osafe x1" and fsafe:"fsafe x2" by (auto dest: hpsafe.cases)
  have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
    by auto
  then have VAF:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a)"
    using agree_sub[OF sub1 VA] by auto 
  note IH' = IH[OF VAF fsafe]
  have sub:"(OSigSet \<sigma> x1) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
    using adj_sub_ode[of \<sigma> x1 x2] 
    unfolding OSigSet_def by auto
(*  have sub:"(\<Union>i\<in>{i |i. Inl i \<in> SIGO x1}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP (EvolveODE x1 x2). SFV \<sigma> a)"
    using adj_sub_ode[of \<sigma> x1 x2] by auto*)
  moreover have IH2:"ODE_sem (adjoint I \<sigma> \<nu>) x1 = ODE_sem (adjoint I \<sigma> \<omega>) x1"
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
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (adjoint I \<sigma> \<nu>) x1 = prog_sem (adjoint I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (adjoint I \<sigma> \<nu>) x2 = prog_sem (adjoint I \<sigma> \<omega>) x2"
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
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (adjoint I \<sigma> \<nu>) x1 = prog_sem (adjoint I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x2. SFV \<sigma> a) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (adjoint I \<sigma> \<nu>) x2 = prog_sem (adjoint I \<sigma> \<omega>) x2"
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
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x. SFV \<sigma> a) \<Longrightarrow> hpsafe x \<Longrightarrow> prog_sem (adjoint I \<sigma> \<nu>) x = prog_sem (adjoint I \<sigma> \<omega>) x"
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
  have sub1:"(SigSet \<sigma> x1) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
    using adj_sub_geq1[of \<sigma> x1 x2] by auto
  have sub2:"(SigSet \<sigma> x2) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Geq x1 x2). SFV \<sigma> a)"
    using adj_sub_geq2[of \<sigma> x2 x1] by auto
  have "dterm_sem (adjoint I \<sigma> \<nu>) x1 = dterm_sem (adjoint I \<sigma> \<omega>) x1"
    by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub1 VA] dsafe1])
  moreover have "dterm_sem (adjoint I \<sigma> \<nu>) x2 = dterm_sem (adjoint I \<sigma> \<omega>) x2"
    by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF sub2 VA] dsafe2])
  ultimately show ?case by auto
next
  case (Prop x1 x2 \<nu> \<omega>)
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> a)"
  assume safe:"fsafe ($\<phi> x1 x2)"
  then have safes:"\<And>i. dsafe (x2 i)" using dfree_is_dsafe by auto
  have subs:"\<And>j. (SigSet \<sigma> (x2 j)) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF ($\<phi> x1 x2). SFV \<sigma> a)"
    subgoal for j using adj_sub_prop[of \<sigma> x2 j x1] by auto
    done
  have "\<And>i. dterm_sem (adjoint I \<sigma> \<nu>) (x2 i) = dterm_sem (adjoint I \<sigma> \<omega>) (x2 i)"
    by (rule uadmit_dterm_adjointS[OF ssafe good_interp agree_sub[OF subs VA] safes])
  then have vec_eq:"\<And>R. (\<chi> i. dterm_sem (adjoint I \<sigma> \<nu>) (x2 i) R) = (\<chi> i. dterm_sem (adjoint I \<sigma> \<omega>) (x2 i) R)"
    by (auto simp add: vec_eq_iff)
  from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (SigSet \<sigma> (x2 j))"
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
        using ssafe dfree_is_dsafe unfolding ssafe_def 
        by (metis option.simps(5))
      have good_interp_extend:"\<And>R. is_interp (extendf I R)" subgoal for R 
          using good_interp using extendf_safe by auto done
      have dsem:"\<And>R . (\<nu> \<in> fml_sem (extendf I R) a) = (\<omega> \<in> fml_sem (extendf I R) a)"
        subgoal for R
          apply (rule coincidence_formula)
          subgoal using ssafe unfolding ssafe_def using some by (metis option.simps(5))
          apply(rule good_interp_extend)
          apply(rule good_interp_extend)
           subgoal unfolding Iagree_def by auto
          subgoal by (rule FVF)
        done
      done
      have pred_eq:"\<And>R. Predicates (adjoint I \<sigma> \<nu>) x1 R = Predicates (adjoint I \<sigma> \<omega>) x1 R"
        using dsem some unfolding adjoint_def by auto
      show "fml_sem (adjoint I \<sigma> \<nu>) ($\<phi> x1 x2) = fml_sem (adjoint I \<sigma> \<omega>) ($\<phi> x1 x2)"
        apply auto
         subgoal for a b using pred_eq[of "(\<chi> i. dterm_sem (adjoint I \<sigma> \<nu>) (x2 i) (a, b))"] vec_eq by auto
        subgoal for a b using pred_eq[of "(\<chi> i. dterm_sem (adjoint I \<sigma> \<nu>) (x2 i) (a, b))"] vec_eq by auto
        done
    qed
    unfolding adjoint_def using adjoint_def local.vec_eq apply auto
    done
next
  case (Not x)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x. SFV \<sigma> a) \<Longrightarrow> fsafe x \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) x = fml_sem (adjoint I \<sigma> \<omega>) x"
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
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x1. SFV \<sigma> a) \<Longrightarrow> fsafe x1 \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) x1 = fml_sem (adjoint I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) x2 = fml_sem (adjoint I \<sigma> \<omega>) x2"
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
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) x2 = fml_sem (adjoint I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Exists x1 x2). SFV \<sigma> a)"
  assume safe:"fsafe (Exists x1 x2)"
  from safe have safe1:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub1:"(\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<subseteq> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF (Exists x1 x2). SFV \<sigma> a)"
    by auto
  show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] by auto
next
  case (Diamond x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGP x1. SFV \<sigma> a) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (adjoint I \<sigma> \<nu>) x1 = prog_sem (adjoint I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) x2 = fml_sem (adjoint I \<sigma> \<omega>) x2"
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
  case (InContext x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>a\<in>SDom \<sigma> \<inter> SIGF x2. SFV \<sigma> a) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) x2 = fml_sem (adjoint I \<sigma> \<omega>) x2"
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

lemma ntadj_sub_assign:"\<And>e \<sigma> x. (\<Union>y\<in>{y. debase y \<in> SIGT e}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (Assign x e)}. FVT (\<sigma> y))"
  by auto

(* hmm inl \<rightarrow> what?*)
lemma ntadj_sub_diff_assign:"\<And>e \<sigma> x. (\<Union>y\<in>{y. y \<in> SIGT e}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl y \<in> SIGP (DiffAssign x e)}. FVT (\<sigma> y))"
  by auto
   
lemma ntadj_sub_geq1:"\<And>\<sigma> x1 x2. (\<Union>y\<in>{y. y \<in> SIGT x1}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl y \<in> SIGF (Geq x1 x2)}. FVT (\<sigma> y))"
  by auto

lemma ntadj_sub_geq2:"\<And>\<sigma> x1 x2. (\<Union>y\<in>{y. y \<in> SIGT x2}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl y \<in> SIGF (Geq x1 x2)}. FVT (\<sigma> y))"
  by auto

lemma ntadj_sub_prop:"\<And>\<sigma> x1 x2 j. (\<Union>y\<in>{y. y \<in> SIGT (x2 j)}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl y \<in> SIGF ($\<phi> x1 x2)}.FVT (\<sigma> y))"
  by auto

lemma ntadj_sub_ode:"\<And>\<sigma> x1 x2. (\<Union>y\<in>{y. Inl y \<in> SIGO x1}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl y \<in> SIGP (EvolveODE x1 x2)}. FVT (\<sigma> y))"
  by auto

lemma uadmit_prog_fml_ntadjoint':
  fixes \<sigma> I
  assumes ssafe:"\<And>i. dsafe (\<sigma> i)"
  assumes good_interp:"is_interp I"
  shows "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (debase x) \<in> SIGP \<alpha> \<or> Inl (Debase x) \<in> SIGP \<alpha>}. FVT (\<sigma> x)) \<Longrightarrow> hpsafe \<alpha> \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) \<alpha> = prog_sem (adjointFO I \<sigma> \<omega>) \<alpha>"
  and "\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (debase x) \<in> SIGF \<phi> \<or> Inl (Debase x) \<in> SIGF \<phi>}. FVT (\<sigma> x)) \<Longrightarrow> fsafe \<phi> \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) \<phi> = fml_sem (adjointFO I \<sigma> \<omega>) \<phi>"
proof (induct "\<alpha>" and "\<phi>")
  case (Pvar x)
  then show ?case unfolding adjointFO_def by auto
next
  case (Assign x e)
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (Assign x e) \<or> Inl (Debase y) \<in> SIGP (Assign x e)}. FVT (\<sigma> y))"
  assume safe:"hpsafe (x := e)"
  from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
  have sub:"(\<Union>y\<in>{y. debase y \<in> SIGT e \<or> Debase y \<in> SIGT e}. FVT (\<sigma> y)) \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (Assign x e) \<or> Inl (Debase y) \<in> SIGP (Assign x e)}. FVT (\<sigma> y))"
    using ntadj_sub_assign[of \<sigma> e x] by auto
  have VA':"(Vagree \<nu> \<omega> (\<Union>i\<in>{i. debase i \<in> SIGT e \<or> Debase i \<in> SIGT e}. FVT (\<sigma> i)))"
    using agree_sub[OF sub VA] by auto
  have "dterm_sem (adjointFO I \<sigma> \<nu>) e = dterm_sem (adjointFO I \<sigma> \<omega>) e"
    using uadmit_dterm_ntadjoint'[of \<sigma> I \<nu> \<omega> e] ssafe good_interp agree_sub[OF sub VA] dsafe by auto
  then show ?case by (auto simp add: vec_eq_iff)
next
  case (AssignAny x)
  then show ?case by (auto simp add: vec_eq_iff)
next
  case (DiffAssign x e)
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (DiffAssign x e) \<or> Inl (Debase y) \<in> SIGP (DiffAssign x e)}. FVT (\<sigma> y))"
  assume safe:"hpsafe (DiffAssign x e)"
  from safe have dsafe:"dsafe e" by (auto dest: hpsafe.cases)
  have sub:"(\<Union>y\<in>{y. debase y \<in> SIGT e \<or> Debase y \<in> SIGT e}. FVT (\<sigma> y)) 
          \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (DiffAssign x e) \<or> Inl (Debase y) \<in> SIGP (DiffAssign x e)}. FVT (\<sigma> y))"
    using ntadj_sub_assign[of \<sigma> e x] by auto
  have VA':"(Vagree \<nu> \<omega> (\<Union>i\<in>{i. debase i \<in> SIGT e \<or>  (Debase i) \<in> SIGT e}. FVT (\<sigma> i)))"
    using agree_sub[OF sub VA] by auto
  have "dterm_sem (adjointFO I \<sigma> \<nu>) e = dterm_sem (adjointFO I \<sigma> \<omega>) e"
    using uadmit_dterm_ntadjoint'[of \<sigma> I \<nu> \<omega> e] ssafe good_interp agree_sub[OF sub VA] dsafe by auto
  then show ?case by (auto simp add: vec_eq_iff)
next
  case (Test x)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x \<or> Inl (Debase y) \<in> SIGF x}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x = fml_sem (adjointFO I \<sigma> \<omega>) x"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (? x) \<or> Inl (Debase y) \<in> SIGP (? x)}. FVT (\<sigma> y))"
  assume hpsafe:"hpsafe (? x)"
  then have fsafe:"fsafe x" by (auto dest: hpsafe.cases)
  have sub:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x \<or> Inl (Debase y) \<in> SIGF x}. FVT (\<sigma> y)) 
   \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (? x) \<or> Inl (Debase y) \<in> SIGP (? x)}. FVT (\<sigma> y))"
    by auto
  have "fml_sem (adjointFO I \<sigma> \<nu>) x = fml_sem (adjointFO I \<sigma> \<omega>) x"
    using IH[OF agree_sub[OF sub VA] fsafe] by auto
  then show ?case by auto
next
  case (EvolveODE x1 x2)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x2 \<or> Inl (Debase y) \<in> SIGF x2}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x2 = fml_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (EvolveODE x1 x2) \<or> Inl (Debase y) \<in> SIGP (EvolveODE x1 x2)}. FVT (\<sigma> y))"
  assume safe:"hpsafe (EvolveODE x1 x2)"
  then have osafe:"osafe x1" and fsafe:"fsafe x2" by (auto dest: hpsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x2 \<or> Inl (Debase y) \<in> SIGF x2}. FVT (\<sigma> y)) 
    \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (EvolveODE x1 x2) \<or>  Inl (Debase y) \<in> SIGP (EvolveODE x1 x2)}. FVT (\<sigma> y))"
    by auto
  then have VAF:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x2 \<or> Inl (Debase y) \<in> SIGF x2}. FVT (\<sigma> y))"
    using agree_sub[OF sub1 VA] by auto 
  note IH' = IH[OF VAF fsafe]
  have sub:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGO x1 }. FVT (\<sigma> y)) 
   \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (EvolveODE x1 x2) \<or> Inl (Debase y) \<in> SIGP (EvolveODE x1 x2)}. FVT (\<sigma> y))"
    by auto
  moreover have IH2:"ODE_sem (adjointFO I \<sigma> \<nu>) x1 = ODE_sem (adjointFO I \<sigma> \<omega>) x1"
    apply (rule uadmit_ode_ntadjoint')
       subgoal by (rule ssafe)
      subgoal by (rule good_interp)
     defer subgoal by (rule osafe)
    using agree_sub[OF sub VA] by auto
  have mkv:"mk_v (adjointFO I \<sigma> \<nu>) x1 = mk_v (adjointFO I \<sigma> \<omega>) x1"
    apply (rule uadmit_mkv_ntadjoint)
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
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP x1 \<or> Inl (Debase y) \<in> SIGP x1}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x1 = prog_sem (adjointFO I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP x2 \<or> Inl (Debase y) \<in> SIGP x2}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x2 = prog_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (x1 \<union>\<union> x2) \<or> Inl (Debase y) \<in> SIGP (x1 \<union>\<union> x2)}. FVT (\<sigma> y))"
  assume safe:"hpsafe (x1 \<union>\<union> x2)"
  from safe have
    safe1:"hpsafe x1"
    and safe2:"hpsafe x2"
    by (auto dest: hpsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (x1) \<or> Inl (Debase y) \<in> SIGP (x1)}. FVT (\<sigma> y)) 
  \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (x1 \<union>\<union> x2) \<or> Inl (Debase y) \<in> SIGP (x1 \<union>\<union> x2)}. FVT (\<sigma> y))"
    by auto
  have sub2:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (x2) \<or> Inl (Debase y) \<in> SIGP (x2)}. FVT (\<sigma> y)) 
           \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (x1 \<union>\<union> x2) \<or>  Inl (Debase y) \<in> SIGP (x1 \<union>\<union> x2)}. FVT (\<sigma> y))"
    by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Sequence x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP x1 \<or> Inl (Debase y) \<in> SIGP x1}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x1 = prog_sem (adjointFO I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP x2 \<or> Inl (Debase y) \<in> SIGP x2}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x2 \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x2 = prog_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (x1 ;; x2) \<or> Inl (Debase y) \<in> SIGP (x1 ;; x2)}. FVT (\<sigma> y))"
  assume safe:"hpsafe (x1 ;; x2)"
  from safe have
    safe1:"hpsafe x1"
    and safe2:"hpsafe x2"
    by (auto dest: hpsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGP x1 \<or> Inl (Debase y) \<in> SIGP x1}. FVT (\<sigma> y)) 
           \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (x1 ;; x2) \<or> Inl (Debase y) \<in> SIGP (x1 ;; x2)}. FVT (\<sigma> y))"
    by auto
  have sub2:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGP x2 \<or> Inl (Debase y) \<in> SIGP x2}. FVT (\<sigma> y)) 
           \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (x1 ;; x2) \<or> Inl (Debase y) \<in> SIGP (x1 ;; x2)}. FVT (\<sigma> y))"
    by auto
  then show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Loop x)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP x \<or> Inl (Debase y) \<in> SIGP x}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x = prog_sem (adjointFO I \<sigma> \<omega>) x"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (x**) \<or> Inl (Debase y) \<in> SIGP (x** )}. FVT (\<sigma> y))"
  assume safe:"hpsafe (x** )"
  from safe have
    safe:"hpsafe x"
    by (auto dest: hpsafe.cases)
  have sub:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (x) \<or> Inl (Debase y) \<in> SIGP (x)}. FVT (\<sigma> y)) 
          \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP (x** ) \<or> Inl (Debase y) \<in> SIGP (x** )}. FVT (\<sigma> y))"
    by auto
  show ?case using IH[OF agree_sub[OF sub VA] safe] by auto
next
  case (Geq x1 x2)
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (Geq x1 x2) \<or> Inl (Debase y) \<in> SIGF (Geq x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe (Geq x1 x2)"
  then have dsafe1:"dsafe x1" and dsafe2:"dsafe x2" by (auto dest: fsafe.cases)
  have sub1:"(\<Union>y\<in>{y. debase y \<in> SIGT x1 \<or> Debase y \<in> SIGT x1}. FVT (\<sigma> y)) 
      \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (Geq x1 x2) \<or> Inl (Debase y) \<in> SIGF (Geq x1 x2)}. FVT (\<sigma> y))"
    by auto
  have sub2:"(\<Union>y\<in>{y. debase y \<in> SIGT x2 \<or> Debase y \<in> SIGT x2}. FVT (\<sigma> y)) 
           \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (Geq x1 x2) \<or> Inl (Debase y) \<in> SIGF (Geq x1 x2)}. FVT (\<sigma> y))"
    by auto
  have "dterm_sem (adjointFO I \<sigma> \<nu>) x1 = dterm_sem (adjointFO I \<sigma> \<omega>) x1"
    by (rule uadmit_dterm_ntadjoint'[OF ssafe good_interp agree_sub[OF sub1 VA] dsafe1])
  moreover have "dterm_sem (adjointFO I \<sigma> \<nu>) x2 = dterm_sem (adjointFO I \<sigma> \<omega>) x2"
    by (rule uadmit_dterm_ntadjoint'[OF ssafe good_interp agree_sub[OF sub2 VA] dsafe2])
  ultimately show ?case by auto
next
  case (Prop x1 x2 \<nu> \<omega>)
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF ($\<phi> x1 x2) \<or> Inl (Debase y) \<in> SIGF ($\<phi> x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe ($\<phi> x1 x2)"
  then have safes:"\<And>i. dsafe (x2 i)" using dfree_is_dsafe by auto
  have subs:"\<And>j. (\<Union>y\<in>{y. debase y \<in> SIGT (x2 j) \<or> Debase y \<in> SIGT (x2 j)}. FVT (\<sigma> y)) 
               \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF ($\<phi> x1 x2) \<or> Inl (Debase y) \<in> SIGF ($\<phi> x1 x2)}. FVT (\<sigma> y))"
    subgoal for j  by auto
    done
  have "\<And>i. dterm_sem (adjointFO I \<sigma> \<nu>) (x2 i) = dterm_sem (adjointFO I \<sigma> \<omega>) (x2 i)"
    by (rule uadmit_dterm_ntadjoint'[OF ssafe good_interp agree_sub[OF subs VA] safes])
  then have vec_eq:"\<And>R. (\<chi> i. dterm_sem (adjointFO I \<sigma> \<nu>) (x2 i) R) = (\<chi> i. dterm_sem (adjointFO I \<sigma> \<omega>) (x2 i) R)"
    by (auto simp add: vec_eq_iff)
  from VA have VAs:"\<And>j. Vagree \<nu> \<omega> (\<Union>y\<in>{y. debase y \<in> SIGT (x2 j) \<or> Debase y \<in> SIGT (x2 j)}. FVT (\<sigma> y))"
    subgoal for j 
      using agree_sub[OF subs[of j] VA] by auto
    done
  then show ?case 
    using vec_eq by (auto simp add: adjointFO_def)
next
  case (Not x)
  assume IH:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x \<or> Inl (Debase y) \<in> SIGF x}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x = fml_sem (adjointFO I \<sigma> \<omega>) x"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (Not x) \<or> Inl (Debase y) \<in> SIGF (Not x)}. FVT (\<sigma> y))"
  assume safe:"fsafe (Not x)"
  from safe have
    safe:"fsafe x"
    by (auto dest: fsafe.cases)
  have sub:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x \<or> Inl (Debase y) \<in> SIGF x}. FVT (\<sigma> y)) 
          \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (Not x) \<or> Inl (Debase y) \<in> SIGF (Not x)}. FVT (\<sigma> y))"
    by auto
  show ?case using IH[OF agree_sub[OF sub VA] safe] by auto
next
  case (And x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x1 \<or> Inl (Debase y) \<in> SIGF x1}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x1 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x1 = fml_sem (adjointFO I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x2 \<or> Inl (Debase y) \<in> SIGF x2}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x2 = fml_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (And x1 x2) \<or> Inl (Debase y) \<in> SIGF (And x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe (And x1 x2)"
  from safe have
    safe1:"fsafe x1"
and safe2:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x1 \<or> Inl (Debase y) \<in> SIGF x1}. FVT (\<sigma> y))  
           \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (And x1 x2) \<or> Inl (Debase y) \<in> SIGF (And x1 x2)}. FVT (\<sigma> y))"
    by auto
  have sub2:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x2 \<or> Inl (Debase y) \<in> SIGF x2}. FVT (\<sigma> y))  
           \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (And x1 x2) \<or> Inl (Debase y) \<in> SIGF (And x1 x2)}. FVT (\<sigma> y))"
    by auto
  show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (Exists x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x2 \<or> Inl (Debase y) \<in> SIGF x2}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x2 = fml_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (Exists x1 x2) \<or> Inl (Debase y) \<in> SIGF (Exists x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe (Exists x1 x2)"
  from safe have safe1:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x2 \<or> Inl (Debase y) \<in> SIGF x2}. FVT (\<sigma> y)) 
           \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (Exists x1 x2) \<or> Inl (Debase y) \<in> SIGF (Exists x1 x2)}. FVT (\<sigma> y))"
    by auto
  show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] by auto
next
  case (Diamond x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGP x1 \<or> Inl (Debase y) \<in> SIGP x1}. FVT (\<sigma> y)) \<Longrightarrow> hpsafe x1 \<Longrightarrow> prog_sem (adjointFO I \<sigma> \<nu>) x1 = prog_sem (adjointFO I \<sigma> \<omega>) x1"
  assume IH2:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x2 \<or> Inl (Debase y) \<in> SIGF x2}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x2 = fml_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (Diamond x1 x2) \<or> Inl (Debase y) \<in> SIGF (Diamond x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe (Diamond x1 x2)"
  from safe have
    safe1:"hpsafe x1"
and safe2:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub1:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGP x1 \<or> Inl (Debase y) \<in> SIGP x1}. FVT (\<sigma> y)) 
          \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (Diamond x1 x2) \<or> Inl (Debase y) \<in> SIGF (Diamond x1 x2)}. FVT (\<sigma> y))"
    by auto
  have sub2:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x2 \<or> Inl (Debase y) \<in> SIGF x2}. FVT (\<sigma> y)) 
           \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (Diamond x1 x2) \<or> Inl (Debase y) \<in> SIGF (Diamond x1 x2)}. FVT (\<sigma> y))"
    by auto
  show ?case using IH1[OF agree_sub[OF sub1 VA] safe1] IH2[OF agree_sub[OF sub2 VA] safe2] by auto
next
  case (InContext x1 x2)
  assume IH1:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x2 \<or> Inl (Debase y) \<in> SIGF x2}. FVT (\<sigma> y)) \<Longrightarrow> fsafe x2 \<Longrightarrow> fml_sem (adjointFO I \<sigma> \<nu>) x2 = fml_sem (adjointFO I \<sigma> \<omega>) x2"
  assume VA:"Vagree \<nu> \<omega> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (InContext x1 x2) \<or> Inl (Debase y) \<in> SIGF (InContext x1 x2)}. FVT (\<sigma> y))"
  assume safe:"fsafe (InContext x1 x2)"
  from safe have  safe1:"fsafe x2"
    by (auto dest: fsafe.cases)
  have sub:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGF x2 \<or> Inl (Debase y) \<in> SIGF x2}. FVT (\<sigma> y)) 
          \<subseteq> (\<Union>y\<in>{y. Inl (debase y) \<in> SIGF (InContext x1 x2) \<or> Inl (Debase y) \<in> SIGF (InContext x1 x2)}. FVT (\<sigma> y))"
    by auto
  show ?case using IH1[OF agree_sub[OF sub VA] safe1]  
    unfolding adjointFO_def by auto
qed

lemma uadmit_prog_ntadjoint:
  assumes TUA:"PUadmitFO \<sigma> \<alpha> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>i . dsafe (\<sigma> i)"
  assumes hpsafe:"hpsafe \<alpha>"
  assumes good_interp:"is_interp I"
  shows  "prog_sem (adjointFO I \<sigma> \<nu>) \<alpha> = prog_sem (adjointFO I \<sigma> \<omega>) \<alpha>"
proof -
  have sub:"(\<Union>x\<in>{x. Inl (debase x) \<in> SIGP \<alpha> \<or> Inl (Debase x) \<in> SIGP \<alpha>}. FVT (\<sigma> x)) \<subseteq> -U" using TUA unfolding PUadmitFO_def by auto
  have VA':"Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (debase x) \<in> SIGP \<alpha> \<or> Inl (Debase x) \<in> SIGP \<alpha>}. FVT (\<sigma> x))" using agree_sub[OF sub VA] by auto
  show ?thesis 
    apply(rule uadmit_prog_fml_ntadjoint'[OF dfree good_interp])
     subgoal by (rule VA')
    subgoal by (rule hpsafe)
    done
qed

lemma uadmit_fml_ntadjoint:
  assumes TUA:"FUadmitFO \<sigma> \<phi> U"
  assumes VA:"Vagree \<nu> \<omega> (-U)"
  assumes dfree:"\<And>i . dsafe (\<sigma> i)"
  assumes fsafe:"fsafe \<phi>"
  assumes good_interp:"is_interp I"
  shows  "fml_sem (adjointFO I \<sigma> \<nu>) \<phi> = fml_sem (adjointFO I \<sigma> \<omega>) \<phi>"
proof -
  have sub:"(\<Union>x\<in>{x. Inl (debase x) \<in> SIGF \<phi> \<or> Inl (Debase x) \<in> SIGF \<phi>}. FVT (\<sigma> x)) \<subseteq> -U" using TUA unfolding FUadmitFO_def by auto
  have VA':"Vagree \<nu> \<omega> (\<Union>x\<in>{x. Inl (debase x) \<in> SIGF \<phi> \<or> Inl (Debase x) \<in> SIGF \<phi>}. FVT (\<sigma> x))" using agree_sub[OF sub VA] by auto
  show ?thesis 
    apply(rule uadmit_prog_fml_ntadjoint'[OF dfree good_interp])
     subgoal by (rule VA')
    subgoal by (rule fsafe)
    done
qed

subsection\<open>Substitution theorems for terms\<close>
lemma nsubst_sterm:
  fixes I::"interp"
  fixes \<nu>::"state"
  shows "TadmitFFO \<sigma> \<theta>  \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> sterm_sem I (TsubstFO \<theta> \<sigma>) (fst \<nu>) = sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induction rule: TadmitFFO.induct)
  case (TadmitFFO_Fun \<sigma> args f) then
  have nb:"nonbase f" and ds:"\<And>i. dsafe (\<sigma> i)"
    and l:"ilength f < MAX_STR"
    and tffo:"\<And>i. TadmitFFO \<sigma> (args i)"
    and IH:"\<And>i. ((\<forall>x. dsafe (\<sigma> x)) \<longrightarrow> sterm_sem I (TsubstFO (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjointFO I \<sigma> \<nu>) (args i) (fst \<nu>))"
    and safes:"\<And>i. dsafe (\<sigma> i)"
    and rb:"dfree (\<sigma> (rebase f))"
    by auto
  have IH':"\<And>i. sterm_sem I (TsubstFO (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjointFO I \<sigma> \<nu>) (args i) (fst \<nu>)"
    using IH ds by auto
  then have vIH:"(\<chi> i. sterm_sem I (TsubstFO (args i) \<sigma>) (fst \<nu>)) = (\<chi> i. sterm_sem (adjointFO I \<sigma> \<nu>) (args i) (fst \<nu>))"
    by auto
  obtain inj where inj:"args_to_id f = Some inj" using nb nonbase_some by auto
  then show ?case proof (cases inj)
    case (Inl a) assume "inj = Inl a" then have cs:"args_to_id f = Some (Inl a)" using inj by auto
    then show ?thesis 
    using cs vIH  ds tffo by(auto simp del: args_to_id.simps simp add: adjointFO_def)
  next
    case (Inr b) assume "inj = Inr b" then have cs:"args_to_id f = Some (Inr b)" using inj by auto
      then have free:"dfree (\<sigma> b)" using arg_rebaseR cs rb nb by blast
      note sems = dsem_to_ssem[OF free]
      then show ?thesis using cs IH adjointFO_def safes by auto
  qed
qed (auto)
  
lemma nsubst_sterm':
  fixes I::"interp"
  fixes a b::"simple_state"
  shows "TadmitFFO \<sigma> \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> sterm_sem I (TsubstFO \<theta> \<sigma>) a = sterm_sem (adjointFO I \<sigma> (a,b)) \<theta> a"
  using nsubst_sterm by (metis fst_conv)

lemma ntsubst_preserves_free:
"dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dfree(TsubstFO \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun i args) then have
        nb:"nonbase i"
    and l:"ilength i < MAX_STR"
    and frees:"\<And>j. dfree (args j)" and IHs:"\<And>j. dfree (TsubstFO (args j) \<sigma>)"
    and sub:"\<And>i. dfree (\<sigma> i)" by auto
  show "?case" proof (cases "args_to_id i")
    case None
    then show ?thesis using nonbase_some[OF nb]  by auto
  next
    case (Some inj) then have inj:"args_to_id i = Some inj" by auto
    then show ?thesis proof (cases inj)
    case (Inl a) then have a:"inj = Inl a" by auto from a inj have cs:"args_to_id i = Some (Inl a)" by auto
    then show ?thesis proof (cases "ident_expose i")
      case (Inl c) then have ie:"ident_expose i = Inl c" by auto
      then show ?thesis using nonbase_some[OF nb] by auto
    next
      case (Inr d) then have ie:"ident_expose i = Inr d" by auto
      then show ?thesis using nb apply auto apply(cases d) apply (auto simp add: FSENT_def SSENT_def FSENTINEL_def SSENTINEL_def)
        using sub cs l dfree_Fun.IH by blast+      
    qed
  next
    case (Inr b) then have a:"inj = Inr b" by auto from a inj have cs:"args_to_id i = Some (Inr b)" by auto
    then show ?thesis  apply(auto)
      apply(cases "ident_expose i")
       apply(auto)
      subgoal for a ba
        apply(cases "a = FSENT")
        by(auto simp add: sub)
      done
  qed
qed

qed (auto intro: dfree.intros)

lemma tsubst_preserves_free:
"dfree \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dfree(Tsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun i args) then 
  have nb:"nonbase i"
  and l:"ilength i < MAX_STR"
  and frees:"\<And>j. dfree (args j)"
  and freeSubst:"\<And>j. dfree (Tsubst (args j) \<sigma>)"
  and sub:"\<And>i f. SFunctions \<sigma> i = Some f \<Longrightarrow> dfree f"
    by auto then
  show "?case" 
  proof (cases "SFunctions \<sigma> i")
    case None
    then show ?thesis 
      using l freeSubst nb by(auto intro:dfree.intros ntsubst_preserves_free)
  next
    case (Some f') assume some:"SFunctions \<sigma> i = Some f'"
    then show ?thesis using l freeSubst nb frees sub by(auto intro:dfree.intros ntsubst_preserves_free)
  qed
(*    by (cases "SFunctions \<sigma> i") (auto intro:dfree.intros ntsubst_preserves_free)*)
qed (auto intro: dfree.intros)

lemma subst_sterm:
  fixes I::"interp"
  fixes \<nu>::"state"
  shows "
    TadmitF \<sigma> \<theta>  \<Longrightarrow>
    (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> 
     sterm_sem I (Tsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induction rule: TadmitF.induct)
  case (TadmitF_Fun1  \<sigma> args f f') then
    have subFree:" TadmitFFO (\<lambda>i. Tsubst (args i) \<sigma>) f'" 
      and frees:"\<And>i. dfree (Tsubst (args i) \<sigma>)" 
      and TFA:"\<And>i. TadmitF \<sigma> (args i)"
      and NTFA:"TadmitFFO (\<lambda>i. Tsubst (args i) \<sigma>) f'"
      and theIH:"\<And>i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)"
      and nb:"nonbase f"
      and l:"ilength f < MAX_STR"
        by auto
      from frees have safes:"\<And>i. dsafe (Tsubst (args i) \<sigma>)"
        by (simp add: dfree_is_dsafe) 
  assume subFreeer:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
  note admit = TadmitF_Fun1.hyps(1) and sfree = TadmitF_Fun1.prems(1)
  have IH:"(\<And>i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>))" 
    using  admit TadmitF_Fun1.prems TadmitF_Fun1.IH by auto
  have vec_eq:"(\<chi> i. sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)) = (\<chi> i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>))"
    apply(rule vec_extensionality)
    using IH by auto
  assume some:"SFunctions \<sigma> f = Some f'" 
  let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
  have IH2:"sterm_sem I (TsubstFO f' ?sub) (fst \<nu>) = sterm_sem (adjointFO I ?sub \<nu>) f' (fst \<nu>)"
    apply(rule nsubst_sterm)
     apply(rule subFree)
    by (rule safes)
  from nb obtain inj where inj:"args_to_id f = Some inj" using nonbase_some by auto
    have silly:"\<lparr>Functions =
        \<lambda>f. case args_to_id f of None \<Rightarrow> Functions I f | Some (Inl f') \<Rightarrow> Functions I f
            | Some (Inr f') \<Rightarrow> \<lambda>_. sterm_sem I (Tsubst (args f') \<sigma>) (fst \<nu>),
        Funls =
          \<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl f') \<Rightarrow> Funls I f
              | Some (Inr f') \<Rightarrow> \<lambda>_. sterm_sem I (Tsubst (args f') \<sigma>) (fst \<nu>),
        Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
     =
     \<lparr>Functions =
        \<lambda>f. case args_to_id f of None \<Rightarrow> Functions I f | Some (Inl xa) \<Rightarrow> Functions I f
            | Some (Inr f') \<Rightarrow> \<lambda>_. (\<chi> i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>)) $ f',
        Funls =
          \<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl xa) \<Rightarrow> Funls I f
              | Some (Inr f') \<Rightarrow> \<lambda>_. (\<chi> i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>)) $ f',
        Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>"
      apply(rule USubst_Lemma.interp_eq)
            apply(auto simp del: args_to_id.simps simp add: vec_eq_iff)
      subgoal
        apply(rule ext) subgoal for f apply(cases "args_to_id f") apply(auto) subgoal for a apply(cases a) apply(auto) done done done
      apply(rule ext) subgoal for f apply(cases "args_to_id f") apply(auto) subgoal for a apply(cases a) apply(auto) done done done
  show "?case" proof (cases "inj")
    case (Inl a) then have cs:"args_to_id f = Some (Inl a)" using inj by auto
    have v:"\<forall>f. ($) (vec_lambda (f::Finite_String.ident \<Rightarrow> real)) = f"
      by (meson UNIV_I vec_lambda_inverse)
    note adjoint_free[of \<sigma> I \<nu> , OF subFreeer, of "(\<lambda> x y. x)"]
    show "?thesis"
      apply(auto simp add: some IH2 vec_eq)
      using  adjointFO_free[OF frees]
       adjoint_free[OF subFreeer, of \<sigma> "(\<lambda> x y. x)" I \<nu>] 
      apply(auto simp del: adjoint_def args_to_id.simps simp add: some vec_eq_iff)
      using silly by auto
  next
    case (Inr b) then have cs:"args_to_id f = Some (Inr b)" using inj by auto
    then show ?thesis 
            apply(auto simp add: some IH2 vec_eq)
      using  adjointFO_free[OF frees]
       adjoint_free[OF subFreeer, of \<sigma> "(\<lambda> x y. x)" I \<nu>] 
      apply(auto simp del: adjoint_def args_to_id.simps simp add: some vec_eq_iff)
      using silly by auto
  qed
next
  case (TadmitF_Fun2  \<sigma> args f) 
  then have none:"SFunctions \<sigma> f = None" by auto
  note admit = TadmitF_Fun2.hyps(1) and sfree = TadmitF_Fun2.prems(1)
  have IH:"(\<And>i. TadmitF \<sigma> (args i) \<Longrightarrow>
      sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>))" 
    using  TadmitF_Fun2.prems TadmitF_Fun2.IH by auto
  have eqs:"\<And>i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)"
    using IH admit TadmitF_Fun2.IH by blast
  show "?case" 
    by(auto simp add: none IH adjoint_def vec_extensionality eqs)
  qed auto

lemma nsubst_dterm':
  fixes I::"interp"
  fixes \<nu>::"state"
  assumes good_interp:"is_interp I"    
  shows "TadmitFO \<sigma> \<theta> \<Longrightarrow> dfree \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dterm_sem I (TsubstFO \<theta> \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> \<nu>"
proof (induction rule: TadmitFO.induct)
  case (TadmitFO_Fun \<sigma> args f) then
  have admit:"\<And>i. TadmitFO \<sigma> (args i)"
  and IH:"\<And>i. dfree (args i) \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dterm_sem I (TsubstFO (args i) \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) (args i) \<nu>"
  and free:"dfree ($f f args)"
  and safe:"\<And>i. dsafe (\<sigma> i)"
    by auto
  from free have frees: "\<And>i. dfree (args i)" by (auto dest: dfree.cases)
  have sem:"\<And>i. dterm_sem I (TsubstFO (args i) \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) (args i) \<nu>"
    using IH[OF frees safe] by auto
  have vecEq:" (\<chi> i. dterm_sem (adjointFO I \<sigma> \<nu>) (args i) \<nu>) =
   (\<chi> i. dterm_sem
                   \<lparr>Functions =   (\<lambda>f. case args_to_id f of Some (Inl f') \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> (\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) | None \<Rightarrow> Functions I f),
                    Funls =  (\<lambda>f. case args_to_id f of Some (Inl f') \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> (\<lambda>_. dterm_sem I (\<sigma> f') \<nu>) | None \<Rightarrow> Funls I f),
                    Predicates = Predicates I, Contexts = Contexts I,
                    Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
          (args i) \<nu>) "
    apply(rule vec_extensionality)
    by (auto simp add: adjointFO_def)
  show " dterm_sem I (TsubstFO ($f f args) \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) ($f f args) \<nu>"
    apply (cases "args_to_id f")  subgoal
      apply (auto simp add: vec_extensionality  adjointFO_def)
      using sem vecEq  args_to_id.elims free nonbase_some by fastforce
    subgoal for a
      apply (auto simp add: vec_extensionality  adjointFO_def)
      apply(cases a)
      apply(auto) subgoal for aa 
      using sem vecEq  args_to_id.elims free nonbase_some
      by auto
    done
  done
next
  case (TadmitFO_Diff \<sigma> \<theta>) 
  hence admit:"TadmitFFO \<sigma> \<theta>"
    and admitU:"NTUadmit \<sigma> \<theta> UNIV"
    (*and IH : "dfree \<theta> \<Longrightarrow>
          (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dterm_sem I (TsubstFO \<theta> \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> \<nu>"*)
    and safe: "dfree (Differential \<theta>)" 
    and freeSub:"\<And>i. dsafe (\<sigma> i)"
    by auto
  from safe have "False" by (auto dest: dfree.cases)
  then show "dterm_sem I (TsubstFO (Differential \<theta>) \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) (Differential \<theta>) \<nu>"
    by auto
next
  case (TadmitFO_Funl \<sigma> F) then
  have df:"dfree ($$F F)" and sub:"\<And>i. dsafe (\<sigma> i)" by auto
  from df have False by auto
  then show ?case by auto
qed (auto simp add: TadmitFO.cases)

lemma ntsubst_free_to_safe:
  "dfree \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dsafe (TsubstFO \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun i args) then have
    nb:"nonbase i"
    and l:"ilength i < MAX_STR"
    and frees:"\<And>j. dfree (args j)"
    and ihs:"\<And>j. dsafe (TsubstFO (args j) \<sigma>)"
    and sub:"\<And>i. dsafe (\<sigma> i)" by auto
  obtain inj where inj:"args_to_id i = Some (inj)" 
    using nb nonbase_some by fastforce
  then show "?case"
  proof (cases inj)
    case (Inl a) then have a:"inj = Inl a" by auto then have cs:"args_to_id i = Some (Inl a)" using inj by auto
    then show ?thesis 
      apply(simp)
      apply(rule conjI)
      subgoal using nb nonbase.simps by blast
      apply(rule conjI)
      subgoal using l arg_lengthL[OF cs] by auto
      subgoal using ihs by auto done
  next
    case (Inr b) then have a:"inj = Inr b" by auto then have cs:"args_to_id i = Some (Inr b)" using inj by auto
    then show ?thesis
      apply(simp) using sub apply auto done 
  qed
qed (auto intro: dsafe.intros)

lemma ntsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dsafe (TsubstFO \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Funl F ) then have
    nb:"nonbase F"
    and l:"ilength F < MAX_STR"
(*    and frees:"\<And>j. dsafe (args j)"*)
(*    and ihs:"\<And>j. dsafe (TsubstFO (args j) \<sigma>)"*)
    and sub:"\<And>i. dfree (\<sigma> i)" by auto
  obtain inj where inj:"args_to_id F = Some (inj)" 
    using nb nonbase_some by 
    fastforce then show "?case"
  proof (cases inj)
    case (Inl a) then have a:"inj = Inl a" by auto then have cs:"args_to_id F = Some (Inl a)" using inj by auto
    then show ?thesis 
      using cs apply(simp)
      apply(rule conjI)
      subgoal using cs nb nonbase.simps by blast
      using l arg_lengthL[OF cs] by auto
  next
    case (Inr b) then have a:"inj = Inr b" by auto then have cs:"args_to_id F = Some (Inr b)" using inj by auto
    then show ?thesis apply(simp) using sub dfree_is_dsafe by auto
  qed
next
  case (dsafe_Fun i args) then have
    nb:"nonbase i"
    and l:"ilength i < MAX_STR"
    and frees:"\<And>j. dsafe (args j)"
    and ihs:"\<And>j. dsafe (TsubstFO (args j) \<sigma>)"
    and sub:"\<And>i. dfree (\<sigma> i)" by auto
  obtain inj where inj:"args_to_id i = Some (inj)" 
    using nb nonbase_some by fastforce
  then show "?case"
  proof (cases inj)
    case (Inl a) then have a:"inj = Inl a" by auto then have cs:"args_to_id i = Some (Inl a)" using inj by auto
    then show ?thesis 
      apply(simp)
      apply(rule conjI)
      subgoal using nb nonbase.simps by blast
      apply(rule conjI)
      subgoal using l arg_lengthL[OF cs] by auto
      subgoal using ihs by auto done
  next
    case (Inr b) then have a:"inj = Inr b" by auto then have cs:"args_to_id i = Some (Inr b)" using inj by auto
    then show ?thesis
      apply(simp) using sub dfree_is_dsafe by auto 
  qed
next
  case (dsafe_Diff \<theta>) then show "?case"
    by  (auto intro:dsafe.intros ntsubst_preserves_free)
qed (auto simp add: ntsubst_preserves_free intro: dsafe.intros)

lemma tsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> (\<And>i f'. SFunls \<sigma> i = Some f' \<Longrightarrow> dsafe f') \<Longrightarrow> dsafe(Tsubst \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Fun i args) then
  have dsafes:"\<And>i. dsafe (args i)"
  and IH:"\<And>j. (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dsafe (Tsubst (args j) \<sigma>)"
  and frees:"\<And>i f. SFunctions \<sigma> i = Some f \<Longrightarrow> dfree f"
    by auto
  have IH':"\<And>i. dsafe (Tsubst (args i) \<sigma>)"
    using frees IH by auto
  then show "?case" 
    apply auto
    apply(cases "SFunctions \<sigma> i")
     subgoal using IH frees dsafe_Fun.hyps(1) local.dsafe_Fun(2) by auto
    subgoal for a using frees[of i a] ntsubst_free_to_safe[of a] IH' by auto
    done 
next
  case (dsafe_Funl F) then show ?case
  by(auto,cases "SFunls \<sigma> F",auto)    
qed (auto intro: dsafe.intros tsubst_preserves_free)

lemma subst_dterm:
  fixes I::"interp"
  assumes good_interp:"is_interp I"
  shows "
    Tadmit \<sigma> \<theta> \<Longrightarrow>
    dsafe \<theta> \<Longrightarrow>
    (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> 
    (\<And>f f'. SPredicates \<sigma> f = Some f'  \<Longrightarrow> fsafe f') \<Longrightarrow>
    (\<And>f f'. SFunls \<sigma> f = Some f'  \<Longrightarrow> dsafe f') \<Longrightarrow>
    (\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE) \<Longrightarrow>
    (\<And>\<nu>. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) \<theta> \<nu>)"
proof (induction rule: Tadmit.induct)
  case (Tadmit_Funl \<sigma> f f' \<nu>)
       assume some:"SFunls \<sigma> f = Some f'"
       assume TA:" Tadmit \<sigma> f'"
       assume sfun:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
       assume spred:"(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
       assume sfunl:"(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
       assume ode_bvo_safe:"(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"

       assume "       (\<And>\<nu>. dsafe f' \<Longrightarrow>
             (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow>
             (\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f') \<Longrightarrow>
             (\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f') \<Longrightarrow> (\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE) \<Longrightarrow> dterm_sem I (Tsubst f' \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) f' \<nu>) "
       then have IH:"dterm_sem I (Tsubst f' \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) f' \<nu>"
         using sfun spred sfunl some ode_bvo_safe apply auto done
       then show ?case apply (auto, cases " SFunls \<sigma> f",auto simp add: IH TA some sfun spred sfunl)
         by (simp add: adjoint_def some)
next
  case (Tadmit_Fun1 \<sigma> args f f' \<nu>) 
  assume sfun:"\<And>i f'. SFunctions \<sigma> i = Some f'\<Longrightarrow> dfree f'"
  assume spred:"\<And>i f'. SPredicates \<sigma> i = Some f' \<Longrightarrow> fsafe f'"
  assume sfunl:"\<And>i f'. SFunls \<sigma> i = Some f' \<Longrightarrow> dsafe f'"
  assume ode_bvo_safe:"(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"
  note safe = Tadmit_Fun1.prems(1) and sfree = Tadmit_Fun1.prems(2) and TO = Tadmit_Fun1.hyps(2)
    and some = Tadmit_Fun1.hyps(1)
  hence safes:"\<And>i. dsafe (args i)" by auto
  from safe have nb:"nonbase f" and l:"ilength f < MAX_STR" by auto
  obtain inj where inj:"args_to_id f = Some inj" using nb nonbase_some by auto
  have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
      dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
    using  Tadmit_Fun1.prems Tadmit_Fun1.IH by blast
  have eqs:"\<And>i \<nu>'. dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>"
    by (auto simp add: IH safes)
  let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
  have subSafe:"(\<And>i. dsafe (?sub i))"
    using  sfunl
    by (simp add: safes sfree tsubst_preserves_safe)
  have freef:"dfree f'" using sfree some TO by auto
  have IH2:"dterm_sem I (TsubstFO f' ?sub) \<nu> = dterm_sem (adjointFO I ?sub \<nu>) f' \<nu>"
    using nsubst_dterm'[OF good_interp] some freef subSafe TO by blast
  have vec:"(\<chi> i. dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>) = (\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>)"
    apply(auto simp add: vec_eq_iff)
    subgoal for i
      using IH[of i, OF safes[of i]] 
      by auto
    done
  show "?case" apply(simp add: some)
    apply(auto simp add: vec IH2)
    apply(auto simp add: some adjoint_def adjointFO_def simp del: args_to_id.simps)
    using IH safes eqs TO sfree  IH2 good_interp adjoint_def adjointFO_def vec adjoint_def 
  proof -
    have "\<forall>f. ($) (vec_lambda (f::Finite_String.ident \<Rightarrow> real)) = f"
      by (meson UNIV_I vec_lambda_inverse)
    then show "dterm_sem \<lparr>Functions = \<lambda>i. case args_to_id i of None \<Rightarrow> Functions I i | Some (Inl ia) \<Rightarrow> Functions I i | Some (Inr i) \<Rightarrow> \<lambda>v. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>, Funls = \<lambda>i. case args_to_id i of None \<Rightarrow> Funls I i | Some (Inl ia) \<Rightarrow> Funls I i | Some (Inr i) \<Rightarrow> \<lambda>p. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>, Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr> f' \<nu> = dterm_sem \<lparr>Functions = \<lambda>i. case args_to_id i of None \<Rightarrow> Functions I i | Some (Inl ia) \<Rightarrow> Functions I i | Some (Inr i) \<Rightarrow> \<lambda>v. (\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) $ i, Funls = \<lambda>i. case args_to_id i of None \<Rightarrow> Funls I i | Some (Inl ia) \<Rightarrow> Funls I i | Some (Inr i) \<Rightarrow> \<lambda>p. (\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) $ i, Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr> f' \<nu>"
      by presburger
  qed
  next
  case (Tadmit_Fun2 \<sigma> args f \<nu>) 
  note safeTA = Tadmit_Fun2.prems(1) and sfree = Tadmit_Fun2.prems(2) 
  and none = Tadmit_Fun2.hyps(1) 
  hence safes:"\<And>i. dsafe (args i)" by auto
  have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
      dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
  using  Tadmit_Fun2.prems Tadmit_Fun2.IH by blast
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
    and IH:"dsafe \<theta> \<Longrightarrow> (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> (\<And>\<nu>. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) \<theta> \<nu>)"
    and safe:"dsafe (Differential \<theta>)"
    and sfree:"\<And>i f'1. SFunctions \<sigma> i = Some f'1 \<Longrightarrow> dfree f'1"
    and sfunl:"\<And>i f'1. SFunls \<sigma> i = Some f'1 \<Longrightarrow> dsafe f'1"
    and spsafe:"\<And>f f'. SPredicates \<sigma> f = Some f'  \<Longrightarrow> fsafe f'"
    and ode_bvo_safe:"(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"
      by auto
  from sfree have sdsafe:"\<And>f f'. SFunctions \<sigma> f = Some f' \<Longrightarrow> dsafe f'"
    using dfree_is_dsafe by auto  
  have VA:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
  from safe have free:"dfree \<theta>" by (auto dest: dsafe.cases intro: dfree.intros)
  from free have tsafe:"dsafe \<theta>" using dfree_is_dsafe by auto
  have freeSubst:"dfree (Tsubst \<theta> \<sigma>)" 
    using tsubst_preserves_free[OF free sfree]
    using Tadmit_Diff.prems(2) free tsubst_preserves_free by blast 
  have IH':"\<And>\<nu>. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) \<theta> \<nu>"
    using IH[OF tsafe sfree] by auto
  have sem_eq:"\<And>\<nu>'. dsafe \<theta> \<Longrightarrow> is_interp I \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<nu>') \<theta>"
    subgoal for \<nu>'
      using uadmit_dterm_adjoint[OF TUA VA sfree sfunl spsafe, of "(\<lambda> x y. x)" "(\<lambda> x y. x)"] ode_bvo_safe
      by auto
    done
  have IH'':"\<And>\<nu>'. dterm_sem I (Tsubst \<theta> \<sigma>) \<nu>' = dterm_sem (adjoint I \<sigma> \<nu>) \<theta> \<nu>'"
    subgoal for \<nu>'
      using sem_eq[OF tsafe good_interp, of \<nu>'] IH'[of \<nu>'] by auto
    done
  have sem_eq:"sterm_sem I (Tsubst \<theta> \<sigma>) = sterm_sem (adjoint I \<sigma> \<nu>) \<theta>" 
    apply (auto simp add: fun_eq_iff)
    subgoal for \<nu>'
      apply (cases "\<nu>'")
      subgoal for \<nu>''
        apply auto
        using dsem_to_ssem[OF free, of "(adjoint I \<sigma> \<nu>)" "(\<nu>',\<nu>')"] dsem_to_ssem[OF freeSubst, of I "(\<nu>',\<nu>')"] IH'[of "(\<nu>)"]
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
        free sem_eq] ode_bvo_safe
    by auto
qed auto  

subsection\<open>Substitution theorems for ODEs\<close>
lemma osubst_preserves_safe:
  assumes ssafe:"ssafe \<sigma>"
  shows "(osafe ODE \<Longrightarrow> Oadmit \<sigma> ODE U \<Longrightarrow> osafe (Osubst ODE \<sigma>))"
proof (induction rule: osafe.induct)
  case (osafe_Var c x2)
  then show ?case using ssafe unfolding ssafe_def apply (cases "SODEs \<sigma> c x2")
    by (simp,metis Osubst.simps(1) option.simps(5))+
next
  case (osafe_Sing \<theta> x)
  then show ?case 
  using tsubst_preserves_free ssafe unfolding ssafe_def by (simp,metis Osubst.simps(1) option.simps(5))+
next
  case (osafe_Prod ODE1 ODE2) then
   have "Oadmit \<sigma> ODE1 U" "Oadmit \<sigma> ODE2 U" "ODE_dom (Osubst ODE1 \<sigma>) \<inter>  ODE_dom (Osubst ODE2 \<sigma>) = {}"
    using osafe_Prod.prems by (auto dest: Oadmit.cases) 
  moreover have IH1:"osafe (Osubst ODE1 \<sigma>)" and IH2:"osafe (Osubst ODE2 \<sigma>)" 
     apply (auto simp add: calculation(1) osafe_Prod.IH(1))
    by (simp add: calculation(2) osafe_Prod.IH(2))
  moreover have safeProd:"osafe (OProd (Osubst ODE1 \<sigma>) (Osubst ODE2 \<sigma>))"
    apply(auto intro: osafe.intros simp add: IH1 IH2)
    using calculation(3) by auto
  moreover have safeprod:"osafe (oprod (Osubst ODE1 \<sigma>) (Osubst ODE2 \<sigma>))"
    using osafe_assoc[of "Osubst ODE1 \<sigma>" "Osubst ODE2 \<sigma>"] safeProd by auto
  ultimately show ?case 
    by(auto)
qed

lemma nosubst_preserves_safe:
  assumes sfree:"\<And>i. dfree (\<sigma> i)"
  fixes \<alpha> ::"hp" and \<phi> ::"formula"
  shows "(osafe ODE \<Longrightarrow> OUadmitFO \<sigma> ODE U \<Longrightarrow> osafe (OsubstFO ODE \<sigma>))"
proof (induction rule: osafe.induct)
  case (osafe_Var c)
  then show ?case by (auto intro: osafe.intros)
next
  case (osafe_Sing \<theta> x)
  then show ?case using sfree ntsubst_preserves_free[of \<theta> \<sigma>] unfolding OUadmitFO_def by (auto intro: osafe.intros)
next
  case (osafe_Prod ODE1 ODE2)
  assume safe1:"osafe ODE1"
    and safe2:"osafe ODE2"
    and disj:"ODE_dom ODE1 \<inter> ODE_dom ODE2 = {}"
    and IH1:"OUadmitFO \<sigma> ODE1 U \<Longrightarrow> osafe (OsubstFO ODE1 \<sigma>)"
    and IH2:"OUadmitFO \<sigma> ODE2 U \<Longrightarrow> osafe (OsubstFO ODE2 \<sigma>)"
    and NOUA:"OUadmitFO \<sigma> (OProd ODE1 ODE2) U"    

  have nosubst_preserves_ODE_dom:"\<And>ODE. ODE_dom (OsubstFO ODE \<sigma>) = ODE_dom ODE"
    subgoal for ODE
      by(induction "ODE",auto simp add: osafe_assoc ODE_dom_assoc)
    done
  have disj':"ODE_dom (OsubstFO ODE1 \<sigma>) \<inter> ODE_dom (OsubstFO ODE2 \<sigma>) = {}"
    using disj nosubst_preserves_ODE_dom by auto
  from NOUA have NOUA1:"OUadmitFO \<sigma> ODE1 U" and NOUA2:"OUadmitFO \<sigma>  ODE2 U"  unfolding OUadmitFO_def 
    by auto
  then show ?case using IH1[OF NOUA1] IH2[OF NOUA2] disj' 
    using osafe_assoc by (auto intro: osafe.intros)
qed

lemma nsubst_dterm:
  fixes I::"interp"
  fixes \<nu>::"state"
  fixes \<nu>'::"state"
  assumes good_interp:"is_interp I"    
  shows "TadmitFO \<sigma> \<theta> \<Longrightarrow> dsafe \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dterm_sem I (TsubstFO \<theta> \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) \<theta> \<nu>"
proof (induction rule: TadmitFO.induct)
  case (TadmitFO_Diff \<sigma> \<theta>) then
  have subFree:"(\<And>i. dsafe (\<sigma> i))"
    and  NTFA:"TadmitFFO \<sigma> \<theta>"
    and substFree:"dfree (TsubstFO \<theta> \<sigma>)"
    and dsafe:"dsafe (Differential \<theta>)"
    and subSafe:"\<And>i. dsafe (\<sigma> i)"
    and  NTU:"NTUadmit \<sigma> \<theta> UNIV"  
    by auto   
  have dfree:"dfree \<theta>" using dsafe by auto
  then show ?case
    apply auto
    apply (unfold directional_derivative_def) 
    apply (rule sterm_determines_frechet)
    subgoal using good_interp by auto
       subgoal using adjointFO_safe[OF good_interp, of \<sigma>] subSafe by auto
      subgoal  using substFree by auto
     subgoal using dfree by auto
    subgoal
      apply(rule ext)
      subgoal for x
        using nsubst_sterm'[of  \<sigma> \<theta> I "(fst \<nu>)" "(snd \<nu>)", OF NTFA subSafe] apply auto
      proof -
        assume sem:"sterm_sem I (TsubstFO \<theta> \<sigma>) (fst \<nu>) = sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> (fst \<nu>)"
        have VA:"\<And>\<nu> \<omega>. Vagree \<nu> (x,snd \<nu>) (-UNIV)" unfolding Vagree_def by auto
        show "sterm_sem I (TsubstFO \<theta> \<sigma>) x = sterm_sem (adjointFO I \<sigma> \<nu>) \<theta> x"
          using uadmit_sterm_ntadjoint  NTU VA subSafe  good_interp
            nsubst_sterm[OF NTFA subSafe, of I \<nu> ] 
          apply auto
          using dsafe substFree  uadmit_sterm_ntadjoint[OF NTU VA subSafe dfree_is_dsafe[OF dfree] good_interp] 
          by (metis NTFA fst_eqD nsubst_sterm)
      qed
    done
  done
next
  case (TadmitFO_Fun \<sigma> args f) then have
    fos:" \<forall>i. TadmitFO \<sigma> (args i)"
    and IH:"\<And>i. (dsafe (args i) \<Longrightarrow> (\<forall>x. dsafe (\<sigma> x)) \<Longrightarrow> dterm_sem I (TsubstFO (args i) \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) (args i) \<nu>)"
    and dsafe:"dsafe ($f f args)"
    and sub:"\<And>i. dsafe (\<sigma> i)" by auto
  from IH dsafe sub have IHs:"\<And>i. dterm_sem I (TsubstFO (args i) \<sigma>) \<nu> = dterm_sem (adjointFO I \<sigma> \<nu>) (args i) \<nu>" by auto
  from dsafe have nb:"nonbase f" by auto
  obtain inj where inj:"args_to_id f = Some (inj)" 
    using nb nonbase_some by fastforce
  then show ?case proof (cases inj)
    case (Inl a) assume a:"inj = Inl a" from inj a have cs:"args_to_id f = (Some (Inl a))" by auto
    then show ?thesis using IHs cs  unfolding adjointFO_def by auto
  next
    case (Inr b) assume a:"inj = Inr b" from inj a have cs:"args_to_id f = (Some (Inr b))" by auto
    then show ?thesis using IHs cs  unfolding adjointFO_def by auto
  qed

next
  case (TadmitFO_Funl \<sigma> F) then have
    dsafe:"dsafe (Functional F)"
    and sub:"\<And>i. dsafe (\<sigma> i)" by auto
  from dsafe have nb:"nonbase F" by auto
  obtain inj where inj:"args_to_id F = Some (inj)" 
    using nb nonbase_some by fastforce
  then show ?case proof (cases inj)
    case (Inl a) assume a:"inj = Inl a" from inj a have cs:"args_to_id F = (Some (Inl a))" by auto
    then show ?thesis unfolding adjointFO_def by auto
next
  case (Inr b) assume a:"inj = Inr b" from inj a have cs:"args_to_id F = (Some (Inr b))" by auto
  then show ?thesis unfolding adjointFO_def by auto
qed
qed (auto)
  
lemma nsubst_ode:
  fixes I::"interp"
  fixes \<nu>::"state"
  fixes \<nu>'::"state"
  assumes good_interp:"is_interp I"    
  shows "osafe ODE \<Longrightarrow> OadmitFO \<sigma> ODE U \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> ODE_sem I (OsubstFO ODE \<sigma>) (fst \<nu>)= ODE_sem (adjointFO I \<sigma> \<nu>) ODE (fst \<nu>)"
proof (induction rule: osafe.induct)
  case (osafe_Var c sp)
  then show ?case unfolding OUadmitFO_def adjointFO_def
    by(cases sp,auto)
next
  case (osafe_Sing \<theta> x)
  then show ?case apply auto
    using nsubst_sterm' [of  \<sigma> \<theta> I "(fst \<nu>)" "(snd \<nu>)"]
    by auto
next
  case (osafe_Prod ODE1 ODE2) then
  have NO1:"OadmitFO \<sigma> ODE1 U" and NO2:"OadmitFO \<sigma> ODE2 U" 
    unfolding OUadmitFO_def by auto
  have "ODE_sem I (OsubstFO ODE1 \<sigma>) (fst \<nu>) = ODE_sem (adjointFO I \<sigma> \<nu>) ODE1 (fst \<nu>)"
    "ODE_sem I (OsubstFO ODE2 \<sigma>) (fst \<nu>) = ODE_sem (adjointFO I \<sigma> \<nu>) ODE2 (fst \<nu>)" using osafe_Prod.IH osafe_Prod.prems osafe_Prod.hyps
    using NO1 NO2 by auto
  then show ?case 
    by(auto simp add: ODE_sem_assoc)
qed
    
lemma osubst_preserves_BVO:
  shows "BVO (OsubstFO ODE \<sigma>) = BVO ODE"
proof (induction "ODE")
  case (OVar x1 x2)
then show ?case by(cases x2, auto simp add: BVO_assoc)
next
  case (OSing x1 x2)
  then show ?case by (auto simp add: BVO_assoc)
next
case (OProd ODE1 ODE2)
  then show ?case by (auto simp add: BVO_assoc)
qed

lemma osubst_preserves_ODE_vars:
  shows "ODE_vars I (OsubstFO ODE \<sigma>) = ODE_vars (adjointFO I \<sigma> \<nu>) ODE"
proof (induction "ODE")
qed (auto simp add: adjointFO_def ODE_vars_assoc)

lemma osubst_preserves_semBV:
  shows "semBV I (OsubstFO ODE \<sigma>) = semBV (adjointFO I \<sigma> \<nu>) ODE"
proof (induction "ODE")
  case (OVar x1 x2)
  then show ?case by(cases x2,auto simp add: adjointFO_def ODE_vars_assoc)
next
  case (OSing x1 x2)
  then show ?case by(auto simp add: adjointFO_def ODE_vars_assoc)
next
  case (OProd ODE1 ODE2)
  then show ?case by(auto simp add: adjointFO_def ODE_vars_assoc)
qed

lemma nsubst_mkv:
  fixes I::"interp"
  fixes \<nu>::"state"
  fixes \<nu>'::"state"
  assumes good_interp:"is_interp I"  
  assumes NOU:"OadmitFO \<sigma> ODE U"
  assumes osafe:"osafe ODE "
  assumes frees:"(\<And>i. dsafe (\<sigma> i))"
  shows "(mk_v I (OsubstFO ODE \<sigma>) \<nu> (fst \<nu>')) 
    = (mk_v (adjointFO I \<sigma> \<nu>') ODE \<nu> (fst \<nu>'))"
  apply(rule agree_UNIV_eq)
  using mk_v_agree[of "adjointFO I \<sigma> \<nu>'" "ODE" \<nu> "fst \<nu>'"]
  using mk_v_agree[of "I" "OsubstFO ODE \<sigma>" \<nu> "fst \<nu>'"] 
  unfolding Vagree_def 
  using nsubst_ode[OF good_interp osafe NOU frees, of \<nu>']
  apply auto
   subgoal for i
     apply(erule allE[where x=i])+
     apply(cases "Inl i \<in> semBV I (OsubstFO ODE \<sigma>)")
      using  osubst_preserves_ODE_vars
      by (metis (full_types))+
  subgoal for i
    apply(erule allE[where x=i])+
    apply(cases "Inr i \<in> BVO ODE")
     using  osubst_preserves_ODE_vars
     by (metis (full_types))+
  done


lemma NO_sub:"OadmitFO \<sigma> ODE A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> OadmitFO \<sigma> ODE B"
  by(induction ODE, auto simp add: OUadmitFO_def)

lemma NO_to_NOU:"OadmitFO \<sigma> ODE S \<Longrightarrow> OUadmitFO \<sigma> ODE S"
  by(induction ODE, auto simp add: OUadmitFO_def)
  
subsection\<open>Substitution theorems for formulas and programs\<close>
lemma nsubst_hp_fml:
  fixes I::"interp"
  assumes good_interp:"is_interp I"    
  shows " (NPadmit \<sigma> \<alpha> \<longrightarrow> (hpsafe \<alpha> \<longrightarrow> (\<forall>i. dsafe (\<sigma> i)) \<longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO \<alpha> \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) \<alpha>)))) \<and>
    (NFadmit \<sigma> \<phi> \<longrightarrow> (fsafe \<phi> \<longrightarrow> (\<forall>i. dsafe (\<sigma> i)) \<longrightarrow> (\<forall> \<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>))))"
proof (induction rule: NPadmit_NFadmit.induct)
  case (NPadmit_Pvar \<sigma> a)
  then show ?case unfolding adjointFO_def by auto
next
  case (NPadmit_ODE \<sigma> ODE \<phi>) then
  have  NOU:"OadmitFO \<sigma> ODE (BVO ODE)"
    and NFA:"NFadmit \<sigma> \<phi>"
    and NFU:"FUadmitFO \<sigma> \<phi> (BVO ODE)"
    and fsafe:"fsafe (FsubstFO \<phi> \<sigma>)"
    and IH:"fsafe \<phi> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>))"
    and osafe':"osafe (OsubstFO ODE \<sigma>)"
      by auto
  have "hpsafe (EvolveODE ODE \<phi>) \<Longrightarrow>  (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (EvolveODE ODE \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (EvolveODE ODE \<phi>)))"
  proof -
    assume safe:"hpsafe (EvolveODE ODE \<phi>)"
    then have osafe:"osafe ODE" and fsafe:"fsafe \<phi>" by auto
    assume frees:"(\<And>i. dsafe (\<sigma> i))"
    fix \<nu> \<omega>
    show "((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (EvolveODE ODE \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (EvolveODE ODE \<phi>))"
    proof (auto)
      fix b 
        and sol :: "real \<Rightarrow>(real, ident) vec" 
        and t :: real
      assume eq1:"\<nu> = (sol 0, b)"
      assume eq2:"\<omega> = mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t)"
      assume t:"0 \<le> t"
      assume sol:"(sol solves_ode (\<lambda>a. ODE_sem I (OsubstFO ODE \<sigma>))) {0..t} 
         {x. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) x \<in> fml_sem I (FsubstFO \<phi> \<sigma>)}"
      have agree_sem:"\<And>t. Vagree (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t)) (sol 0, b) (- (Inl ` ODE_vars I (OsubstFO ODE \<sigma>) \<union> Inr ` ODE_vars I (OsubstFO ODE \<sigma>)))"
        subgoal for t
          using mk_v_agree[of I "OsubstFO ODE \<sigma>" "(sol 0, b)" "sol t"] unfolding Vagree_def apply auto
          done
        done
      have bv_sub:"(-BVO ODE) \<subseteq> - (Inl ` ODE_vars I (OsubstFO ODE \<sigma>) \<union> Inr ` ODE_vars I (OsubstFO ODE \<sigma>))"
      proof(induction ODE)
        case (OVar x1 x2)
        then show ?case using good_interp unfolding is_interp_def by (cases x2,auto)
      next
        case (OSing x1 x2)
        then show ?case by(auto)
      next
        case (OProd ODE1 ODE2)
        then show ?case by(auto simp add: ODE_vars_assoc)
      qed
      have agree:"\<And>t. Vagree (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t)) (sol 0, b) (- BVO ODE)"
        using agree_sub[OF bv_sub agree_sem] by auto
      (* Necessary *)
      have mkv:"\<And>t. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t) = mk_v (adjointFO I \<sigma> (sol t, b)) ODE (sol 0, b) (sol t)"
        using nsubst_mkv[OF good_interp NOU osafe frees]
        by auto
      have hmm:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,b) (sol s, b) (-(BVO ODE))"
        using ODE_bound_effect sol good_interp
        by (metis osubst_preserves_BVO)
      have FVT_sub:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGO ODE}. FVT (\<sigma> y)) \<subseteq> (-(BVO ODE))"
        using NOU NO_to_NOU OUadmitFO_def 
        by fastforce
      have agrees:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,b) (sol s, b) (\<Union>y\<in>{y. Inl (debase y) \<in> SIGO ODE}. FVT (\<sigma> y))" 
        subgoal for s using agree_sub[OF FVT_sub hmm[of s]] by auto done
      have "\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjointFO I \<sigma> (sol s, b)) ODE  = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE"
        subgoal for s
          apply (rule uadmit_mkv_ntadjoint)
             prefer 3
             using NOU hmm[of s] NO_to_NOU unfolding OUadmitFO_def Vagree_def
             apply fastforce   
            using frees good_interp osafe by auto
        done
      then have mkva:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjointFO I \<sigma> (sol s, b)) ODE (sol 0, b) (sol s) = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol s)"
        by presburger
      have main_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow>  mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol s) "
        using mkv mkva by auto
      note mkvt = main_eq[of t]
      have fml_eq1:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
          (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) 
        = (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s))) \<phi>)"
        using IH[OF fsafe frees] by auto
      have fml_eq2:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
        ((mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s))) \<phi>)
        =(mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>))"
        subgoal for s
          using NFU frees fsafe good_interp mk_v_agree osubst_preserves_ODE_vars uadmit_fml_ntadjoint
          using agree by blast
        done
      have fml_eq3:"\<And>s. s \<in> {0..t} \<Longrightarrow>
        (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>) = (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>) "
        using main_eq by auto
      have fml_eq: "\<And>s. s \<in> {0..t} \<Longrightarrow>
         (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) 
          =  (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>)"
        using fml_eq1 fml_eq2 fml_eq3 by meson
      have sem_eq:"\<And>t. ODE_sem I (OsubstFO ODE \<sigma>) (sol t) = ODE_sem (adjointFO I \<sigma> (sol t, b)) ODE (sol t)"
        subgoal for t
          using nsubst_ode[OF good_interp osafe NOU frees, of "(sol t,b)"] by auto
        done
      have sem_fact:"\<And>s. s \<in> {0..t} \<Longrightarrow> ODE_sem I (OsubstFO ODE \<sigma>) (sol s) = ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE (sol s)"
        subgoal for s
          using nsubst_ode[OF good_interp osafe NOU frees, of "(sol s, b)"]
          uadmit_ode_ntadjoint'[OF frees good_interp agrees[of s] osafe]
          by auto
        done
      have sol':"(sol solves_ode (\<lambda>_. ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE)) {0..t}
         {x. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) x \<in> fml_sem I (FsubstFO \<phi> \<sigma>)}"
        apply (rule solves_ode_congI)
            apply (rule sol)
           subgoal for ta by auto
          subgoal for ta by (rule sem_fact[of ta])
         subgoal by (rule refl)
        subgoal by (rule refl)
        done
      have sub:"\<And>s. s \<in> {0..t} 
              \<Longrightarrow> sol s \<in> {x. (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>)}"
        using fml_eq rangeI t sol solves_ode_domainD by fastforce
      have sol'':"(sol solves_ode (\<lambda>c. ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE)) {0..t}
 {x. mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>}"
        apply (rule solves_odeI)
         subgoal using sol' solves_ode_vderivD by blast
        using sub by auto
      show "\<exists>sola. sol 0 = sola 0 \<and>
          (\<exists>ta. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t) = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sola 0, b) (sola ta) \<and>
                0 \<le> ta \<and>
                (sola solves_ode (\<lambda>a. ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE)) {0..ta}
                 {x. mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sola 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>})"
        apply(rule exI[where x=sol])
        apply(rule conjI)
         subgoal by (rule refl)
        apply(rule exI[where x=t])
        apply(rule conjI)
         subgoal using  mkvt t by auto
        apply(rule conjI)
         subgoal by (rule t)
        subgoal by (rule sol'') 
        done
  next
    fix b 
      and sol::"real \<Rightarrow> (real, ident) vec" 
      and t::real
    assume eq1:"\<nu> = (sol 0, b)"
    assume eq2:"\<omega> = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol t)"
    assume t:"0 \<le> t"
    assume sol:"(sol solves_ode (\<lambda>a. ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE)) {0..t}
     {x. mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>}"
    have agree_sem:"\<And>t. Vagree (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t)) (sol 0, b) (- (Inl ` ODE_vars I (OsubstFO ODE \<sigma>) \<union> Inr ` ODE_vars I (OsubstFO ODE \<sigma>)))"
      subgoal for t
        using mk_v_agree[of I "OsubstFO ODE \<sigma>" "(sol 0, b)" "sol t"] unfolding Vagree_def apply auto
        done
      done
    have bv_sub:"(-BVO ODE) \<subseteq> - (Inl ` ODE_vars I (OsubstFO ODE \<sigma>) \<union> Inr ` ODE_vars I (OsubstFO ODE \<sigma>))"
    proof(induction ODE)
      case (OVar x1 x2)
      then show ?case  apply(cases x2, auto simp add: ODE_vars_assoc) using good_interp unfolding is_interp_def by auto 
    next
      case (OSing x1 x2)
      then show ?case by( auto simp add: ODE_vars_assoc)
    next
      case (OProd ODE1 ODE2)
      then show ?case by( auto simp add: ODE_vars_assoc)
    qed
    have agree:"\<And>t. Vagree (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t)) (sol 0, b) (- BVO ODE)"
      using agree_sub[OF bv_sub agree_sem] by auto
    (* Necessary *)
    have mkv:"\<And>t. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol t) = mk_v (adjointFO I \<sigma> (sol t, b)) ODE (sol 0, b) (sol t)"
      using nsubst_mkv[OF good_interp NOU osafe frees]
      by auto
    have hmm:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,b) (sol s, b) (-(BVO ODE))"
      apply(rule ODE_bound_effect)
using sol good_interp
      osubst_preserves_ODE_vars good_interp apply auto
  apply(rule adjointFO_safe) apply(rule good_interp) 
  using frees by blast
    have FVT_sub:"(\<Union>y\<in>{y. Inl (debase y) \<in> SIGO ODE}. FVT (\<sigma> y)) \<subseteq> (-(BVO ODE))"
      using NOU NO_to_NOU unfolding OUadmitFO_def by fastforce
    have agrees:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,b) (sol s, b) (\<Union>y\<in>{y. Inl (debase y) \<in> SIGO ODE}. FVT (\<sigma> y))" 
      subgoal for s using agree_sub[OF FVT_sub hmm[of s]] by auto done
    have "\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjointFO I \<sigma> (sol s, b)) ODE  = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE"
      subgoal for s
        apply (rule uadmit_mkv_ntadjoint)
           prefer 3
           using NOU hmm[of s] NO_to_NOU unfolding OUadmitFO_def Vagree_def
           apply fastforce   
          using frees good_interp osafe by auto
        done
    then have mkva:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjointFO I \<sigma> (sol s, b)) ODE (sol 0, b) (sol s) = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol s)"
      by presburger
    have main_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow>  mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) = mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol s) "
      using mkv mkva by auto
    note mkvt = main_eq[of t]
    have fml_eq1:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
        (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) 
      = (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s))) \<phi>)"
      using IH[OF fsafe frees] by auto
    have fml_eq2:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
      ((mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s))) \<phi>)
      =(mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>))"
        using  NFU frees fsafe good_interp mk_v_agree osubst_preserves_ODE_vars uadmit_fml_ntadjoint agree by blast
      
    have fml_eq3:"\<And>s. s \<in> {0..t} \<Longrightarrow>
     (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>) = (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>) "
     using main_eq by auto
    have fml_eq: "\<And>s. s \<in> {0..t} \<Longrightarrow>
      (mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) (sol s) \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) 
       =  (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) (sol s) \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>)"
      using fml_eq1 fml_eq2 fml_eq3 by meson
     have sem_eq:"\<And>t. ODE_sem I (OsubstFO ODE \<sigma>) (sol t) = ODE_sem (adjointFO I \<sigma> (sol t, b)) ODE (sol t)"
       subgoal for t
         using nsubst_ode[OF good_interp osafe NOU frees, of "(sol t,b)"] by auto
       done
    have sem_fact:"\<And>s. s \<in> {0..t} \<Longrightarrow> ODE_sem I (OsubstFO ODE \<sigma>) (sol s) = ODE_sem (adjointFO I \<sigma> (sol 0, b)) ODE (sol s)"
      subgoal for s
        using nsubst_ode[OF good_interp osafe NOU frees, of "(sol s, b)"]
        uadmit_ode_ntadjoint'[OF frees good_interp agrees[of s] osafe]
        by auto
      done
    have sol':"
      (sol solves_ode (\<lambda>a. ODE_sem I (OsubstFO ODE \<sigma>))) {0..t}  {x. mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>}"
      apply (rule solves_ode_congI)
          apply (rule sol)
         subgoal for ta by auto
        subgoal for ta using sem_fact[of ta] by auto
       subgoal by (rule refl)
      subgoal by (rule refl)
      done
    have sub:"\<And>s. s \<in> {0..t} 
            \<Longrightarrow> sol s \<in> {x. (mk_v (adjointFO I \<sigma> (sol 0,b)) ODE (sol 0, b) x \<in> fml_sem (adjointFO I \<sigma> (sol 0, b)) \<phi>)}"
      using fml_eq rangeI t sol solves_ode_domainD by fastforce
    have sol'':"(sol solves_ode (\<lambda>a. ODE_sem I (OsubstFO ODE \<sigma>))) {0..t} {x. mk_v I (OsubstFO ODE \<sigma>) (sol 0, b) x \<in> fml_sem I (FsubstFO \<phi> \<sigma>)}"
      apply (rule solves_odeI)
       subgoal using sol' solves_ode_vderivD by blast
      using sub fml_eq by blast
    show "\<exists>sola. sol 0 = sola 0 \<and>
          (\<exists>ta. mk_v (adjointFO I \<sigma> (sol 0, b)) ODE (sol 0, b) (sol t) = mk_v I (OsubstFO ODE \<sigma>) (sola 0, b) (sola ta) \<and>
                0 \<le> ta \<and>
                (sola solves_ode (\<lambda>a. ODE_sem I (OsubstFO ODE \<sigma>))) {0..ta} {x. mk_v I (OsubstFO ODE \<sigma>) (sola 0, b) x \<in> fml_sem I (FsubstFO \<phi> \<sigma>)})"
      apply(rule exI[where x=sol])
      apply(rule conjI)
       subgoal by (rule refl)
      apply(rule exI[where x=t])
      apply(rule conjI)
       subgoal using t mkvt by auto
      apply(rule conjI)
       subgoal by (rule t)
      subgoal by (rule sol'')
      done
    qed
  qed
  then show ?case by auto 
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
  then have NTA:"\<And>i. TadmitFO \<sigma> (args i)" by auto
  have "\<And>\<nu>.  fsafe ($\<phi> f args) \<Longrightarrow>  (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<nu> \<in> fml_sem I (FsubstFO ($\<phi> f args) \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) ($\<phi> f args))"
  proof -
    fix \<nu>
    assume safe:"fsafe ($\<phi> f args)"
    from safe have safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
    assume subFree:"(\<And>i. dsafe (\<sigma> i))"
    have vec_eq:"(\<chi> i. dterm_sem (adjointFO I \<sigma> \<nu>) (args i) \<nu>) = (\<chi> i. dterm_sem I (TsubstFO (args i) \<sigma>) \<nu>)"
      apply(rule vec_extensionality)
      using nsubst_dterm[OF good_interp NTA safes subFree] by auto
    then show "?thesis \<nu>" unfolding adjointFO_def by auto
  qed
  then show ?case by auto 
next
  case (NPadmit_Sequence \<sigma> a b) then 
  have PUA:"PUadmitFO \<sigma> b (BVP (PsubstFO a \<sigma>))"
    and PA:"NPadmit \<sigma> a"
    and IH1:"hpsafe a \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a))"
    and IH2:"hpsafe b \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) b))"
    and hpsafeS:"hpsafe (PsubstFO a \<sigma>)"
     by auto
  have "hpsafe (a ;; b) \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (a ;; b)))"
  proof -
    assume hpsafe:"hpsafe (a ;; b)"
    assume ssafe:"(\<And>i. dsafe (\<sigma> i))"
    from hpsafe have safe1:"hpsafe a" and safe2:"hpsafe b" by (auto dest: hpsafe.cases)
    fix \<nu> \<omega>
    have agree:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(PsubstFO a \<sigma>))"
      subgoal for \<mu>
        using bound_effect[OF good_interp, of "(PsubstFO a \<sigma>)" \<nu> , OF hpsafeS] by auto
      done
    have sem_eq:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> 
        ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) b) =
        ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<mu>) b)"
      subgoal for \<mu>
      proof -
        assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>)"
        show "((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) b) = ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<mu>) b)"
          using uadmit_prog_ntadjoint [OF PUA agree[OF assm] ssafe safe2 good_interp] 
          by auto
      qed
      done      
    have "((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a ;; b) \<sigma>)) = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem I (PsubstFO b \<sigma>))"
      by auto
    moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<mu>) b)"
      using IH2[OF safe2 ssafe] by auto
    moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<and> (\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) b)"
      using sem_eq by auto
    moreover have "... = (\<exists> \<mu>. (\<nu>, \<mu>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a \<and> (\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) b)"
      using IH1[OF safe1 ssafe] by auto
    ultimately
    show "((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (a ;; b))"
      by auto
  qed
  then show ?case by auto
next
  case (NPadmit_Loop \<sigma> a) then 
  have PA:"NPadmit \<sigma> a"
    and PUA:"PUadmitFO \<sigma> a (BVP (PsubstFO a \<sigma>))"
    and IH:"hpsafe a \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a))"
    and hpsafeS:"hpsafe (PsubstFO a \<sigma>)"
      by auto
  have "hpsafe (a**) \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (a**)))"
  proof -
    assume "hpsafe (a**)"
    then have hpsafe:"hpsafe a" by (auto dest: hpsafe.cases)
    assume ssafe:"(\<And>i. dsafe (\<sigma> i))"
    have agree:"\<And>\<nu> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(PsubstFO a \<sigma>))"
      subgoal for \<nu> \<mu>
        using bound_effect[OF good_interp, of "(PsubstFO a \<sigma>)" \<nu>, OF hpsafeS] 
        by auto
      done
    have sem_eq:"\<And>\<nu> \<mu> \<omega>. (\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> 
        ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a) =
        ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<mu>) a)"
      subgoal for \<nu> \<mu> \<omega> 
        proof -
          assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (PsubstFO a \<sigma>)"
          show "((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a) = ((\<mu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<mu>) a)"
            using uadmit_prog_ntadjoint[OF PUA agree[OF assm] ssafe hpsafe  good_interp] by auto
        qed
      done 
    fix \<nu> \<omega>
    have UN_rule:"\<And> a S S'. (\<And>n b. (a,b) \<in> S n \<longleftrightarrow> (a,b) \<in> S' n) \<Longrightarrow> (\<And>b. (a,b) \<in> (\<Union>n. S n) \<longleftrightarrow> (a,b) \<in> (\<Union>n. S' n))"
      by auto
    have eqL:"((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (PsubstFO a \<sigma>)) ^^ n))"
      using rtrancl_is_UN_relpow by auto
    moreover have eachEq:"\<And>n. ((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (PsubstFO a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (adjointFO I \<sigma> \<nu>) a)^^ n)))"
    proof -
      fix n
      show "((\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> (prog_sem I (PsubstFO a \<sigma>)) ^^ n) = ((\<nu>, \<omega>) \<in> (prog_sem (adjointFO I \<sigma> \<nu>) a)^^ n)))"
      proof (induct n)
        case 0
        then show ?case by auto
      next
        case (Suc n) then
        have IH2:"\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>) ^^ n) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a ^^ n)"
          by auto
        have relpow:"\<And>R n. R ^^ Suc n = R O R ^^ n"
          using relpow.simps(2) relpow_commute by metis
        show ?case 
          apply (simp only: relpow[of n "prog_sem I (PsubstFO a \<sigma>)"] relpow[of n "prog_sem (adjointFO I \<sigma> \<nu>) a"])
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
    moreover have "((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem I (PsubstFO a \<sigma>)) ^^ n)) = ((\<nu>, \<omega>) \<in> (\<Union> n.(prog_sem (adjointFO I \<sigma> \<nu>) a)^^ n))"
      apply(rule UN_rule)
      using eachEq by auto
    moreover have eqR:"((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (a**)) = ((\<nu>, \<omega>) \<in> (\<Union>n. (prog_sem (adjointFO I \<sigma> \<nu>) a) ^^ n))"
       using rtrancl_is_UN_relpow by auto
    ultimately show "((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) (a**))"
      by auto
  qed
  then show ?case by auto
next
  case (NFadmit_Exists \<sigma> \<phi> x)
  then have IH:"fsafe \<phi> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>))"
    and FUA:"FUadmitFO \<sigma> \<phi> {Inl x}"
    by blast+
  have fsafe:"fsafe (Exists x \<phi>) \<Longrightarrow> fsafe \<phi>"
    by (auto dest: fsafe.cases)
  have eq:"fsafe (Exists x \<phi>) \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>)  (Exists x \<phi>)))"
  proof -
    assume fsafe:"fsafe (Exists x \<phi>)"
    from fsafe have fsafe':"fsafe \<phi>" by (auto dest: fsafe.cases)
    assume ssafe:"(\<And>i. dsafe (\<sigma> i))"
    fix \<nu>
    have agree:"\<And>r. Vagree \<nu> (repv \<nu> x r) (- {Inl x})"
      unfolding Vagree_def by auto
    have sem_eq:"\<And>r. ((repv \<nu> x r) \<in> fml_sem (adjointFO I \<sigma> (repv \<nu> x r)) \<phi>) =
                      ((repv \<nu> x r) \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>)"
      using uadmit_fml_ntadjoint[OF FUA agree ssafe fsafe' good_interp] by auto
    have "(\<nu> \<in> fml_sem I (FsubstFO  (Exists x \<phi>) \<sigma>)) = (\<exists>r. (repv \<nu> x r) \<in> fml_sem I (FsubstFO \<phi> \<sigma>))"
      by auto
    moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (adjointFO I \<sigma> (repv \<nu> x r)) \<phi>)"
      using IH[OF fsafe' ssafe] by auto
    moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>)"
      using sem_eq by auto
    moreover have "... = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) (Exists x \<phi>))"
      by auto
    ultimately show "(\<nu> \<in> fml_sem I (FsubstFO  (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) (Exists x \<phi>))"
      by auto
  qed
  then show ?case by auto
next
  case (NFadmit_Diamond \<sigma> \<phi> a) then 
  have PA:"NPadmit \<sigma> a" 
    and FUA:"FUadmitFO \<sigma> \<phi> (BVP (PsubstFO a \<sigma>))"
    and IH1:"fsafe \<phi> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>))"
    and IH2:"hpsafe a \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a))"
    and hpsafeF:"hpsafe (PsubstFO a \<sigma>)"
      by auto
  have "fsafe (\<langle> a \<rangle> \<phi>) \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO (\<langle> a \<rangle> \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) (\<langle> a \<rangle> \<phi>)))"
  proof -
    assume fsafe:"fsafe (\<langle> a \<rangle> \<phi>)"
    assume ssafe:"(\<And>i. dsafe (\<sigma> i))"
    from fsafe have fsafe':"fsafe \<phi>" and hpsafe:"hpsafe a" by (auto dest: fsafe.cases)
    fix \<nu>
    have agree:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> Vagree \<nu> \<omega> (-BVP(PsubstFO a \<sigma>))"
      using bound_effect[OF good_interp, of "(PsubstFO a \<sigma>)" \<nu>, OF hpsafeF] by auto
    have sem_eq:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>) \<Longrightarrow> 
        (\<omega> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>) =
        (\<omega> \<in> fml_sem (adjointFO I \<sigma> \<omega>) \<phi>)"
      using uadmit_fml_ntadjoint [OF FUA agree ssafe fsafe' good_interp] by auto
    have "(\<nu> \<in> fml_sem I (FsubstFO (\<langle> a \<rangle> \<phi>) \<sigma>)) = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I (PsubstFO a \<sigma>) \<and> \<omega> \<in> fml_sem I (FsubstFO \<phi> \<sigma>))"
      by auto
    moreover have "... = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a \<and> \<omega> \<in> fml_sem (adjointFO I \<sigma> \<omega>) \<phi>)"
      using IH1[OF fsafe' ssafe] IH2[OF hpsafe ssafe, of \<nu>] by auto
    moreover have "... = (\<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem (adjointFO I \<sigma> \<nu>) a \<and> \<omega> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>)"
      using sem_eq IH2 hpsafe ssafe by blast
    moreover have "... = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) (\<langle> a \<rangle> \<phi>))"
      by auto
    ultimately show "?thesis \<nu>" by auto
  qed
  then show ?case by auto
next
  case (NFadmit_Context \<sigma> \<phi> C) then
  have FA:"NFadmit \<sigma> \<phi>"
    and FUA:"FUadmitFO \<sigma> \<phi> UNIV"
    and IH:"fsafe \<phi> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>))"
      by auto
  have "fsafe (InContext C \<phi>) \<Longrightarrow>
           (\<And>i. dsafe (\<sigma> i))\<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) (InContext C \<phi>)))"
  proof -
    assume safe:"fsafe (InContext C \<phi>)"
    then have fsafe:"fsafe \<phi>" by (auto dest: fsafe.cases)
    assume ssafe:"\<And>i. dsafe (\<sigma> i)"
    fix \<nu>
    have Ieq:" Contexts (adjointFO I \<sigma> \<nu>) C = Contexts I C"
      unfolding adjointFO_def by auto
    have IH':"\<And>\<nu>. (\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>)"
      using IH[OF fsafe ssafe] by auto
    have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
    have adj_eq:"\<And>\<omega>. fml_sem (adjointFO I \<sigma> \<nu>) \<phi> = fml_sem (adjointFO I \<sigma> \<omega>) \<phi>"
      using uadmit_fml_ntadjoint[OF FUA agree ssafe fsafe good_interp] by auto
    then have sem:"fml_sem I (FsubstFO \<phi> \<sigma>) =  fml_sem (adjointFO I \<sigma> \<nu>) \<phi>"
      using IH' agree adj_eq by auto
    show "?thesis \<nu>"  using Ieq sem by auto
  qed
  then show ?case by auto
qed (auto)

lemma nsubst_fml:
  fixes I::"interp"
  fixes \<nu>::"state"
  assumes good_interp:"is_interp I"
  assumes NFA:"NFadmit \<sigma> \<phi>"
  assumes fsafe:"fsafe \<phi>"
  assumes frees:"(\<forall>i. dsafe (\<sigma> i))"
  shows "(\<nu> \<in> fml_sem I (FsubstFO \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjointFO I \<sigma> \<nu>) \<phi>)"
  using good_interp NFA fsafe frees 
  by (auto simp add: nsubst_hp_fml)

lemma nsubst_hp:
  fixes I::"interp"
  fixes \<nu>::"state"
  assumes good_interp:"is_interp I"    
  assumes NPA:"NPadmit \<sigma> \<alpha>"
  assumes hpsafe:"hpsafe \<alpha>"
  assumes frees:"\<And>i. dsafe (\<sigma> i)"
  shows "((\<nu>, \<omega>) \<in> prog_sem I (PsubstFO \<alpha> \<sigma>)) = ((\<nu>, \<omega>) \<in>  prog_sem (adjointFO I \<sigma> \<nu>) \<alpha>)"
 using good_interp NPA hpsafe frees nsubst_hp_fml by blast

lemma psubst_sterm:
  fixes I::"interp"
  assumes good_interp:"is_interp I"    
  shows "(sterm_sem I \<theta> = sterm_sem (PFadjoint I \<sigma>) \<theta>)"
proof (induction \<theta>)
qed (auto simp add: PFadjoint_def)

lemma psubst_dterm:
  fixes I::"interp"
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
    
lemma psubst_ode:
assumes good_interp:"is_interp I"
shows "ODE_sem I ODE = ODE_sem (PFadjoint I \<sigma>) ODE"
proof (induction "ODE")
  case (OVar x sp)
  then show ?case unfolding PFadjoint_def 
    apply(cases sp,auto)
     apply(rule ext, rule vec_extensionality,auto)
    by(rule ext, rule vec_extensionality,auto)
next
  case (OSing x1a x2)
  then show ?case apply auto apply (rule ext) apply (rule vec_extensionality) using psubst_sterm[OF good_interp, of x2 \<sigma>]  by auto 
next
  case (OProd ODE1 ODE2)
  then show ?case by auto
qed
  
lemma psubst_fml:
fixes I::"interp"
assumes good_interp:"is_interp I"    
shows "(PPadmit \<sigma> \<alpha>  \<longrightarrow> hpsafe \<alpha> \<longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<longrightarrow> (\<forall> \<nu> \<omega>. (\<nu>,\<omega>) \<in> prog_sem I (PPsubst \<alpha> \<sigma>) = ((\<nu>,\<omega>) \<in> prog_sem (PFadjoint I \<sigma>) \<alpha>))) \<and> 
  (PFadmit \<sigma> \<phi> \<longrightarrow> fsafe \<phi> \<longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<longrightarrow> (\<forall> \<nu>. \<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>)))"
proof (induction rule: PPadmit_PFadmit.induct)
  case (PPadmit_ODE \<sigma> \<phi> ODE)
  assume PF:"PFadmit \<sigma> \<phi>"
  assume PFU:"PFUadmit \<sigma> \<phi> (BVO ODE)"
  assume IH:"fsafe \<phi> \<longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<longrightarrow> (\<forall>\<nu>. (\<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>))"
  have "hpsafe (EvolveODE ODE \<phi>) \<Longrightarrow>
  (\<forall>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (EvolveODE ODE \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (EvolveODE ODE \<phi>)))"
  proof -
    assume safe:"hpsafe (EvolveODE ODE \<phi>)"
    from safe have fsafe:"fsafe \<phi>" by auto
    assume ssafe:"(\<forall>i. fsafe (\<sigma> i))"
    have fml_eq:"\<And>\<nu>. (\<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>)"
      using IH ssafe fsafe by auto
    fix \<nu> \<omega>
    show "((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (EvolveODE ODE \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (EvolveODE ODE \<phi>))"
      apply auto
    proof -
      fix b sol t
      assume eq1:"\<nu> = (sol 0, b)"
        and eq2:"\<omega> = mk_v I ODE (sol 0, b) (sol t)"
        and t:"0 \<le> t"
        and sol:"(sol solves_ode (\<lambda>a. ODE_sem I ODE)) {0..t} {x. mk_v I ODE (sol 0, b) x \<in> fml_sem I (PFsubst \<phi> \<sigma>)}"
      have var:"ODE_vars I ODE =  ODE_vars (PFadjoint I \<sigma>) ODE"
        by(induction ODE, auto simp add: PFadjoint_def)
      have mkv_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v I ODE (sol 0, b) (sol s) = mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) (sol s)"
        apply(rule agree_UNIV_eq)
        unfolding Vagree_def apply auto
         subgoal for s i
           using mk_v_agree[of I ODE "(sol 0, b)" "sol s"] mk_v_agree[of "PFadjoint I \<sigma>" ODE "(sol 0, b)" "sol s"]
           unfolding Vagree_def var 
           apply (cases "Inl i \<in> Inl ` ODE_vars I ODE", auto simp add: var)
            by force
        subgoal for s i
          using mk_v_agree[of I ODE "(sol 0, b)" "sol s"] mk_v_agree[of "PFadjoint I \<sigma>" ODE "(sol 0, b)" "sol s"]
          unfolding Vagree_def var 
          apply (cases "Inr i \<in> Inr ` ODE_vars I ODE", auto simp add: var psubst_ode)
           using psubst_ode[OF good_interp, of ODE \<sigma>] apply auto
          using psubst_ode[OF good_interp, of ODE \<sigma>] by force
        done
      have sol':"(sol solves_ode (\<lambda>_. ODE_sem (PFadjoint I \<sigma>) ODE)) {0..t}
       {x. mk_v I ODE (sol 0, b) x \<in> fml_sem I (PFsubst \<phi> \<sigma>)}"
        apply (rule solves_ode_congI)
            apply (rule sol)
           subgoal for ta by auto
          subgoal for ta using psubst_ode[OF good_interp, of ODE \<sigma>] by auto
         subgoal by (rule refl)
        subgoal by (rule refl)
        done
      have sub:"\<And>s. s \<in> {0..t} 
              \<Longrightarrow> sol s \<in> {x. (mk_v (PFadjoint I \<sigma> ) ODE (sol 0, b) x \<in> fml_sem (PFadjoint I \<sigma> ) \<phi>)}"
        subgoal for s
          using solves_ode_domainD[OF sol, of s] mkv_eq[of s] fml_eq[of "mk_v (PFadjoint I \<sigma> ) ODE (sol 0, b) (sol s)"]
          by auto
        done
      have sol'':"(sol solves_ode (\<lambda>c. ODE_sem (PFadjoint I \<sigma> ) ODE)) {0..t}
        {x. mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) x \<in> fml_sem (PFadjoint I \<sigma> ) \<phi>}"
        apply (rule solves_odeI)
         subgoal using sol' solves_ode_vderivD by blast
        using sub by auto          
      show"\<exists>sola. sol 0 = sola 0 \<and>
          (\<exists>ta. mk_v I ODE (sol 0, b) (sol t) = mk_v (PFadjoint I \<sigma>) ODE (sola 0, b) (sola ta) \<and>
                0 \<le> ta \<and>
                (sola solves_ode (\<lambda>a. ODE_sem (PFadjoint I \<sigma>) ODE)) {0..ta}
               {x. mk_v (PFadjoint I \<sigma>) ODE (sola 0, b) x \<in> fml_sem (PFadjoint I \<sigma>) \<phi>})"
        apply(rule exI[where x=sol])
        apply(rule conjI)
         apply(rule refl)
        apply(rule exI[where x=t])
        apply(rule conjI)
         subgoal using mkv_eq t by auto
        apply(rule conjI)
         apply(rule t)
        apply(rule sol'') 
        done
    next
      fix b sol t
      assume eq1:"\<nu> = (sol 0, b)"
        and eq2:"\<omega> = mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) (sol t)"
        and t:"0 \<le> t"
        and sol:"(sol solves_ode (\<lambda>a. ODE_sem (PFadjoint I \<sigma>) ODE)) {0..t} {x. mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) x \<in> fml_sem (PFadjoint I \<sigma>) \<phi>}"
      have var:"ODE_vars I ODE =  ODE_vars (PFadjoint I \<sigma>) ODE"
        by(induction ODE, auto simp add: PFadjoint_def)
      have mkv_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v I ODE (sol 0, b) (sol s) = mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) (sol s)"
        apply(rule agree_UNIV_eq)
        unfolding Vagree_def apply auto
         subgoal for s i
           using mk_v_agree[of I ODE "(sol 0, b)" "sol s"] mk_v_agree[of "PFadjoint I \<sigma>" ODE "(sol 0, b)" "sol s"]
           unfolding Vagree_def var 
           apply (cases "Inl i \<in> Inl ` ODE_vars I ODE", auto simp add: var)
            by force
        subgoal for s i
          using mk_v_agree[of I ODE "(sol 0, b)" "sol s"] mk_v_agree[of "PFadjoint I \<sigma>" ODE "(sol 0, b)" "sol s"]
          unfolding Vagree_def var 
          apply (cases "Inr i \<in> Inr ` ODE_vars I ODE", auto simp add: var psubst_ode)
           using psubst_ode[OF good_interp, of ODE \<sigma>] apply auto
          using psubst_ode[OF good_interp, of ODE \<sigma>] by force
        done
      have sol':"(sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t}
         {x. mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) x \<in> fml_sem (PFadjoint I \<sigma>) \<phi>}"
        apply (rule solves_ode_congI)
            apply (rule sol)
           subgoal for ta by auto
          subgoal for ta using psubst_ode[OF good_interp, of ODE \<sigma>] by auto
         subgoal by (rule refl)
        subgoal by (rule refl)
        done
      have sub:"\<And>s. s \<in> {0..t} 
              \<Longrightarrow> sol s \<in> {x. (mk_v  I ODE (sol 0, b) x \<in> fml_sem I (PFsubst \<phi> \<sigma>))}"
        subgoal for s
          using solves_ode_domainD[OF sol, of s] mkv_eq[of s] fml_eq[of "mk_v (PFadjoint I \<sigma> ) ODE (sol 0, b) (sol s)"]
          by auto
        done
      have sol'':"(sol solves_ode (\<lambda>c. ODE_sem I ODE)) {0..t}
        {x. mk_v I ODE (sol 0, b) x \<in> fml_sem I (PFsubst \<phi> \<sigma>)}"
        apply (rule solves_odeI)
         subgoal using sol' solves_ode_vderivD by blast
        using sub by auto
      show "\<exists>sola. sol 0 = sola 0 \<and>
          (\<exists>ta. mk_v (PFadjoint I \<sigma>) ODE (sol 0, b) (sol t) = mk_v I ODE (sola 0, b) (sola ta) \<and>
                0 \<le> ta \<and> (sola solves_ode (\<lambda>a. ODE_sem I ODE)) {0..ta} {x. mk_v I ODE (sola 0, b) x \<in> fml_sem I (PFsubst \<phi> \<sigma>)})"
        apply(rule exI[where x=sol])
        apply(rule conjI)
         apply(rule refl)
        apply(rule exI[where x=t])
        apply(rule conjI)
         subgoal using mkv_eq t by auto
        apply(rule conjI)
         apply(rule t)
        apply(rule sol'') 
        done
    qed
  qed
  then show ?case
    by auto
next
  case (PPadmit_Assign \<sigma> x \<theta>)
  have "hpsafe (x := \<theta>) \<Longrightarrow> (\<forall>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (x := \<theta>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (x := \<theta>)))"
  proof -
    assume safe:"hpsafe (x := \<theta>)"
    then have dsafe:"dsafe \<theta>" by auto
    assume safes:"(\<forall>i. fsafe (\<sigma> i))"
    show "?thesis"
      apply(auto)
       subgoal using psubst_dterm[OF good_interp dsafe, of \<sigma>] by auto
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
       subgoal using psubst_dterm[OF good_interp dsafe, of \<sigma>] by auto
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
    from safe have safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
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
  case (PPadmit_Sequence \<sigma> a b) then 
  have PUA:"PPUadmit \<sigma> b (BVP (PPsubst a \<sigma>))"
    and PA:"PPadmit \<sigma> a"
    and IH1:"hpsafe a \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) a))"
    and IH2:"hpsafe b \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<forall> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) b))"
    and substSafe:"hpsafe (PPsubst a \<sigma>)"
    by auto
  have "hpsafe (a ;; b) \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And> \<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a ;; b)))"
  proof -
    assume hpsafe:"hpsafe (a ;; b)"
    assume ssafe:"(\<And>i. fsafe (\<sigma> i))"
    from hpsafe have safe1:"hpsafe a" and safe2:"hpsafe b" by (auto dest: hpsafe.cases)
    fix \<nu> \<omega>
    have agree:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(PPsubst a \<sigma>))"
      subgoal for \<mu>
        using bound_effect[OF good_interp, of "(PPsubst a \<sigma>)" \<nu>, OF substSafe] by auto
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
  and substSafe:"hpsafe (PPsubst a \<sigma>)"   
    by auto
  have "hpsafe (a**) \<Longrightarrow> (\<And>i. fsafe (\<sigma> i)) \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (PPsubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (PFadjoint I \<sigma>) (a**)))"
  proof -
    assume "hpsafe (a**)"
    then have hpsafe:"hpsafe a" by (auto dest: hpsafe.cases)
    assume ssafe:"\<And>i. fsafe (\<sigma> i)"
    have agree:"\<And>\<nu> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (PPsubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(PPsubst a \<sigma>))"
      subgoal for \<nu> \<mu>
        using bound_effect[OF good_interp, of "(PPsubst a \<sigma>)" \<nu>, OF substSafe] by auto
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
    then have fsafe:"fsafe \<phi>" 
    and nb:"nonbase C" by auto
    assume ssafe:"(\<And>i. fsafe (\<sigma> i))"
    fix \<nu> :: "state"
    have IH':"\<And>\<nu>. (\<nu> \<in> fml_sem I (PFsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (PFadjoint I \<sigma>) \<phi>)"
      using IH[OF fsafe ssafe] by auto
    have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
    then have sem:"fml_sem I (PFsubst \<phi> \<sigma>) =  fml_sem (PFadjoint I \<sigma>) \<phi>"
      using IH' agree  by auto
    obtain inj where inj:"args_to_id C = Some (inj)" 
    using nb nonbase_some by fastforce
  then show "?thesis \<nu>" proof (cases inj)
    case (Inl a) assume a:"inj = Inl a" from a inj have "args_to_id C = Some (Inl a)" by auto
    then show ?thesis using sem unfolding PFadjoint_def by auto
  next
    case (Inr b) assume b:"inj = Inr b" from b inj have "args_to_id C = Some (Inr b)" by auto
    then show ?thesis using sem unfolding PFadjoint_def by auto
  qed
  qed
  then show ?case by auto
qed (auto simp add: PFadjoint_def)

lemma TUadmit_sub:
  assumes sub:"R \<subseteq> S"
  shows "TUadmit \<sigma> \<theta> S \<Longrightarrow> TUadmit \<sigma> \<theta> R"
  unfolding TUadmit_def using sub by auto
 

lemma Oadmit_sub:
  assumes sub:"R \<subseteq> S"
  shows "Oadmit \<sigma> ODE S  \<Longrightarrow> Oadmit \<sigma> ODE R"
proof (induction ODE)
  case (OVar x1 x2)
  then show ?case by(auto)
next
  case (OSing x1 x2)
  then show ?case using sub TUadmit_sub[OF sub] by(auto simp add: TUadmit_sub sub)
next
  case (OProd ODE1 ODE2)
  then show ?case by(auto)
qed
  

lemma subst_ode:
  fixes I:: "interp" and \<nu> :: "state"
  assumes good_interp:"is_interp I"
  shows "osafe ODE \<Longrightarrow> 
         ssafe \<sigma> \<Longrightarrow> 
         Oadmit \<sigma> ODE (BVO ODE) \<Longrightarrow>
         ODE_sem I (Osubst ODE \<sigma>) (fst \<nu>) = ODE_sem (adjoint I \<sigma> \<nu>) ODE (fst \<nu>)"
proof (induction rule: osafe.induct)
  case (osafe_Var c sp)
  assume  ssafe:"ssafe \<sigma>"
  and OA:"Oadmit \<sigma> (OVar c sp) (BVO (OVar c sp))"

  show ?case unfolding adjoint_def
    apply(cases sp)
    subgoal apply (cases "SODEs \<sigma> c All", auto)
    
    apply(rule vec_extensionality,auto)
      apply (cases "SODEs \<sigma> c All", auto)
      using OA apply(simp)
      using ODE_unbound_zero[OF good_interp] by blast
 proof -
     fix x2 i ::ident
     assume sp:"sp = Some x2"
     have odebv:"\<And>ode x. x \<notin> ODEBV I ode (Some x)" using good_interp unfolding is_interp_def by auto
     show "ODE_sem I (Osubst (OVar c sp) \<sigma>) (fst \<nu>) =
          ODE_sem \<lparr>Functions = \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' \<nu>,
                     Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem I f' R,
                     Predicates = \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. \<nu> \<in> fml_sem (extendf I R) p',
                     Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c',
                     Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x,
                     ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x,
                     ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr>
           (OVar c sp) (fst \<nu>)"
    subgoal apply (cases "SODEs \<sigma> c sp", auto)
    apply(rule vec_extensionality,auto)
      apply (cases "SODEs \<sigma> c sp", auto)
      using OA apply(simp)
      apply(auto)
       using ODE_unbound_zero[OF good_interp] by auto
     done
 qed
next
  case (osafe_Sing \<theta> x)
  then show ?case apply auto
    using subst_sterm [of  \<sigma> \<theta> I "\<nu>"]
    unfolding ssafe_def by (simp,metis  option.simps(5))+
next
  case (osafe_Prod ODE1 ODE2) then
  have NOU1:"Oadmit \<sigma> ODE1  (BVO (oprod ODE1 ODE2))" and NOU2:"Oadmit \<sigma> ODE2  (BVO (oprod ODE1 ODE2))" 
    by (auto simp add: BVO_assoc)
  have TUA_sub:"\<And>\<sigma> \<theta> A B. TUadmit \<sigma> \<theta> B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> TUadmit \<sigma> \<theta> A"
    unfolding TUadmit_def by auto
  have OA_sub:"\<And>ODE A B. Oadmit \<sigma> ODE B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Oadmit \<sigma> ODE A"
    subgoal for ODE A B
    proof (induction rule: Oadmit.induct)
      case (Oadmit_Var \<sigma> c U)
      then show ?case by auto
    next
      case (Oadmit_VarNB \<sigma> c x U)
      then show ?case by auto
    next
      case (Oadmit_Sing \<sigma> \<theta> U x)
      then show ?case using TUA_sub[of \<sigma> \<theta> U A] by auto
    next
      case (Oadmit_Prod \<sigma> ODE1 U ODE2)
      then show ?case by auto
    qed
    done
  have sub1:"(BVO ODE1) \<subseteq> (BVO (oprod ODE1 ODE2))"
    by (auto simp add: BVO_assoc)
  have sub2: "(BVO ODE2) \<subseteq> (BVO (oprod ODE1 ODE2))"
    by (auto simp add: BVO_assoc)
  have "ODE_sem I (Osubst ODE1 \<sigma>) (fst \<nu>) = ODE_sem (adjoint I \<sigma> \<nu>) ODE1 (fst \<nu>)"
    "ODE_sem I (Osubst ODE2 \<sigma>) (fst \<nu>) = ODE_sem (adjoint I \<sigma> \<nu>) ODE2 (fst \<nu>)" using osafe_Prod.IH osafe_Prod.prems osafe_Prod.hyps
    using OA_sub[OF NOU1 sub1] OA_sub[OF NOU2 sub2] 
    by(auto simp add: ODE_sem_assoc)
  then show ?case 
    by (auto simp add: ODE_sem_assoc)
qed

lemma osubst_eq_ODE_vars: "ODE_vars I (Osubst ODE \<sigma>) = ODE_vars (adjoint I \<sigma> \<nu>) ODE"
proof (induction ODE)
  case (OVar x x2)
  then show ?case
    by (cases "SODEs \<sigma> x x2", auto simp add: adjoint_def)
qed (auto simp add: ODE_vars_assoc)

lemma subst_semBV:"semBV (adjoint I \<sigma> \<nu>') ODE = (semBV I (Osubst ODE \<sigma>))"
proof (induction ODE)
  case (OVar x x2)
  then show ?case by (cases "SODEs \<sigma> x x2", auto simp add: adjoint_def)
  case (OProd ODE1 ODE2)
  then show ?case 
    by(auto simp add: ODE_vars_assoc) 
qed (auto)

lemma subst_mkv:
  fixes I::"interp"
  fixes \<nu>::"state"
  fixes \<nu>'::"state"
  assumes good_interp:"is_interp I"  
  assumes NOU:"Oadmit \<sigma> ODE (BVO ODE)"
  assumes osafe:"osafe ODE "
  assumes frees:"ssafe \<sigma>"
  shows "(mk_v I (Osubst ODE \<sigma>) \<nu> (fst \<nu>')) 
    = (mk_v (adjoint I \<sigma> \<nu>') ODE \<nu> (fst \<nu>'))"
  apply(rule agree_UNIV_eq)
  using mk_v_agree[of "adjoint I \<sigma> \<nu>'" "ODE" \<nu> "fst \<nu>'"]
  using mk_v_agree[of "I" "Osubst ODE \<sigma>" \<nu> "fst \<nu>'"] 
  unfolding Vagree_def 
  using subst_ode[OF good_interp osafe  frees NOU, of \<nu>'] 
  apply auto
   subgoal for i
     apply(erule allE[where x=i])+
     apply(cases "Inl i \<in> Inl ` ODE_vars (adjoint I \<sigma> \<nu>') ODE")
      using osubst_eq_ODE_vars[of I ODE \<sigma> \<nu>']
            apply force
   proof -
     assume "ODE_sem I (Osubst ODE \<sigma>) (fst \<nu>') = ODE_sem (adjoint I \<sigma> \<nu>') ODE (fst \<nu>')"
       "Inl i \<notin> Inl ` ODE_vars (adjoint I \<sigma> \<nu>') ODE \<and> Inl i \<notin> Inr ` ODE_vars (adjoint I \<sigma> \<nu>') ODE \<longrightarrow>
       fst (mk_v (adjoint I \<sigma> \<nu>') ODE \<nu> (fst \<nu>')) $ i = fst \<nu> $ i"
       "Inl i \<notin> Inl ` ODE_vars I (Osubst ODE \<sigma>) \<and> Inl i \<notin> Inr ` ODE_vars I (Osubst ODE \<sigma>) \<longrightarrow>
       fst (mk_v I (Osubst ODE \<sigma>) \<nu> (fst \<nu>')) $ i = fst \<nu> $ i"
       "Inl i \<notin> Inl ` ODE_vars (adjoint I \<sigma> \<nu>') ODE"
     then show
        "fst (mk_v I (Osubst ODE \<sigma>) \<nu> (fst \<nu>')) $ i = fst (mk_v (adjoint I \<sigma> \<nu>') ODE \<nu> (fst \<nu>')) $ i"
         using osubst_eq_ODE_vars[of I ODE \<sigma> \<nu>'] by force
   qed
  subgoal for i
    apply(erule allE[where x=i])+
    apply(cases "Inr i \<in> Inr ` ODE_vars (adjoint I \<sigma> \<nu>') ODE")
     using osubst_eq_ODE_vars[of I ODE \<sigma> \<nu>']
     apply force
  proof -
    assume "ODE_sem I (Osubst ODE \<sigma>) (fst \<nu>') = ODE_sem (adjoint I \<sigma> \<nu>') ODE (fst \<nu>')"
      "Inr i \<notin> Inl ` ODE_vars (adjoint I \<sigma> \<nu>') ODE \<and> Inr i \<notin> Inr ` ODE_vars (adjoint I \<sigma> \<nu>') ODE \<longrightarrow>
      snd (mk_v (adjoint I \<sigma> \<nu>') ODE \<nu> (fst \<nu>')) $ i = snd \<nu> $ i"
      "Inr i \<notin> Inl ` ODE_vars I (Osubst ODE \<sigma>) \<and> Inr i \<notin> Inr ` ODE_vars I (Osubst ODE \<sigma>) \<longrightarrow>
      snd (mk_v I (Osubst ODE \<sigma>) \<nu> (fst \<nu>')) $ i = snd \<nu> $ i"
      "Inr i \<notin> Inr ` ODE_vars (adjoint I \<sigma> \<nu>') ODE"
    then show "snd (mk_v I (Osubst ODE \<sigma>) \<nu> (fst \<nu>')) $ i = snd (mk_v (adjoint I \<sigma> \<nu>') ODE \<nu> (fst \<nu>')) $ i"
      using osubst_eq_ODE_vars[of I ODE \<sigma> \<nu>'] by force
  qed
  done

lemma subst_fml_hp:
  fixes I::"interp"
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
  have "hpsafe ($\<alpha> a) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst ($\<alpha> a) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) ($\<alpha> a)))"
    apply (cases "SPrograms \<sigma> a")
     unfolding adjoint_def by auto
  then show ?case by auto
next
  case (Padmit_Sequence \<sigma> a b) then 
  have PUA:"PUadmit \<sigma> b (BVP (Psubst a \<sigma>))"
    and PA:"Padmit \<sigma> a"
    and IH1:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a))"
    and IH2:"hpsafe b \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) b))"
    and substSafe:"hpsafe (Psubst a \<sigma>)"
    by auto
  have "hpsafe (a ;; b) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (a ;; b)))"
  proof -
    assume hpsafe:"hpsafe (a ;; b)"
    assume ssafe:"ssafe \<sigma>"
    from hpsafe have safe1:"hpsafe a" and safe2:"hpsafe b" by (auto dest: hpsafe.cases)
    fix \<nu> \<omega>
    have agree:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(Psubst a \<sigma>))"
      subgoal for \<mu>
        using bound_effect[OF good_interp, of "(Psubst a \<sigma>)" \<nu>, OF substSafe] by auto
      done
    have sem_eq:"\<And>\<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> 
        ((\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) b) =
        ((\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<mu>) b)"
      subgoal for \<mu>
      proof -
        assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>)"
        show "((\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) b) = ((\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<mu>) b)"
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
    show "((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a ;; b) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (a ;; b))"
      by auto
  qed
  then show ?case by auto
next
  case (Padmit_Loop \<sigma> a) then 
  have PA:"Padmit \<sigma> a"
    and PUA:"PUadmit \<sigma> a (BVP (Psubst a \<sigma>))"
    and IH:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a))"
    and substSafe:"hpsafe (Psubst a \<sigma>)"
    by auto
  have "hpsafe (a**) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (a**)))"
  proof -
    assume "hpsafe (a**)"
    then have hpsafe:"hpsafe a" by (auto dest: hpsafe.cases)
    assume ssafe:"ssafe \<sigma>"
    have agree:"\<And>\<nu> \<mu>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<mu> (-BVP(Psubst a \<sigma>))"
    subgoal for \<nu> \<mu>
      using bound_effect[OF good_interp, of "(Psubst a \<sigma>)" \<nu>, OF substSafe] by auto
    done
  have sem_eq:"\<And>\<nu> \<mu> \<omega>. (\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> 
      ((\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a) =
      ((\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<mu>) a)"
    subgoal for \<nu> \<mu> \<omega> 
    proof -
      assume assm:"(\<nu>, \<mu>) \<in> prog_sem I (Psubst a \<sigma>)"
      show "((\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a) = ((\<mu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<mu>) a)"
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
      have IH2:"\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>) ^^ n) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a ^^ n)"
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
  ultimately show "((\<nu>, \<omega>) \<in> prog_sem I (Psubst (a**) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (a**))"
    by auto
   qed
  then show ?case by auto
next
  let ?Set =  "\<lambda>\<theta>. (\<Union>i\<in>SIGT \<theta>. (case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<union> (case SFunls \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x))"
  case (Padmit_ODE \<sigma> ODE \<phi>) then
  have OA:"Oadmit \<sigma> ODE (BVO ODE)"
    and FA:"Fadmit \<sigma> \<phi>"
    and FUA:"FUadmit \<sigma> \<phi> (BVO ODE)"
    and IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
      by auto
  have "hpsafe (EvolveODE ODE \<phi>) \<Longrightarrow>
     ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (EvolveODE ODE \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (EvolveODE ODE \<phi>)))"
  proof (auto)
    fix aa ba bb
      and sol :: "real \<Rightarrow>(real, ident) vec" 
      and t :: real
    assume ssafe:"ssafe \<sigma>"
    assume osafe:"osafe ODE"
    assume fsafe:"fsafe \<phi>"
    assume t:"0 \<le> t"
    assume eq:"(aa,ba) = mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol t)"
    assume sol:"(sol solves_ode (\<lambda>a. ODE_sem I (Osubst ODE \<sigma>))) {0..t} 
      {x. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) x \<in> fml_sem I (Fsubst \<phi> \<sigma>)}"
    have silly:"
      \<And>t. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol t) = mk_v (adjoint I \<sigma> (sol t, bb)) ODE (sol 0, bb) (sol t)"
      subgoal for t using subst_mkv[OF good_interp OA osafe ssafe, of "(sol 0, bb)" "(sol t, bb)"] by auto done
    have hmmsubst:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,bb) (sol s, bb) (-(BVO (Osubst ODE \<sigma>)))"
      subgoal for s
        apply (rule ODE_bound_effect[of ]) apply(rule good_interp)
         apply auto[1]  
        by (rule sol)
      done
    have sub:"Oadmit \<sigma> ODE (BVO ODE) \<Longrightarrow> (-(BVO ODE)) \<subseteq> (-(BVO (Osubst ODE \<sigma>)))"
    proof(induction ODE)
      case (OVar x1 x2)
      assume theu:" Oadmit \<sigma> (OVar x1 x2) (BVO (OVar x1 x2))"
      have foo:"\<And>ode x. x \<notin> ODEBV I ode (Some x)" using good_interp unfolding is_interp_def by auto
      show ?case apply(cases x2,auto simp add: BVO_assoc, cases "SODEs \<sigma> x1 x2",auto)
        subgoal for x2a y
         using foo[of x2a x1]    
         good_interp unfolding is_interp_def using theu  Oadmit_Var_simps option.distinct(1) option.inject
         by (simp add: \<open>x2a \<notin> ODEBV I x1 (Some x2a)\<close>)
       subgoal for x2a
         apply(cases "SODEs \<sigma> x1 (Some x2a)",auto)
       proof -
         fix a:: "ODE"
         assume nb:"x2 = Some x2a"
         assume inr:"Inr x2a \<in> BVO a"
         assume some:"SODEs \<sigma> x1 (Some x2a)= Some a"
         show False
           using theu nb inr some BVO_lr[of x2a a] by(auto simp add: Oadmit_Var_simps)
       qed
     done
    next
      case (OSing x1 x2)
      then show ?case by(auto simp add: BVO_assoc)
    next
      case (OProd ODE1 ODE2)
        assume IH1:"Oadmit \<sigma> ODE1 (BVO ODE1) \<Longrightarrow> - BVO ODE1 \<subseteq> - BVO (Osubst ODE1 \<sigma>)"
        assume IH2:"Oadmit \<sigma> ODE2 (BVO ODE2) \<Longrightarrow> - BVO ODE2 \<subseteq> - BVO (Osubst ODE2 \<sigma>)"
        assume O:"Oadmit \<sigma> (OProd ODE1 ODE2) (BVO (OProd ODE1 ODE2))"
        have O1:"Oadmit \<sigma> ODE1 (BVO ODE1)" 
          apply(rule  Oadmit_sub[where S="BVO (OProd ODE1 ODE2)"])
          using O by auto
        have O2:"Oadmit \<sigma> ODE2 (BVO ODE2)" 
          apply(rule  Oadmit_sub[where S="BVO (OProd ODE1 ODE2)"])
          using O by auto
        then show ?case 
          using IH1 IH2 O1 O2
          by(auto simp add: ODE_vars_assoc BVO_assoc) 
    qed
    have hmm:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,bb) (sol s, bb) (-(BVO ODE))"
      subgoal for s
        using agree_sub[OF sub hmmsubst[of s]] OA by auto
      done
    from hmm have hmm':"\<And>s. s \<in> {0..t} \<Longrightarrow> VSagree (sol 0) (sol s) {x. Inl x \<in> (-(BVO ODE))}"
      unfolding VSagree_def Vagree_def by auto
    note hmmm = hmmsubst
    from hmmm have hmmm':"\<And>s. s \<in> {0..t} \<Longrightarrow> VSagree (sol 0) (sol s) {x. Inl x \<in> (-(BVO (Osubst ODE \<sigma>)))}"
      unfolding VSagree_def Vagree_def by auto
    have Vagree_of_VSagree:"\<And>\<nu>1 \<nu>2 \<omega>1 \<omega>2 S. VSagree \<nu>1 \<nu>2 {x. Inl x \<in> S} \<Longrightarrow> VSagree \<omega>1 \<omega>2 {x. Inr x \<in> S} \<Longrightarrow> Vagree (\<nu>1, \<omega>1) (\<nu>2, \<omega>2) S"
      unfolding VSagree_def Vagree_def by auto
    have mkv:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol s, bb)) ODE (sol 0, bb) (sol s)"
      subgoal for s by (rule silly[of s])
      done
    have lem:"\<And>ODE. Oadmit \<sigma> ODE (BVO ODE) \<Longrightarrow> 
\<^cancel>\<open>   (\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)\<close>
   (OSigSet \<sigma> ODE) \<subseteq> (-(BVO ODE))"
      subgoal for ODE
        apply(induction rule: Oadmit.induct)
        subgoal for \<sigma> c U 
          unfolding OSigSet_def by auto
        subgoal for \<sigma> c U  x
          unfolding OSigSet_def by auto
        subgoal for \<sigma> \<theta> U x 
          apply(auto simp add: OSigSet_def)
          subgoal for y ya
          apply (cases "SFunctions \<sigma> ya")
           apply auto
          unfolding TUadmit_def
        proof -
          fix a
          assume un:"(\<Union>i\<in>SIGT \<theta>. (case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<union> (case SFunls \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)) \<inter> U = {}"
          assume sig:"ya \<in> SIGT \<theta>"
          assume some:"SFunctions \<sigma> ya = Some a"
          assume fvt:"y \<in> FVT a"
          assume xU:"y \<in> U"
          from un sig have "((\<Union>i\<in>SIGT \<theta>. (case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<union> (case SFunls \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)) ) \<inter> U = {}"
            by auto 
          then have "(FVT a) \<inter> U = {}"
            using some 
            apply(auto) 
            using sig by fastforce
          then show "False" using fvt xU by auto
        qed
        done
      subgoal for \<sigma> ODE1 U ODE2
        by(auto simp add: OSigSet_def)
      done
        done
    have FVT_sub:"(OSigSet \<sigma> ODE) \<subseteq> (-(BVO ODE))"
      using lem[OF OA] unfolding OSigSet_def by auto
    have agrees: "\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,bb) (sol s, bb) (OSigSet \<sigma> ODE)\<^cancel>\<open>(\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)\<close>"
       subgoal for s using agree_sub[OF FVT_sub hmm[of s]] by auto done
    have "\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjoint I \<sigma> (sol 0, bb)) ODE = mk_v (adjoint I \<sigma> (sol s, bb)) ODE"
      subgoal for s         
        apply (rule uadmit_mkv_adjoint)
           prefer 3       
          subgoal using agrees by auto
         using OA hmm[of s] unfolding  Vagree_def
        using ssafe good_interp osafe by auto
      done
    then have mkva:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjoint I \<sigma> (sol s, bb)) ODE (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s)"
      by presburger
    have main_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow>  mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s) "
      using mkv mkva by auto
    note mkvt = main_eq[of t]
    have fml_eq1:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
        (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem I (Fsubst \<phi> \<sigma>)) 
      = (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi>)"
      using IH[OF fsafe ssafe] by auto
    have fml_vagree:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- semBV I (Osubst ODE \<sigma>))"
      subgoal for s
        using mk_v_agree[of I "Osubst ODE \<sigma>" "(sol 0,bb)" "sol s"] osubst_eq_ODE_vars[of I ODE \<sigma>]
        unfolding Vagree_def
        by auto
      done
    have sembv_eq:"semBV I (Osubst ODE \<sigma>) = semBV (adjoint I \<sigma> (sol 0, bb)) ODE"
      using subst_semBV by auto
    have fml_vagree':"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- semBV (adjoint I \<sigma> (sol 0,bb)) ODE)"
      using sembv_eq fml_vagree by auto
    have mysub:"Oadmit \<sigma> ODE (BVO ODE) \<Longrightarrow> -BVO ODE \<subseteq> -(semBV I (Osubst ODE \<sigma>))"
(*    have sub:"Oadmit \<sigma> ODE (BVO ODE) \<Longrightarrow> (-(BVO ODE)) \<subseteq> (-(BVO (Osubst ODE \<sigma>)))"*)
    proof(induction ODE)
      case (OVar x1 x2)
      assume theu:" Oadmit \<sigma> (OVar x1 x2) (BVO (OVar x1 x2))"
      have foo:"\<And>ode x. x \<notin> ODEBV I ode (Some x)" using good_interp unfolding is_interp_def by auto
      show ?case apply(cases x2,auto simp add: BVO_assoc, cases "SODEs \<sigma> x1 x2",auto)
        subgoal for x2a 
         using foo[of x2a x1]    
         good_interp unfolding is_interp_def using theu  Oadmit_Var_simps option.distinct(1) option.inject
         by smt
       subgoal for x a
         apply(cases "SODEs \<sigma> x1 x2",auto)
       proof -
(*         fix a:: "ODE"*)
         assume nb:"x2 = Some x"
         assume inr:"x \<in> ODE_vars I a"
         assume some:"SODEs \<sigma> x1 (Some x) = Some a"
         have bvo:"(Inl x \<notin> BVO a)"
           using some theu nb by auto
         show False
           using inr bvo good_interp ODE_vars_sub_BVO_inl by auto
       qed
       subgoal for x 
         apply(cases "SODEs \<sigma> x1 x2",auto)
         subgoal using good_interp unfolding is_interp_def by auto
       proof -
         fix a:: "ODE"
         assume nb:"x2 = Some x"
         assume inr:"x \<in> ODE_vars I a"
         assume some:"SODEs \<sigma> x1 (Some x)= Some a"
         have bvo:"(Inl x \<notin> BVO a)"
           using some theu nb by auto
         show False
           using inr bvo good_interp ODE_vars_sub_BVO_inl by auto
       qed
     done
    next
      case (OSing x1 x2)
      then show ?case by(auto simp add: BVO_assoc)
    next
      case (OProd ODE1 ODE2)
        assume IH1:"Oadmit \<sigma> ODE1 (BVO ODE1) \<Longrightarrow> - BVO ODE1 \<subseteq> - semBV I (Osubst ODE1 \<sigma>)"
        assume IH2:"Oadmit \<sigma> ODE2 (BVO ODE2) \<Longrightarrow> - BVO ODE2 \<subseteq> - semBV I (Osubst ODE2 \<sigma>)"
        assume O:"Oadmit \<sigma> (OProd ODE1 ODE2) (BVO (OProd ODE1 ODE2))"
        have O1:"Oadmit \<sigma> ODE1 (BVO ODE1)" 
          apply(rule  Oadmit_sub[where S="BVO (OProd ODE1 ODE2)"])
          using O by auto
        have O2:"Oadmit \<sigma> ODE2 (BVO ODE2)" 
          apply(rule  Oadmit_sub[where S="BVO (OProd ODE1 ODE2)"])
          using O by auto
        then show ?case 
          using IH1 IH2 O1 O2
            by(auto simp add: ODE_vars_assoc) 
    qed


    have fml_vagree:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- BVO ODE)"
      subgoal for s using agree_sub[OF mysub fml_vagree[of s]] OA by auto done
    have fml_sem_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi> = fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>"
      apply (rule uadmit_fml_adjoint)
          using FUA fsafe ssafe  good_interp fml_vagree by auto
    have fml_eq2:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
      ((mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi>)
      =(mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>))"
      using fml_sem_eq by auto
    have fml_eq3:"\<And>s. s \<in> {0..t} \<Longrightarrow>
      (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>) = (mk_v (adjoint I \<sigma> (sol 0,bb)) ODE (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>) "
      using main_eq by auto
    have fml_eq: "\<And>s. s \<in> {0..t} \<Longrightarrow>
      (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem I (Fsubst \<phi> \<sigma>)) 
       =  (mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>)"
      using fml_eq1 fml_eq2 fml_eq3 by meson
    have sem_eq:"\<And>t. ODE_sem I (Osubst ODE \<sigma>) (sol t) = ODE_sem (adjoint I \<sigma> (sol t, bb)) ODE (sol t)"
      subgoal for t
        using subst_ode[OF good_interp osafe ssafe OA, of "(sol t,bb)"] by auto
      done
    have sem_fact:"\<And>s. s \<in> {0..t} \<Longrightarrow> ODE_sem I (Osubst ODE \<sigma>) (sol s) = ODE_sem (adjoint I \<sigma> (sol 0, bb)) ODE (sol s)"
      subgoal for s
        using subst_ode[OF good_interp osafe ssafe OA, of "(sol s, bb)"]
        uadmit_ode_adjoint'[OF ssafe good_interp agrees[of s] osafe] 
        by auto
      done
    have sol':"(sol solves_ode (\<lambda>_. ODE_sem (adjoint I \<sigma> (sol 0, bb)) ODE)) {0..t}
       {x. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) x \<in> fml_sem I (Fsubst \<phi> \<sigma>)}"
      apply (rule solves_ode_congI)
          apply (rule sol)
         subgoal for ta by auto
        subgoal for ta by (rule sem_fact[of ta])
       subgoal by (rule refl)
      subgoal by (rule refl)
      done
    have sub:"\<And>s. s \<in> {0..t} 
            \<Longrightarrow> sol s \<in> {x. (mk_v (adjoint I \<sigma> (sol 0,bb)) ODE (sol 0, bb) x \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>)}"
      using fml_eq rangeI t sol solves_ode_domainD by fastforce
    have sol'':"(sol solves_ode (\<lambda>c. ODE_sem (adjoint I \<sigma> (sol 0, bb)) ODE)) {0..t}
{x. mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) x \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>}"
      apply (rule solves_odeI)
       subgoal using sol' solves_ode_vderivD by blast
      using sub by auto
    show "\<exists>sola. sol 0 = sola 0 \<and>
      (\<exists>ta. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol t) = mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sola 0, bb) (sola ta) \<and>
            0 \<le> ta \<and>
            (sola solves_ode (\<lambda>a. ODE_sem (adjoint I \<sigma> (sol 0, bb)) ODE)) {0..ta}
             {x. mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sola 0, bb) x \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>})"
    apply(rule exI[where x=sol])
    apply(rule conjI)
     subgoal by (rule refl)
    apply(rule exI[where x=t])
    apply(rule conjI)
     subgoal using  mkvt t by auto
    apply(rule conjI)
     subgoal by (rule t)
    subgoal by (rule sol'') 
    done
  next
    fix aa ba bb 
      and sol::"real \<Rightarrow> (real, ident) vec" 
      and t::real
    assume ssafe:"ssafe \<sigma>"
    assume osafe:"osafe ODE"
    assume fsafe:"fsafe \<phi>"
    from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
        "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      "(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"
        unfolding ssafe_def by (metis option.simps(5))+
    have good_adjoint:"is_interp (adjoint I \<sigma> (sol 0, bb))" 
      apply(rule adjoint_safe) apply(rule good_interp) using ssafe  ssafes   by auto
    assume eq:"(aa,ba) = mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol t)"
    assume t:"0 \<le> t"
    assume sol:"(sol solves_ode (\<lambda>a. ODE_sem (adjoint I \<sigma> (sol 0, bb)) ODE)) {0..t}
    {x. mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) x \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>}"
    have silly:"
      \<And>t. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol t) = mk_v (adjoint I \<sigma> (sol t, bb)) ODE (sol 0, bb) (sol t)"
      subgoal for t using subst_mkv[OF good_interp OA osafe ssafe, of "(sol 0, bb)" "(sol t, bb)"] by auto done
    have hmm:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,bb) (sol s, bb) (-(BVO ODE))"
      subgoal for s
        apply (rule ODE_bound_effect[of "(adjoint I \<sigma> (sol 0,bb))"]) apply(rule good_adjoint)
         apply auto[1]
        using  sol apply auto done
      done
    from hmm have hmm':"\<And>s. s \<in> {0..t} \<Longrightarrow> VSagree (sol 0) (sol s) {x. Inl x \<in> (-(BVO ODE))}"
      unfolding VSagree_def Vagree_def by auto
    have Vagree_of_VSagree:"\<And>\<nu>1 \<nu>2 \<omega>1 \<omega>2 S. VSagree \<nu>1 \<nu>2 {x. Inl x \<in> S} \<Longrightarrow> VSagree \<omega>1 \<omega>2 {x. Inr x \<in> S} \<Longrightarrow> Vagree (\<nu>1, \<omega>1) (\<nu>2, \<omega>2) S"
      unfolding VSagree_def Vagree_def by auto
    have mkv:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol s, bb)) ODE (sol 0, bb) (sol s)"
      subgoal for s by (rule silly[of s])
      done
    have lem:"\<And>ODE. Oadmit \<sigma> ODE (BVO ODE) \<Longrightarrow> \<^cancel>\<open>(\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)\<close> (OSigSet \<sigma> ODE) \<subseteq> (-(BVO ODE))"
      subgoal for ODE
        apply(induction rule: Oadmit.induct)
        apply (auto simp add: OSigSet_def)
        subgoal for \<sigma> \<theta> U x xa
        apply (cases "SFunctions \<sigma> xa")
         apply auto
        unfolding TUadmit_def
     proof -
       fix a
       assume un:"(\<Union>i\<in>SIGT \<theta>. (case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<union> (case SFunls \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)) \<inter> U = {}"
       assume sig:"xa \<in> SIGT \<theta>"
       assume some:"SFunctions \<sigma> xa = Some a"
       assume fvt:"x \<in> FVT a"
       assume xU:"x \<in> U"
       from un sig have "(case SFunctions \<sigma> xa of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<inter> U = {}"
         by auto 
       then have "(FVT a) \<inter> U = {}"
        using some by auto
      then show "False" using fvt xU by auto
    qed
    done
  done
(*        subgoal for \<sigma> \<theta> U x xa
        apply (cases "SFunls \<sigma> xa")
         apply auto
          unfolding TUadmit_def
  proof -
       fix a
       assume un:"(\<Union>i\<in>SIGT \<theta>. (case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<union> (case SFunls \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)) \<inter> U = {}"
       assume sig:"xa \<in> SIGT \<theta>"
       assume some:"SFunls \<sigma> xa = Some a"
       assume fvt:"x \<in> FVT a"
       assume xU:"x \<in> U"
       from un sig have "(case SFunls \<sigma> xa of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x) \<inter> U = {}"
         by auto 
       then have "(FVT a) \<inter> U = {}"
        using some by auto
      then show "False" using fvt xU by auto
     qed
       done
     done*)
    have FVT_sub:"OSigSet \<sigma> ODE \<^cancel>\<open>(\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)\<close> \<subseteq> (-(BVO ODE))"
      using lem[OF OA] by auto
    have agrees: "\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (sol 0,bb) (sol s, bb) (OSigSet \<sigma> ODE) \<^cancel>\<open>(\<Union>i\<in>{i |i. Inl i \<in> SIGO ODE}. case SFunctions \<sigma> i of None \<Rightarrow> {} | Some x \<Rightarrow> FVT x)\<close>"
       subgoal for s using agree_sub[OF FVT_sub hmm[of s]] by auto done
    have "\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjoint I \<sigma> (sol 0, bb)) ODE = mk_v (adjoint I \<sigma> (sol s, bb)) ODE"
      subgoal for s         
        apply (rule uadmit_mkv_adjoint)
           prefer 3
          subgoal using agrees by auto
         using OA hmm[of s] unfolding  Vagree_def
        using ssafe good_interp osafe by auto
      done
    then have mkva:"\<And>s. s \<in> {0..t} \<Longrightarrow> mk_v (adjoint I \<sigma> (sol s, bb)) ODE (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s)"
      by presburger
    have main_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow>  mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) = mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s) "
      using mkv mkva by auto
    note mkvt = main_eq[of t]
    have fml_eq1:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
        (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem I (Fsubst \<phi> \<sigma>)) 
      = (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi>)"
      using IH[OF fsafe ssafe] by auto
    have fml_vagree:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- semBV I (Osubst ODE \<sigma>))"
      subgoal for s
        using mk_v_agree[of I "Osubst ODE \<sigma>" "(sol 0,bb)" "sol s"] osubst_eq_ODE_vars[of I ODE \<sigma>]
        unfolding Vagree_def
        by auto
      done
    have sembv_eq:"semBV I (Osubst ODE \<sigma>) = semBV (adjoint I \<sigma> (sol 0, bb)) ODE"
      using subst_semBV by auto
    have fml_vagree':"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- semBV (adjoint I \<sigma> (sol 0,bb)) ODE)"
      using sembv_eq fml_vagree by auto
    have mysub:"Oadmit \<sigma> ODE (BVO ODE) \<Longrightarrow> -BVO ODE \<subseteq> -(semBV I (Osubst ODE \<sigma>))"
    proof(induction ODE)
      case (OVar x1 x2)
      then show ?case apply(cases x2)
        subgoal by auto
        subgoal for x2a
          apply(cases "SODEs \<sigma> x1 x2")
          subgoal by auto 
        proof -
          fix a:: "ODE"
          assume OA:"Oadmit \<sigma> (OVar x1 x2) (BVO (OVar x1 x2))"
          assume some:"SODEs \<sigma> x1 x2= Some a"
          assume nb:"x2 = Some x2a"
         show "- BVO (OVar x1 x2) \<subseteq> - semBV I (Osubst (OVar x1 x2) \<sigma>)"
           using   some 
           using ODE_vars_sub_BVO_inl[OF good_interp, of "OVar x1 x2"]  
            ODE_vars_assoc  nb  some BVO_lr[of x2a a] OA
           apply(auto simp add: Oadmit_Var_simps  ODE_vars_sub_BVO_inl[OF good_interp, of "OVar x1 x2"]  
            ODE_vars_assoc  nb  some BVO_lr[of x2a a] OA)
         proof -
           assume odebv:"Inl ` ODEBV I x1 (Some x2a) \<subseteq> - {Inl x2a, Inr x2a}"
           assume inr:"Inr x2a \<notin> BVO a"
           assume odev:"x2a \<in> ODE_vars I a"
           show False using
             ODE_vars_sub_BVO_inr[OF good_interp, of "a"] inr odev by auto
         next
           assume odebv:"Inl ` ODEBV I x1 (Some x2a) \<subseteq> - {Inl x2a, Inr x2a}"
           assume inr:"Inr x2a \<notin> BVO a"
           assume odev:"x2a \<in> ODE_vars I a"
           show False using
             ODE_vars_sub_BVO_inr[OF good_interp, of "a"] inr odev by auto
         qed
       qed done
    next
      case (OSing x1 x2)
      then show ?case by(auto simp add: ODE_vars_assoc)
    next
      case (OProd ODE1 ODE2)
        assume IH1:"Oadmit \<sigma> ODE1 (BVO ODE1) \<Longrightarrow> - BVO ODE1 \<subseteq> - semBV I (Osubst ODE1 \<sigma>)"
        assume IH2:"Oadmit \<sigma> ODE2 (BVO ODE2) \<Longrightarrow> - BVO ODE2 \<subseteq> - semBV I (Osubst ODE2 \<sigma>)"
        assume O:"Oadmit \<sigma> (OProd ODE1 ODE2) (BVO (OProd ODE1 ODE2))"
        have O1:"Oadmit \<sigma> ODE1 (BVO ODE1)" 
          apply(rule  Oadmit_sub[where S="BVO (OProd ODE1 ODE2)"])
          using O by auto
        have O2:"Oadmit \<sigma> ODE2 (BVO ODE2)" 
          apply(rule  Oadmit_sub[where S="BVO (OProd ODE1 ODE2)"])
          using O by auto
        then show ?case 
          using IH1 IH2 O1 O2
            by(auto simp add: ODE_vars_assoc) 
    qed
    have fml_vagree:"\<And>s. s \<in> {0..t} \<Longrightarrow> Vagree (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s)) (sol 0, bb) (- BVO ODE)"
      subgoal for s using agree_sub[OF mysub fml_vagree[of s]] OA apply auto done done
    have fml_sem_eq:"\<And>s. s \<in> {0..t} \<Longrightarrow> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi> = fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>"
      apply (rule uadmit_fml_adjoint)
      using FUA fsafe ssafe  good_interp fml_vagree by auto
    have fml_eq2:"\<And>s. s \<in> {0..t} \<Longrightarrow> 
      ((mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s))) \<phi>)
      =(mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>))"
      using fml_sem_eq by auto
    have fml_eq3:"\<And>s. s \<in> {0..t} \<Longrightarrow>
        (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>) = (mk_v (adjoint I \<sigma> (sol 0,bb)) ODE (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>) "
      using main_eq by auto
    have fml_eq: "\<And>s. s \<in> {0..t} \<Longrightarrow>
         (mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem I (Fsubst \<phi> \<sigma>)) 
          =  (mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol s) \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>)"
         using fml_eq1 fml_eq2 fml_eq3 by meson
    have sem_eq:"\<And>t. ODE_sem I (Osubst ODE \<sigma>) (sol t) = ODE_sem (adjoint I \<sigma> (sol t, bb)) ODE (sol t)"
      subgoal for t
        using subst_ode[OF good_interp osafe ssafe OA, of "(sol t,bb)"] by auto
      done
    have sem_fact:"\<And>s. s \<in> {0..t} \<Longrightarrow> ODE_sem I (Osubst ODE \<sigma>) (sol s) = ODE_sem (adjoint I \<sigma> (sol 0, bb)) ODE (sol s)"
      subgoal for s
        using subst_ode[OF good_interp osafe ssafe OA, of "(sol s, bb)"]
        uadmit_ode_adjoint'[OF ssafe good_interp agrees[of s] osafe] 
        by auto
      done
    have sub:"\<And>s. s \<in> {0..t} 
            \<Longrightarrow> sol s \<in> {x. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) (sol s) \<in> fml_sem I (Fsubst \<phi> \<sigma>)}"
      using fml_eq rangeI t sol solves_ode_domainD by fastforce
    have sol':"(sol solves_ode (\<lambda>a. ODE_sem I (Osubst ODE \<sigma>))) {0..t} {x. mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) x \<in> fml_sem (adjoint I \<sigma> (sol 0, bb)) \<phi>}"
      apply (rule solves_ode_congI)
          apply (rule sol)
         subgoal for ta by auto
        subgoal for ta using sem_fact[of ta] by auto
       subgoal by (rule refl)
      subgoal by (rule refl)
      done
    have sol'':"(sol solves_ode (\<lambda>a. ODE_sem I (Osubst ODE \<sigma>))) {0..t} {x. mk_v I (Osubst ODE \<sigma>) (sol 0, bb) x \<in> fml_sem I (Fsubst \<phi> \<sigma>)}"
      apply (rule solves_odeI)
       subgoal using sol' solves_ode_vderivD by blast
      subgoal for ta using sub[of ta] apply auto 
        by (meson empty_iff)
      done
  show "\<exists>sola. sol 0 = sola 0 \<and>
        (\<exists>ta. mk_v (adjoint I \<sigma> (sol 0, bb)) ODE (sol 0, bb) (sol t) = mk_v I (Osubst ODE \<sigma>) (sola 0, bb) (sola ta) \<and>
              0 \<le> ta \<and>
              (sola solves_ode (\<lambda>a. ODE_sem I (Osubst ODE \<sigma>))) {0..ta} {x. mk_v I (Osubst ODE \<sigma>) (sola 0, bb) x \<in> fml_sem I (Fsubst \<phi> \<sigma>)})"
    apply(rule exI[where x=sol])
    apply(rule conjI)
     subgoal by (rule refl)
    apply(rule exI[where x=t])
    apply(rule conjI)
     subgoal using  mkvt t by auto
    apply(rule conjI)
     subgoal by (rule t)
    subgoal using sol'' by auto 
    done
  qed
  then show "?case" by auto 
next
  case (Padmit_Choice \<sigma> a b) then 
  have IH1:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a))"
    and IH2:"hpsafe b \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst b \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) b))"
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
      "(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"
        unfolding ssafe_def by (metis option.simps(5))+
    from hpsafe have dsafe:"dsafe \<theta>" by (auto elim: hpsafe.cases)
    fix \<nu> \<omega>

    show "?thesis \<nu> \<omega>"
      using subst_dterm[OF good_interp TA dsafe ssafes]
      by auto
  qed
  then show ?case by auto
next
  case (Padmit_AssignAny \<sigma> x) then
  show ?case by auto
next
  case (Padmit_DiffAssign \<sigma> \<theta> x) then
  have TA:"Tadmit \<sigma> \<theta>" by auto
  have "hpsafe (DiffAssign x \<theta>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow>  (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (DiffAssign x \<theta>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (DiffAssign x \<theta>)))"
  proof -
    assume hpsafe:"hpsafe (DiffAssign x \<theta>)"
    assume ssafe:"ssafe \<sigma>"
    from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
        "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      "(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"
        unfolding ssafe_def by (metis option.simps(5))+
    from hpsafe have dsafe:"dsafe \<theta>" by (auto elim: hpsafe.cases)
    fix \<nu> \<omega>
    show "?thesis \<nu> \<omega>"
      using subst_dterm[OF good_interp TA dsafe ssafes]
      by auto
  qed
  then show ?case by auto
next
  case (Padmit_Test \<sigma> \<phi>) then
  have IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
    by auto
  have "hpsafe (? \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst (? \<phi>) \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) (? \<phi>)))"
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
  have "fsafe (Geq \<theta>1 \<theta>2) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (Geq \<theta>1 \<theta>2) \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (Geq \<theta>1 \<theta>2)))"
  proof -
    assume fsafe:"fsafe (Geq \<theta>1 \<theta>2)"
    assume ssafe:"ssafe \<sigma>"
    from fsafe have dsafe1:"dsafe \<theta>1" and dsafe2:"dsafe \<theta>2"
      by (auto dest: fsafe.cases)
    from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
      "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      "(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"
      unfolding ssafe_def by (metis option.simps(5))+
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
    and substSafes:"\<And>i. dsafe (Tsubst (args i) \<sigma>)"
      by auto
    have "fsafe ($\<phi> p args) \<Longrightarrow>
         ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst ($\<phi> p args) \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) ($\<phi> p args)))"
    proof -
      assume fsafe:"fsafe ($\<phi> p args)"
      then have "nonbase p" by auto
      assume ssafe:"ssafe \<sigma>"
      from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
      "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      "(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"
      unfolding ssafe_def by (metis option.simps(5))+
      fix \<nu>
      from fsafe have safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
      have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
          dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
        using  subst_dterm[OF good_interp TA safes ssafes]  by auto
      have eqs:"\<And>i \<nu>'. dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>"
        by (auto simp add: IH safes)
      let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
      have freef:"fsafe p'" using ssafe some unfolding ssafe_def by (metis option.simps(5))+ 
      have IH2:"(\<nu> \<in> fml_sem I (FsubstFO p' ?sub)) = (\<nu> \<in> fml_sem (adjointFO I ?sub \<nu>) p')"
        using nsubst_fml good_interp NFA freef substSafes
        by blast
      have vec:"(\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)"
        apply(auto simp add: vec_eq_iff)
        subgoal for i
          using IH[of i, OF safes[of i]] 
          by auto
        done
      show "?thesis \<nu>" 
        using IH safes eqs apply (auto simp add:  IH2  some good_interp)
        using some unfolding adjoint_def adjointFO_def apply (auto simp del: args_to_id.simps)
      proof -
        assume a1:" \<nu> \<in> fml_sem
          \<lparr>Functions =
             \<lambda>f. case args_to_id f of None \<Rightarrow> Functions I f | Some (Inl f') \<Rightarrow> Functions I f
                 | Some (Inr f') \<Rightarrow> \<lambda>_. dterm_sem I (Tsubst (args f') \<sigma>) \<nu>,
             Funls =
               \<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl f') \<Rightarrow> Funls I f
                   | Some (Inr f') \<Rightarrow> \<lambda>R. dterm_sem I (Tsubst (args f') \<sigma>) \<nu>,
             Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
          p'"
(*        assume a1: "\<nu> \<in> fml_sem \<lparr>Functions = \<lambda>f. case args_to_id f of Some (Inl x) \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> \<lambda>_. (\<chi> i. dterm_sem \<lparr>Functions = \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' \<nu>, Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem I f' \<nu>, Predicates = \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. \<nu> \<in> fml_sem (extendf I R) p', Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c', Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x, ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x, ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr> (args i) \<nu>) $ f', 
Funls = \<lambda>f. case args_to_id f of Some (Inl x) \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> \<lambda>_. (\<chi> i. dterm_sem \<lparr>Functions = \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' \<nu>, Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem I f' \<nu>, Predicates = \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. \<nu> \<in> fml_sem (extendf I R) p', Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c', Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x, ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x, ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr> (args i) \<nu>) $ f' | None \<Rightarrow> Funls I f, Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr> p'"*)
        have f2: "\<forall>f. ($) (vec_lambda (f::Finite_String.ident \<Rightarrow> real)) = f"
          by (simp add: vec_lambda_inverse)
        then have "\<nu> \<in> fml_sem 
\<lparr>Functions = \<lambda>i. case args_to_id i of Some (Inl x) \<Rightarrow> Functions I i 
  | Some (Inr i) \<Rightarrow> \<lambda>v. dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu> | None \<Rightarrow> Functions I i, 
  Funls = \<lambda>i. case args_to_id i of Some (Inl x) \<Rightarrow> Funls I i 
|   Some (Inr i) \<Rightarrow> \<lambda>p. dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu> | None \<Rightarrow> Funls I i, Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr> p'"
          using a1 adjoint_def vec 
        proof -
          have "(\<lambda>i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<lambda>i. dterm_sem (USubst.adjoint I \<sigma> \<nu>) (args i) \<nu>)"
            using vec by fastforce
          then show ?thesis
            by (metis (no_types) a1)
        qed
        then show " \<nu> \<in> fml_sem
          \<lparr>Functions =
             \<lambda>f. case args_to_id f of None \<Rightarrow> Functions I f | Some (Inl xa) \<Rightarrow> Functions I f
                 | Some (Inr f') \<Rightarrow>
                     \<lambda>_. (\<chi> i. dterm_sem
                                \<lparr>Functions = \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' \<nu>,
                                   Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem I f' R,
                                   Predicates =
                                     \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. \<nu> \<in> fml_sem (extendf I R) p',
                                   Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c',
                                   Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x,
                                   ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x,
                                   ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr>
                                (args i) \<nu>) $
                         f',
             Funls =
               \<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl xa) \<Rightarrow> Funls I f
                   | Some (Inr f') \<Rightarrow>
                       \<lambda>_. (\<chi> i. dterm_sem
                                  \<lparr>Functions =
                                     \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' \<nu>,
                                     Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem I f' R,
                                     Predicates =
                                       \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. \<nu> \<in> fml_sem (extendf I R) p',
                                     Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c',
                                     Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x,
                                     ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x,
                                     ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr>
                                  (args i) \<nu>) $
                           f',
             Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
          p'"
          using f2  vec  USubst.adjoint_def by metis
      next
        assume a1: "\<nu> \<in> fml_sem
          \<lparr>Functions =
             \<lambda>f. case args_to_id f of None \<Rightarrow> Functions I f | Some (Inl xa) \<Rightarrow> Functions I f
                 | Some (Inr f') \<Rightarrow>
                     \<lambda>_. (\<chi> i. dterm_sem
                                \<lparr>Functions = \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' \<nu>,
                                   Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some f' \<Rightarrow>  dterm_sem I f',
                                   Predicates =
                                     \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. \<nu> \<in> fml_sem (extendf I R) p',
                                   Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c',
                                   Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x,
                                   ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x,
                                   ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr>
                                (args i) \<nu>) $
                         f',
             Funls =
               \<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl xa) \<Rightarrow> Funls I f
                   | Some (Inr f') \<Rightarrow>
                       \<lambda>_. (\<chi> i. dterm_sem
                                  \<lparr>Functions =
                                     \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' \<nu>,
                                     Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem I f' R,
                                     Predicates =
                                       \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. \<nu> \<in> fml_sem (extendf I R) p',
                                     Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c',
                                     Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x,
                                     ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x,
                                     ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr>
                                  (args i) \<nu>) $
                           f',
             Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
          p'"
        have f2: "\<forall>f. ($) (vec_lambda (f::Finite_String.ident \<Rightarrow> real)) = f"
          by (simp add: vec_lambda_inverse)
         show " \<nu> \<in> fml_sem
          \<lparr>Functions =
             \<lambda>f. case args_to_id f of None \<Rightarrow> Functions I f | Some (Inl f') \<Rightarrow> Functions I f
                 | Some (Inr f') \<Rightarrow> \<lambda>_. dterm_sem I (Tsubst (args f') \<sigma>) \<nu>,
             Funls =
               \<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl f') \<Rightarrow> Funls I f
                   | Some (Inr f') \<Rightarrow> \<lambda>_. dterm_sem I (Tsubst (args f') \<sigma>) \<nu>,
             Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
          p'"
          using f2  adjoint_def vec a1 
        proof -
          have f1: "(\<lambda>i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<lambda>i. dterm_sem (USubst.adjoint I \<sigma> \<nu>) (args i) \<nu>)"
            using vec by auto
          have "\<nu> \<in> fml_sem \<lparr>Functions = \<lambda>i. case args_to_id i of None \<Rightarrow> Functions I i | Some (Inl ia) \<Rightarrow> Functions I i | Some (Inr i) \<Rightarrow> \<lambda>v. dterm_sem (USubst.adjoint I \<sigma> \<nu>) (args i) \<nu>, Funls = \<lambda>i. case args_to_id i of None \<Rightarrow> Funls I i | Some (Inl ia) \<Rightarrow> Funls I i | Some (Inr i) \<Rightarrow> \<lambda>p. dterm_sem (USubst.adjoint I \<sigma> \<nu>) (args i) \<nu>, Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr> p'"
            by (metis USubst.adjoint_def a1 f2) 
          then show ?thesis
            using f1 by metis
        qed
      qed
    qed
  then show "?case" by auto
next
  case (Fadmit_Prop2 \<sigma> args p) 
  note TA = Fadmit_Prop2.hyps(1)
    and none = Fadmit_Prop2.hyps(2)
  have "fsafe (Prop p args) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>.(\<nu> \<in> fml_sem I (Fsubst ($\<phi> p args) \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) ($\<phi> p args)))"
  proof -
    assume safe:"fsafe (Prop p args)" and ssafe:"ssafe \<sigma>"
    from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
        "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      "(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"
        unfolding ssafe_def by (metis option.simps(5))+
    fix \<nu>
    from safe have  safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
    have IH:"(\<And>\<nu>'. \<And>i. dsafe (args i) \<Longrightarrow>
        dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
    using  subst_dterm good_interp TA safes ssafes by auto
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
  have IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
    by blast
  have fsafe:"fsafe (Not \<phi>) \<Longrightarrow> fsafe \<phi>"
    by (auto dest: fsafe.cases)
  show ?case using IH[OF fsafe] by auto
next
  case (Fadmit_And \<sigma> \<phi> \<psi>) then
    have IH1:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
      and IH2:"fsafe \<psi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<psi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<psi>))"
      by (blast)+
    have fsafe1:"fsafe (\<phi> && \<psi>) \<Longrightarrow> fsafe \<phi>" and fsafe2:"fsafe (\<phi> && \<psi>) \<Longrightarrow> fsafe \<psi>" 
      by (auto dest: fsafe.cases)
    show ?case using IH1[OF fsafe1] IH2[OF fsafe2] by auto
next
  case (Fadmit_Exists \<sigma> \<phi> x)
  then have IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
    and FUA:"FUadmit \<sigma> \<phi> {Inl x}"
    by blast+
  have fsafe:"fsafe (Exists x \<phi>) \<Longrightarrow> fsafe \<phi>"
    by (auto dest: fsafe.cases)
  have eq:"fsafe (Exists x \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst  (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>)  (Exists x \<phi>)))"
  proof -
    assume fsafe:"fsafe (Exists x \<phi>)"
    from fsafe have fsafe':"fsafe \<phi>" by (auto dest: fsafe.cases)
    assume ssafe:"ssafe \<sigma>"
    fix \<nu>
    have agree:"\<And>r. Vagree \<nu> (repv \<nu> x r) (- {Inl x})"
      unfolding Vagree_def by auto
    have sem_eq:"\<And>r. ((repv \<nu> x r) \<in> fml_sem (adjoint I \<sigma> (repv \<nu> x r)) \<phi>) =
                      ((repv \<nu> x r) \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>)"
      using uadmit_fml_adjoint[OF FUA agree fsafe' ssafe good_interp] by auto
    have "(\<nu> \<in> fml_sem I (Fsubst  (Exists x \<phi>) \<sigma>)) = (\<exists>r. (repv \<nu> x r) \<in> fml_sem I (Fsubst \<phi> \<sigma>))"
      by auto
    moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (adjoint I \<sigma> (repv \<nu> x r)) \<phi>)"
      using IH[OF fsafe' ssafe] by auto
    moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>)"
      using sem_eq by auto
    moreover have "... = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (Exists x \<phi>))"
      by auto
    ultimately show "(\<nu> \<in> fml_sem I (Fsubst  (Exists x \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>)  (Exists x \<phi>))"
      by auto
    qed
  then show ?case by auto
next
  case (Fadmit_Diamond \<sigma> \<phi> a) then 
    have PA:"Padmit \<sigma> a" 
      and FUA:"FUadmit \<sigma> \<phi> (BVP (Psubst a \<sigma>))"
      and IH1:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
      and IH2:"hpsafe a \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu> \<omega>. ((\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>)) = ((\<nu>, \<omega>) \<in> prog_sem (adjoint I \<sigma> \<nu>) a))"
      and substSafe:"hpsafe (Psubst a \<sigma>)"
      by auto
    have "fsafe (\<langle> a \<rangle> \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (\<langle> a \<rangle> \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (\<langle> a \<rangle> \<phi>)))"
    proof -
      assume fsafe:"fsafe (\<langle> a \<rangle> \<phi>)"
      assume ssafe:"ssafe \<sigma>"
      from fsafe have fsafe':"fsafe \<phi>" and hpsafe:"hpsafe a" by (auto dest: fsafe.cases)
      fix \<nu>
      have agree:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> Vagree \<nu> \<omega> (-BVP(Psubst a \<sigma>))"
        using bound_effect[OF good_interp, of "(Psubst a \<sigma>)" \<nu>, OF substSafe] by auto
      have sem_eq:"\<And>\<omega>. (\<nu>, \<omega>) \<in> prog_sem I (Psubst a \<sigma>) \<Longrightarrow> 
          (\<omega> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>) =
          (\<omega> \<in> fml_sem (adjoint I \<sigma> \<omega>) \<phi>)"
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
   have "fsafe(Prop p args) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>.(\<nu> \<in> fml_sem I (Fsubst ($\<phi> p args) \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) ($\<phi> p args)))"
   proof -
     assume fsafe:"fsafe (Prop p args)"
       and ssafe:"ssafe \<sigma>"
     from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
       "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      "(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"
       unfolding ssafe_def by (metis option.simps(5))+
     fix \<nu>
     note TA = Fadmit_Prop1.hyps(1)
       and some = Fadmit_Prop1.hyps(2) and NFA = Fadmit_Prop1.hyps(3)
     from fsafe have safes:"\<And>i. dsafe (args i)" using dfree_is_dsafe by auto
     have IH:"(\<And>\<nu>. \<And>i. dsafe (args i) \<Longrightarrow>
         dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
       using  subst_dterm  good_interp TA safes ssafes by auto
     have eqs:"\<And>i \<nu>'. dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>"
       by (auto simp add: IH safes)
     let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
     have subSafe:"(\<forall> i. dsafe (?sub i))"
       by (simp add: safes ssafes tsubst_preserves_safe)
     have freef:"fsafe p'" using ssafe some unfolding ssafe_def by (metis option.simps(5))+ 
     have IH2:"(\<nu> \<in> fml_sem I (FsubstFO p' ?sub)) = (\<nu> \<in> fml_sem (adjointFO I ?sub \<nu>) p')"
       by (simp add: nsubst_fml [OF good_interp NFA freef subSafe])
     have vec:"\<And>\<nu>. (\<chi> i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<chi> i. dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)"
       apply(auto simp add: vec_eq_iff)
       subgoal for a b i
         using IH[of i, OF safes[of i]] 
         by auto
       done
     show "?thesis \<nu>" 
       using IH safes eqs apply (auto simp add:  IH2  some good_interp)
     proof -
       assume a0:"\<nu> \<in> fml_sem (adjointFO I (\<lambda>i. Tsubst (args i) \<sigma>) \<nu>) p'"
       then have a0: "\<nu> \<in> fml_sem \<lparr>Functions =
             \<lambda>f. case args_to_id f of None \<Rightarrow> Functions I f | Some (Inl f') \<Rightarrow> Functions I f
                 | Some (Inr f') \<Rightarrow> \<lambda>_. dterm_sem I (Tsubst (args f') \<sigma>) \<nu>,
             Funls =
               \<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl f') \<Rightarrow> Funls I f
                   | Some (Inr f') \<Rightarrow> \<lambda>_. dterm_sem I (Tsubst (args f') \<sigma>) \<nu>,
             Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
          p'" unfolding adjointFO_def by auto
       have f2: "\<forall>f. ($) (vec_lambda (f::Finite_String.ident \<Rightarrow> real)) = f"
         by (simp add: vec_lambda_inverse)
       have dtsub:"(\<lambda>i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<lambda>i. dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)"
         using vec by auto
       then have dat:"\<nu> \<in> fml_sem \<lparr>Functions =
             \<lambda>f. case args_to_id f of None \<Rightarrow> Functions I f | Some (Inl f') \<Rightarrow> Functions I f
                 | Some (Inr f') \<Rightarrow> \<lambda>R. dterm_sem (adjoint I \<sigma> \<nu>) (args f') \<nu>,
             Funls =
               \<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl f') \<Rightarrow> Funls I f
                   | Some (Inr f') \<Rightarrow> \<lambda>R. dterm_sem (adjoint I \<sigma> \<nu>) (args f') \<nu>,
             Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>
          p'"
         using a0 vec f2 by metis
        show " Predicates (USubst.adjoint I \<sigma> \<nu>) p (\<chi> i. dterm_sem (USubst.adjoint I \<sigma> \<nu>) (args i) \<nu>)"
         using f2 adjoint_def vec apply(auto simp add: some  simp del: args_to_id.simps )
         using dat  
         using USubst.adjoint_def by metis
    next
      assume a0:"Predicates (USubst.adjoint I \<sigma> \<nu>) p (\<chi> i. dterm_sem (USubst.adjoint I \<sigma> \<nu>) (args i) \<nu>)"
      then have a1:"\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (Prop p args)" by auto
       have f2: "\<forall>f. ($) (vec_lambda (f::Finite_String.ident \<Rightarrow> real)) = f"
         using vec_lambda_inverse by blast
       note f3 = a0[unfolded adjoint_def]

       have f3: "(\<lambda>i \<nu>. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>) = (\<lambda>i \<nu>. dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)"
         by (simp add: IH safes)
       (*TODO: Verbose*)
       have funlEq:"(\<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl f') \<Rightarrow> Funls I f
                   | Some (Inr f') \<Rightarrow>
                       \<lambda>Q. (\<chi> i. dterm_sem
                                  \<lparr>Functions =
                                     \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' Q,
                                   Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem I f' R,
                                   Predicates =
                                      \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. Q \<in> fml_sem (extendf I R) p',
                                   Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c',
                                   Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x,
                                   ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x,
                                   ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr>
                                  (args i) Q) $
                           f')
= (\<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl f') \<Rightarrow> Funls I f
                   | Some (Inr f') \<Rightarrow> \<lambda>R. dterm_sem I (Tsubst (args f') \<sigma>) R)"

         apply(rule ext)+ subgoal for f x
           apply(cases "args_to_id f") apply auto subgoal for a
             apply(cases "ident_expose f")  apply(auto simp add: SSENT_def FSENT_def SSENTINEL_def FSENTINEL_def)
             subgoal for aa b apply(cases a) apply auto subgoal for ba  using IH IH2 
               using f3[unfolded adjoint_def] apply auto
               by metis+ done done done done
       have sillier:"\<lparr>Functions =
             \<lambda>f. case args_to_id f of None \<Rightarrow> Functions I f | Some (Inl f') \<Rightarrow> Functions I f
                 | Some (Inr f') \<Rightarrow>
                     \<lambda>_. ((\<chi> i. dterm_sem
                                \<lparr>Functions = \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' \<nu>,
                                   Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem I f' R,
                                   Predicates =
                                     \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. \<nu> \<in> fml_sem (extendf I R) p',
                                   Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c',
                                   Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x,
                                   ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x,
                                   ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr>
                                (args i) \<nu>) $
                         f'),
             Funls =
               \<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl f') \<Rightarrow> Funls I f
                   | Some (Inr f') \<Rightarrow>
                       \<lambda>Q. (\<chi> i. dterm_sem
                                  \<lparr>Functions =
                                     \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' Q,
                                   Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem I f' R,
                                   Predicates =
                                      \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. Q \<in> fml_sem (extendf I R) p',
                                   Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c',
                                   Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x,
                                   ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x,
                                   ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr>
                                  (args i) Q) $
                           f',
             Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr> 
    = \<lparr>Functions =
             \<lambda>f. case args_to_id f of None \<Rightarrow> Functions I f | Some (Inl f') \<Rightarrow> Functions I f
                 | Some (Inr f') \<Rightarrow> \<lambda>_. dterm_sem I (Tsubst (args f') \<sigma>) \<nu>,
             Funls =
               \<lambda>f. case args_to_id f of None \<Rightarrow> Funls I f | Some (Inl f') \<Rightarrow> Funls I f
                   | Some (Inr f') \<Rightarrow> \<lambda>R. dterm_sem I (Tsubst (args f') \<sigma>) R,
             Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr>" 
         apply(rule interp_eq)
               apply(auto simp del: args_to_id.simps)
         subgoal apply(rule ext)+ subgoal for f x apply(cases "ident_expose f") using IH IH2 apply(auto simp add: SSENT_def FSENT_def SSENTINEL_def FSENTINEL_def)
           by (simp add: USubst.adjoint_def eqs)+ done
       subgoal apply(rule ext)+ 
         subgoal for f x 
           apply(cases "ident_expose f")
           subgoal for a by auto
           subgoal for b
             apply(cases b)
             subgoal for a ba
               apply(auto simp add: SSENT_def FSENT_def SSENTINEL_def FSENTINEL_def)
               using funlEq 
               by (metis USubst.adjoint_def f3)+ done done done done 
     show " \<nu> \<in> fml_sem (adjointFO I (\<lambda>i. Tsubst (args i) \<sigma>) \<nu>) p'"
       using a1
       apply(auto simp add: adjointFO_def adjoint_def some )
       using f3 sillier  a1[unfolded adjoint_def] using  ident_expose_def     adjointFO_def adjoint_def   some  args_to_id.simps f3 sledgehammer
proof -
  assume a1: "\<nu> \<in> fml_sem \<lparr>Functions = \<lambda>f. case case ident_expose f of Inl x \<Rightarrow> Map.empty x | Inr (xa, xs) \<Rightarrow> if xa = FSENT then Some (Inr xs) else if xa = SSENT then Some (Inl xs) else None of None \<Rightarrow> Functions I f | Some (Inl f') \<Rightarrow> Functions I f | Some (Inr f') \<Rightarrow> \<lambda>_. (\<chi> i. dterm_sem \<lparr>Functions = \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' \<nu>, Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some x \<Rightarrow> dterm_sem I x, Predicates = \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. \<nu> \<in> fml_sem (extendf I R) p', Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c', Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x, ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x, ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr> (args i) \<nu>) $ f', Funls = \<lambda>f. case case ident_expose f of Inl x \<Rightarrow> Map.empty x | Inr (xa, xs) \<Rightarrow> if xa = FSENT then Some (Inr xs) else if xa = SSENT then Some (Inl xs) else None of None \<Rightarrow> Funls I f | Some (Inl f') \<Rightarrow> Funls I f | Some (Inr f') \<Rightarrow> \<lambda>_. (\<chi> i. dterm_sem \<lparr>Functions = \<lambda>f. case SFunctions \<sigma> f of None \<Rightarrow> Functions I f | Some f' \<Rightarrow> \<lambda>R. dterm_sem (extendf I R) f' \<nu>, Funls = \<lambda>f. case SFunls \<sigma> f of None \<Rightarrow> Funls I f | Some x \<Rightarrow> dterm_sem I x, Predicates = \<lambda>p. case SPredicates \<sigma> p of None \<Rightarrow> Predicates I p | Some p' \<Rightarrow> \<lambda>R. \<nu> \<in> fml_sem (extendf I R) p', Contexts = \<lambda>c. case SContexts \<sigma> c of None \<Rightarrow> Contexts I c | Some c' \<Rightarrow> \<lambda>R. fml_sem (extendc I R) c', Programs = \<lambda>a. case SPrograms \<sigma> a of None \<Rightarrow> Programs I a | Some x \<Rightarrow> prog_sem I x, ODEs = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEs I ode sp | Some x \<Rightarrow> ODE_sem I x, ODEBV = \<lambda>ode sp. case SODEs \<sigma> ode sp of None \<Rightarrow> ODEBV I ode sp | Some x \<Rightarrow> ODE_vars I x\<rparr> (args i) \<nu>) $ f', Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr> p'"
  have f2: "\<forall>p. (\<lambda>i. dterm_sem \<lparr>Functions = \<lambda>i. case SFunctions \<sigma> i of None \<Rightarrow> Functions I i | Some t \<Rightarrow> \<lambda>v. dterm_sem (extendf I v) t p, Funls = \<lambda>i. case SFunls \<sigma> i of None \<Rightarrow> Funls I i | Some x \<Rightarrow> dterm_sem I x, Predicates = \<lambda>i. case SPredicates \<sigma> i of None \<Rightarrow> Predicates I i | Some f \<Rightarrow> \<lambda>v. p \<in> fml_sem (extendf I v) f, Contexts = \<lambda>i. case SContexts \<sigma> i of None \<Rightarrow> Contexts I i | Some f \<Rightarrow> \<lambda>r. fml_sem (extendc I r) f, Programs = \<lambda>i. case SPrograms \<sigma> i of None \<Rightarrow> Programs I i | Some x \<Rightarrow> prog_sem I x, ODEs = \<lambda>i z. case SODEs \<sigma> i z of None \<Rightarrow> ODEs I i z | Some x \<Rightarrow> ODE_sem I x, ODEBV = \<lambda>i z. case SODEs \<sigma> i z of None \<Rightarrow> ODEBV I i z | Some x \<Rightarrow> ODE_vars I x\<rparr> (args i) p) = (\<lambda>i. dterm_sem I (Tsubst (args i) \<sigma>) p)"
    using USubst.adjoint_def vec by force
  have "\<nu> \<in> fml_sem \<lparr>Functions = \<lambda>i. case case ident_expose i of Inl x \<Rightarrow> Map.empty x | Inr (c, i) \<Rightarrow> if c = FSENT then Some (Inr i) else if c = SSENT then Some (Inl i) else None of None \<Rightarrow> Functions I i | Some (Inl ia) \<Rightarrow> Functions I i | Some (Inr i) \<Rightarrow> \<lambda>v. dterm_sem \<lparr>Functions = \<lambda>i. case SFunctions \<sigma> i of None \<Rightarrow> Functions I i | Some t \<Rightarrow> \<lambda>v. dterm_sem (extendf I v) t \<nu>, Funls = \<lambda>i. case SFunls \<sigma> i of None \<Rightarrow> Funls I i | Some x \<Rightarrow> dterm_sem I x, Predicates = \<lambda>i. case SPredicates \<sigma> i of None \<Rightarrow> Predicates I i | Some f \<Rightarrow> \<lambda>v. \<nu> \<in> fml_sem (extendf I v) f, Contexts = \<lambda>i. case SContexts \<sigma> i of None \<Rightarrow> Contexts I i | Some f \<Rightarrow> \<lambda>r. fml_sem (extendc I r) f, Programs = \<lambda>i. case SPrograms \<sigma> i of None \<Rightarrow> Programs I i | Some x \<Rightarrow> prog_sem I x, ODEs = \<lambda>i z. case SODEs \<sigma> i z of None \<Rightarrow> ODEs I i z | Some x \<Rightarrow> ODE_sem I x, ODEBV = \<lambda>i z. case SODEs \<sigma> i z of None \<Rightarrow> ODEBV I i z | Some x \<Rightarrow> ODE_vars I x\<rparr> (args i) \<nu>, Funls = \<lambda>i. case case ident_expose i of Inl x \<Rightarrow> Map.empty x | Inr (c, i) \<Rightarrow> if c = FSENT then Some (Inr i) else if c = SSENT then Some (Inl i) else None of None \<Rightarrow> Funls I i | Some (Inl ia) \<Rightarrow> Funls I i | Some (Inr i) \<Rightarrow> \<lambda>p. dterm_sem \<lparr>Functions = \<lambda>i. case SFunctions \<sigma> i of None \<Rightarrow> Functions I i | Some t \<Rightarrow> \<lambda>v. dterm_sem (extendf I v) t \<nu>, Funls = \<lambda>i. case SFunls \<sigma> i of None \<Rightarrow> Funls I i | Some x \<Rightarrow> dterm_sem I x, Predicates = \<lambda>i. case SPredicates \<sigma> i of None \<Rightarrow> Predicates I i | Some f \<Rightarrow> \<lambda>v. \<nu> \<in> fml_sem (extendf I v) f, Contexts = \<lambda>i. case SContexts \<sigma> i of None \<Rightarrow> Contexts I i | Some f \<Rightarrow> \<lambda>r. fml_sem (extendc I r) f, Programs = \<lambda>i. case SPrograms \<sigma> i of None \<Rightarrow> Programs I i | Some x \<Rightarrow> prog_sem I x, ODEs = \<lambda>i z. case SODEs \<sigma> i z of None \<Rightarrow> ODEs I i z | Some x \<Rightarrow> ODE_sem I x, ODEBV = \<lambda>i z. case SODEs \<sigma> i z of None \<Rightarrow> ODEBV I i z | Some x \<Rightarrow> ODE_vars I x\<rparr> (args i) \<nu>, Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr> p'"
    using a1 f2 
  proof -
    have "\<forall>f. ($) (vec_lambda (f::Finite_String.ident \<Rightarrow> real)) = f"
      by (meson UNIV_I vec_eq_iff vec_lambda_beta vec_lambda_inject)
    then show ?thesis
      using a1 by presburger
  qed
  then show "\<nu> \<in> fml_sem \<lparr>Functions = \<lambda>i. case case ident_expose i of Inl x \<Rightarrow> Map.empty x | Inr (c, i) \<Rightarrow> if c = FSENT then Some (Inr i) else if c = SSENT then Some (Inl i) else None of None \<Rightarrow> Functions I i | Some (Inl ia) \<Rightarrow> Functions I i | Some (Inr i) \<Rightarrow> \<lambda>v. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>, Funls = \<lambda>i. case case ident_expose i of Inl x \<Rightarrow> Map.empty x | Inr (c, i) \<Rightarrow> if c = FSENT then Some (Inr i) else if c = SSENT then Some (Inl i) else None of None \<Rightarrow> Funls I i | Some (Inl ia) \<Rightarrow> Funls I i | Some (Inr i) \<Rightarrow> \<lambda>p. dterm_sem I (Tsubst (args i) \<sigma>) \<nu>, Predicates = Predicates I, Contexts = Contexts I, Programs = Programs I, ODEs = ODEs I, ODEBV = ODEBV I\<rparr> p'"
    using f2 by metis 
qed
      
     qed
   qed
next 
  case (Fadmit_Context1 \<sigma> \<phi> C C') then
  have FA:"Fadmit \<sigma> \<phi>"
    and FUA:"FUadmit \<sigma> \<phi> UNIV"
    and some:"SContexts \<sigma> C = Some C'"
    and PFA:"PFadmit (\<lambda>_. Fsubst \<phi> \<sigma>) C'"
    and IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
    and substSafe:"fsafe(Fsubst \<phi> \<sigma>)"
    by auto
  have "fsafe (InContext C \<phi>) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (InContext C \<phi>)))"
  proof -
    assume safe:"fsafe (InContext C \<phi>)"
    from safe have fsafe:"fsafe \<phi>" by (auto dest: fsafe.cases)
    assume ssafe:"ssafe \<sigma>"
    fix \<nu> :: "state"
    have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
    have adj_eq:"\<And>\<omega>. fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
      using uadmit_fml_adjoint[OF FUA agree fsafe ssafe good_interp] by auto
    have eq:"(\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>)"
      using adj_eq IH[OF fsafe ssafe] by auto
    let ?sub = "(\<lambda>_. Fsubst \<phi> \<sigma>)"
    let ?R1 = "fml_sem I (Fsubst \<phi> \<sigma>)"
    let ?R2 = "fml_sem (adjoint I \<sigma> \<nu>) \<phi>"
    have eq':"?R1 = ?R2"
      using adj_eq IH[OF fsafe ssafe] by auto
    have freef:"fsafe C'" using ssafe some unfolding ssafe_def by (metis option.simps(5))+ 
    have IH2:"(\<nu> \<in> fml_sem I (PFsubst C' ?sub)) = (\<nu> \<in> fml_sem (PFadjoint I ?sub) C')"
      using psubst_fml good_interp PFA fsafe substSafe freef by blast 
    have IH':"(\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
      using IH[OF fsafe ssafe] by auto
    then have IH:"fml_sem I (Fsubst \<phi> \<sigma>) = fml_sem (adjoint I \<sigma> \<nu>) \<phi>"
      using eq' by blast
    have duh:" (\<lambda>f' _. fml_sem I (case () of () \<Rightarrow> Fsubst \<phi> \<sigma>)) = (\<lambda> x (). fml_sem (adjoint I \<sigma> \<nu>) \<phi>)"
      by (simp add: case_unit_Unity eq' ext)
    have extend_PF:"(PFadjoint I ?sub) = (extendc I ?R2)"
      unfolding PFadjoint_def using IH apply(auto simp del: args_to_id.simps)
      apply(rule ext)
      by meson
    have "(\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem I (PFsubst C' (\<lambda>_. Fsubst \<phi> \<sigma>)))"
      using some by simp
    moreover have "... = (\<nu> \<in> fml_sem (PFadjoint I ?sub) C')"
      using IH2 by auto
    moreover have "... = (\<nu> \<in> fml_sem (extendc I ?R2) C')"
      using extend_PF by simp
    moreover have "... = (\<nu> \<in> fml_sem (extendc I ?R1) C')"
      using eq' by auto
    moreover have "... = (\<nu> \<in> Contexts (adjoint I \<sigma> \<nu>) C (fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
      using some unfolding adjoint_def apply (auto simp del: args_to_id.simps)
      using eq' adjoint_def by metis+
    moreover have "... = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (InContext C \<phi>))"
      by auto
    ultimately
    show "(\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (InContext C \<phi>))"
      by blast
  qed
  then show ?case by auto
next
  case (Fadmit_Context2 \<sigma> \<phi> C) then
  have FA:"Fadmit \<sigma> \<phi>"
  and FUA:"FUadmit \<sigma> \<phi> UNIV"
  and none:"SContexts \<sigma> C = None"
  and IH:"fsafe \<phi> \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>))"
    by auto
  have "fsafe (InContext C \<phi>) \<Longrightarrow>
           ssafe \<sigma> \<Longrightarrow> (\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst (InContext C \<phi>) \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (InContext C \<phi>)))"
  proof -
    assume safe:"fsafe (InContext C \<phi>)"
    then have fsafe:"fsafe \<phi>" by (auto dest: fsafe.cases)
    assume ssafe:"ssafe \<sigma>"
    fix \<nu>
    have Ieq:" Contexts (adjoint I \<sigma> \<nu>) C = Contexts I C"
      using none unfolding adjoint_def by auto
    have IH':"\<And>\<nu>. (\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>)"
      using IH[OF fsafe ssafe] by auto
    have agree:"\<And>\<omega>. Vagree \<nu> \<omega> (-UNIV)" unfolding Vagree_def by auto
    have adj_eq:"\<And>\<omega>. fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
      using uadmit_fml_adjoint[OF FUA agree fsafe ssafe good_interp] by auto
    then have sem:"fml_sem I (Fsubst \<phi> \<sigma>) =  fml_sem (adjoint I \<sigma> \<nu>) \<phi>"
      using IH' agree adj_eq by auto
    show "?thesis \<nu>"  using none Ieq sem by auto 
  qed
  then show ?case by auto
qed

lemma subst_fml:
  fixes I::"interp" and \<nu>::"state"
  assumes good_interp:"is_interp I"
  assumes Fadmit:"Fadmit \<sigma> \<phi>"
  assumes fsafe:"fsafe \<phi>"
  assumes ssafe:"ssafe \<sigma>"
  shows "(\<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)) = (\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>)"
      using subst_fml_hp[OF good_interp] Fadmit fsafe ssafe by blast
    
lemma subst_fml_valid:
  fixes I::"interp" and \<nu>::"state"
  assumes Fadmit:"Fadmit \<sigma> \<phi>"
  assumes fsafe:"fsafe \<phi>"
  assumes ssafe:"ssafe \<sigma>"
  assumes valid:"valid \<phi>"
  shows "valid (Fsubst \<phi> \<sigma>)"
proof -
  have sub_sem:"\<And>I \<nu>. is_interp I \<Longrightarrow> \<nu> \<in> fml_sem I (Fsubst \<phi> \<sigma>)"
  proof -
    fix I::"interp" and \<nu>::"state"
    assume good_interp:"is_interp I"
    have good_adj:"is_interp (adjoint I \<sigma> \<nu>)"
      apply(rule adjoint_safe[OF good_interp])
      using ssafe unfolding ssafe_def by (metis option.simps(5))+
    have \<phi>sem:"\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) \<phi>" using valid using good_adj unfolding valid_def by blast
    then show "?thesis I \<nu>"
      using subst_fml[OF good_interp Fadmit fsafe ssafe]
      by auto
  qed
  then show ?thesis unfolding valid_def by blast 
qed

context includes no_funcset_notation begin

lemma Tadmit_Zero[simp]: "Tadmit \<sigma> \<^bold>0"
  unfolding Zero_def by simp

lemma Tadmit_One[simp]: "Tadmit \<sigma> \<^bold>1"
  unfolding One_def by simp

lemma fsafe_TT[simp]: "fsafe TT"
  unfolding TT_def by simp

lemma fsafe_FF[simp]: "fsafe FF"
  unfolding FF_def by simp

lemma fsafe_Or[simp]:
  "fsafe (A || B) \<longleftrightarrow> fsafe A \<and> fsafe B"
  unfolding Or_def
  by simp

lemma fsafe_Implies[simp]:
  "fsafe (A \<rightarrow> B) \<longleftrightarrow> fsafe A \<and> fsafe B"
  unfolding Implies_def
  by auto

lemma Fadmit_TT[simp]: "Fadmit \<sigma> TT"
  unfolding TT_def by simp

lemma Fadmit_FF[simp]: "Fadmit \<sigma> FF"
  unfolding FF_def by simp

lemma Fadmit_Or[simp]:
  "Fadmit \<sigma> (A || B) \<longleftrightarrow> Fadmit \<sigma> A \<and> Fadmit \<sigma> B"
  unfolding Or_def
  by simp

lemma Fadmit_Implies[simp]:
  "Fadmit \<sigma> (A \<rightarrow> B) \<longleftrightarrow> Fadmit \<sigma> A \<and> Fadmit \<sigma> B"
  unfolding Implies_def
  by auto

end

lemma subst_sequent:
  fixes I::" interp" and \<nu>::" state"
  assumes good_interp:"is_interp I"
  assumes Sadmit:"Sadmit \<sigma> (\<Gamma>,\<Delta>)"
  assumes Ssafe:"Ssafe (\<Gamma>,\<Delta>)"
  assumes ssafe:"ssafe \<sigma>"
  shows "(\<nu> \<in> seq_sem I (Ssubst (\<Gamma>,\<Delta>) \<sigma>)) = (\<nu> \<in> seq_sem (adjoint I \<sigma> \<nu>) (\<Gamma>,\<Delta>))"
proof -
  let ?f = "(seq2fml (\<Gamma>, \<Delta>))"
  have subst_eqG:"Fsubst (foldr (&&) \<Gamma> TT) \<sigma> = foldr  (&&) (map (\<lambda>\<phi>. Fsubst \<phi> \<sigma>) \<Gamma>) TT"
    by(induction \<Gamma>, auto simp add: TT_def)
  have subst_eqD:"Fsubst (foldr (||) \<Delta> FF) \<sigma> = foldr (||)  (map (\<lambda>\<phi>. Fsubst \<phi> \<sigma>) \<Delta>) FF"
    by(induction \<Delta>, auto simp add: FF_def Or_def)
  have subst_eq:"Fsubst ?f \<sigma> = (seq2fml (Ssubst (\<Gamma>, \<Delta>) \<sigma>))"
    using subst_eqG subst_eqD 
    by (auto simp add: Implies_def Or_def)
  have fsafeG:"fsafe (foldr (&&) \<Gamma> TT)" 
    using Ssafe by (induction \<Gamma>) fastforce+
  have fsafeD:"fsafe (foldr (||) \<Delta> FF)" 
    using Ssafe by(induction \<Delta>) fastforce+
  have fsafe:"fsafe ?f" 
    using fsafeD fsafeG by auto
  have FadmitG:"Fadmit \<sigma> (foldr (&&) \<Gamma> TT)"
    using Sadmit by (induction \<Gamma>) (fastforce simp add: Sadmit_def)+
  have FadmitD:"Fadmit \<sigma> (foldr (||) \<Delta> FF)"
    using Sadmit by (induction \<Delta>) (fastforce simp add: Sadmit_def)+
  have Fadmit:"Fadmit \<sigma> ?f" 
    using FadmitG FadmitD unfolding Implies_def
    by (simp add: Implies_def Or_def)
  have "(\<nu> \<in> fml_sem I (Fsubst ?f \<sigma>)) 
       =(\<nu> \<in> fml_sem (adjoint I \<sigma> \<nu>) (seq2fml (\<Gamma>, \<Delta>)))"
    using subst_fml[OF good_interp Fadmit fsafe ssafe]
    by auto
  then show ?thesis
    using subst_eq by auto
  qed

lemma Ssubst_sound:
  fixes  \<nu>::"state"
  assumes Sadmit:"Sadmit \<sigma> (\<Gamma>,\<Delta>)"
  assumes Ssafe:"Ssafe (\<Gamma>,\<Delta>)"
  assumes ssafe:"ssafe \<sigma>"
  assumes valid:"seq_valid (\<Gamma>,\<Delta>)"
  shows "seq_valid (Ssubst (\<Gamma>,\<Delta>) \<sigma>)"
proof -
     from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f')"
       "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      "(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>i x ODE. SODEs \<sigma> i (Some x) = Some ODE \<Longrightarrow> Inl x \<notin> BVO ODE)"
       unfolding ssafe_def by (metis option.simps(5))+

  have 1:"\<And>I \<nu>. is_interp I \<Longrightarrow> \<nu> \<in> seq_sem I (\<Gamma>,\<Delta>)" using valid unfolding seq_valid_def  by auto
  have goods:"\<And>I \<nu>. is_interp I \<Longrightarrow>is_interp (adjoint I \<sigma> \<nu>)" 
    apply(intro adjoint_safe)
    subgoal by auto
    using ssafe Ssafe ssafes by (auto simp add: ssafe_def Ssafe_def)
  have 2:"\<And>I \<nu>. is_interp I \<Longrightarrow>\<nu> \<in> seq_sem (adjoint I \<sigma> \<nu>) (\<Gamma>, \<Delta>)" subgoal for x
      by(rule 1[OF goods]) done
  have "\<And>I \<nu>. is_interp I \<Longrightarrow>\<nu> \<in> seq_sem I (Ssubst (\<Gamma>, \<Delta>) \<sigma>)"
    using 2 subst_sequent Sadmit Ssafe ssafe by auto
  then show ?thesis
    by(auto simp add: seq_valid_def) 
qed


fun Rsafe::"rule \<Rightarrow> bool"
where Rsafe_def:"Rsafe R = ((\<forall>i. i \<ge> 0 \<longrightarrow> i < length (fst R) \<longrightarrow> Ssafe (nth (fst R) i)) 
                    \<and> Ssafe (snd R))"

lemma Rsafe_code[code]:"Rsafe R = 
((foldr  (\<lambda> x acc. acc \<and> Ssafe x) (fst R) True)   \<and> Ssafe (snd R))"
  apply (auto simp del: Ssafe.simps)
  proof -
    assume all:"\<forall>i<length (fst R). Ssafe (fst R ! i)"
    have mem:"\<And>x. List.member (fst R) x \<Longrightarrow> Ssafe x" 
      apply(erule member_nthE)
      using all by (auto)
    have memimp:"\<And>L. (\<forall>x. List.member L x \<longrightarrow> Ssafe x) \<Longrightarrow>  (foldr (\<lambda>x acc. acc \<and> Ssafe x)  L True)"
      subgoal for L
        apply(induction L)
        by(auto simp add: member_rec)
      done
    show "foldr (\<lambda>x acc. acc \<and> Ssafe x)  (fst R) True" 
      apply(rule memimp)
      using all mem memimp by auto
  next
    fix i
    assume foldr:"foldr (\<lambda>x acc. acc \<and> Ssafe x)  (fst R) True"
    assume i:"i < length (fst R)"
  then have mem:"List.member (fst R) (fst R! i)"
    using nth_member i by auto
  have memimp:"\<And>L x. (foldr (\<lambda>x acc. acc \<and> Ssafe x)  L True) \<Longrightarrow>List.member L x \<Longrightarrow> Ssafe x"
      subgoal for L
        apply(induction L)
        by(auto simp add: member_rec)
      done
    show "Ssafe (fst R ! i)" 
      apply(rule memimp[where L="fst R"])
       apply(rule foldr)
      by (rule mem)
qed


subsection \<open>Soundness of substitution rule\<close>
theorem subst_rule:
  assumes sound:"sound R"
  assumes Radmit:"Radmit \<sigma> R"
  assumes FVS:"FVS \<sigma> = {}"
  assumes Rsafe:"Rsafe R"
  assumes ssafe:"ssafe \<sigma>"
  shows "sound (Rsubst R \<sigma>)"
proof -
  obtain SG and C where Rdef:"R = (SG,C)" by (cases R, auto)
  obtain SG' and C' where Rdef':"Rsubst R \<sigma> = (SG',C')" by (cases R, auto)
  obtain \<Gamma>C and \<Delta>C where Cdef:"C = (\<Gamma>C, \<Delta>C)" by (cases C, auto)
  obtain \<Gamma>C' and \<Delta>C' where C'def:"C' = (\<Gamma>C', \<Delta>C')" by (cases C', auto)
  have CC':"(Ssubst (\<Gamma>C, \<Delta>C) \<sigma>) = (\<Gamma>C', \<Delta>C')"
    using Rdef Rdef' Cdef C'def by auto
  have "\<And>I \<nu>. is_interp I \<Longrightarrow> (\<And>\<Gamma> \<Delta> \<omega>  . List.member SG' (\<Gamma>, \<Delta>) \<Longrightarrow> \<omega> \<in> seq_sem I (\<Gamma>, \<Delta>)) \<Longrightarrow> \<nu> \<in> seq_sem I C'"
  proof -
    fix I::"interp" and \<nu>::"state"
    assume good_interp:"is_interp I"
    assume prems:"(\<And>\<Gamma> \<Delta> \<omega>. List.member SG' (\<Gamma>, \<Delta>) \<Longrightarrow> \<omega> \<in> seq_sem I (\<Gamma>, \<Delta>))"
    have good_interp':"\<And>\<omega>. is_interp (adjoint I \<sigma> \<omega>)"
      using adjoint_safe[OF good_interp ] ssafe[unfolded ssafe_def] by (metis option.simps(5))
    have sound:"\<And>\<omega>. (\<And>\<phi> \<nu> . List.member SG \<phi> \<Longrightarrow> \<nu> \<in> seq_sem (adjoint I \<sigma> \<omega>) \<phi>) \<Longrightarrow> \<omega> \<in> seq_sem (adjoint I \<sigma> \<omega>) (\<Gamma>C, \<Delta>C)"
      using soundD_memv[of SG C] sound good_interp' Rdef Cdef by auto
    have SadmitC:"Sadmit \<sigma> (\<Gamma>C, \<Delta>C)" 
      using Radmit unfolding Radmit_def Rdef Cdef by auto
    have SsafeC:"Ssafe (\<Gamma>C, \<Delta>C)"       using Rsafe unfolding Rsafe_def Rdef Cdef by auto
    have seq_sem:"\<nu> \<in> seq_sem (adjoint I \<sigma> \<nu>) (\<Gamma>C, \<Delta>C)"
    proof(rule sound)
      fix S :: "sequent" and \<nu>'
      assume mem:"List.member SG S"
      obtain \<Gamma>S \<Delta>S where Sdef:"S = (\<Gamma>S, \<Delta>S)" by (cases S, auto)
      from mem obtain di where di:"di < length SG \<and> SG ! di = S"
      by (meson in_set_conv_nth in_set_member)
      have SadmitS:"Sadmit \<sigma> (\<Gamma>S, \<Delta>S)"
        using Rdef Sdef di Radmit Radmit_def by auto
      have SsafeS:"Ssafe (\<Gamma>S, \<Delta>S)"
        using Rsafe unfolding Rsafe_def Rdef Cdef using Sdef mem di by auto
      have map_mem:"\<And>f L x. List.member L x \<Longrightarrow> List.member (map f L) (f x)"
        subgoal for f L x 
          by (induction L, auto simp add: member_rec)
        done
      let ?S' = "(Ssubst (\<Gamma>S, \<Delta>S) \<sigma>)"
      have eq:"Ssubst S \<sigma> = (map (\<lambda>\<phi>. Fsubst \<phi> \<sigma>) \<Gamma>S, map (\<lambda>\<phi>. Fsubst \<phi> \<sigma>) \<Delta>S)" 
        using Sdef by auto
      from Sdef have mem':"List.member SG' (fst ?S', snd ?S')"
        using mem Rdef Rdef' eq map_mem[of SG S "(\<lambda>x. Ssubst x \<sigma>)"] by auto
      have "\<nu>' \<in> seq_sem I (fst ?S', snd ?S')" by (rule prems[OF mem', of \<nu>'])
      then have "\<nu>' \<in> seq_sem (adjoint I \<sigma> \<nu>') S"
        using subst_sequent[OF good_interp SadmitS SsafeS ssafe, of \<nu>']
        Sdef by auto
      have VA:"Vagree \<nu> \<nu>' (FVS \<sigma>)" using FVS unfolding Vagree_def by auto
    from ssafe have ssafes:"(\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dsafe f')"
      "(\<And>f f'. SFunls \<sigma> f = Some f' \<Longrightarrow> dsafe f')"
        "(\<And>f f'. SPredicates \<sigma> f = Some f' \<Longrightarrow> fsafe f')"
      unfolding ssafe_def  using dfree_is_dsafe
      by (metis option.simps(5))+

      show "\<nu>' \<in> seq_sem (adjoint I \<sigma> \<nu>) S"
        using adjoint_consequence[OF ssafes] VA ssafe[unfolded ssafe_def]
          \<open>\<nu>' \<in> seq_sem (adjoint I \<sigma> \<nu>') S\<close> dfree_is_dsafe good_interp
        by auto
      qed
    have "\<nu> \<in> seq_sem I (\<Gamma>C', \<Delta>C')"
      using subst_sequent[OF good_interp SadmitC SsafeC ssafe, of \<nu>] seq_sem Cdef C'def CC'
      by auto
    then show  "\<nu> \<in> seq_sem I C'" using C'def by auto
    qed
  then show ?thesis
    apply(rule soundI_memv')
      using Rdef' by auto
qed

end