theory "Frechet_Correctness"
imports
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
  "./Lib"
  "./Syntax"
  "./Denotational_Semantics"
  "./Ids"
begin
context ids begin
subsection \<open>Characterization of Term Derivatives\<close>
text \<open>
 This section builds up to a proof that in well-formed interpretations, all
 terms have derivatives, and those derivatives agree with the expected rules
 of derivatives. In particular, we show the [frechet] function given in the
 denotational semantics is the true Frechet derivative of a term. From this
 theorem we can recover all the standard derivative rules as corollaries.
\<close>

lemma inner_prod_eq:
  fixes i::"'a::finite"
  shows "(\<lambda>(v::'a Rvec). v \<bullet> basis_vector i) = (\<lambda>(v::'a Rvec). v $ i)"
  unfolding cart_eq_inner_axis basis_vector.simps axis_def by (simp add: eq_commute)

theorem svar_deriv:
  fixes x:: "'sv::finite" and \<nu>:: "'sv Rvec" and F::"real filter"
  shows "((\<lambda>v. v $ x) has_derivative (\<lambda>v'. v' \<bullet> (\<chi> i. if x = i then 1 else 0))) (at \<nu>)"
proof -
  let ?f = "(\<lambda>v. v)"
  let ?f' = "(\<lambda>v'. v')"
  let ?g = "(\<lambda>v. basis_vector x)"
  let ?g' = "(\<lambda>v. 0)"
  have id_deriv: "(?f has_derivative ?f') (at \<nu>) "
  by (rule has_derivative_ident)
  have const_deriv: "(?g has_derivative ?g') (at \<nu>)"
  by (rule has_derivative_const)
  have inner_deriv:"((\<lambda>x. inner (?f x) (?g x)) has_derivative
                     (\<lambda>h. inner (?f \<nu>) (?g' h) + inner (?f' h) (?g \<nu>))) (at \<nu>)"
  by (intro has_derivative_inner [OF id_deriv const_deriv])

  from inner_prod_eq
  have left_eq: "(\<lambda>x. inner (?f x) (?g x)) = (\<lambda>v. vec_nth v x)"
  by (auto)
  from inner_deriv and inner_prod_eq
  have better_deriv:"((\<lambda>v. vec_nth v x) has_derivative
                     (\<lambda>h. inner (?f \<nu>) (?g' h) + inner (?f' h) (?g \<nu>))) (at \<nu>)"
  by (metis (no_types, lifting) UNIV_I has_derivative_transform)
  have deriv_eq: "(\<lambda>h. inner (?f \<nu>) (?g' h) + inner (?f' h) (?g \<nu>))
    = (\<lambda>v'. inner v' (\<chi> i. if x = i then 1 else 0))"
  by(auto)
  from better_deriv and deriv_eq show ?thesis by (auto)
qed

lemma function_case_inner:
  assumes good_interp:
    "(\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x))"
  assumes IH:"((\<lambda>v. \<chi> i. sterm_sem I (args i) v)
             has_derivative (\<lambda> v. (\<chi> i. frechet I (args i) \<nu> v))) (at \<nu>)"
  shows  "((\<lambda>v. Functions I f (\<chi> i. sterm_sem I (args i) v))
            has_derivative (\<lambda>v. frechet I ($f f args) \<nu> v)) (at \<nu>)"
proof -
  let ?h = "(\<lambda>v. Functions I f (\<chi> i. sterm_sem I (args i) v))"
  let ?h' = "frechet I ($f f args) \<nu>"
  let ?g = "(\<lambda>v. \<chi> i. sterm_sem I (args i) v)"
  let ?g' = "(\<lambda>v. \<chi> i. frechet I (args i) \<nu> v)"
  let ?f = "(\<lambda>y. Functions I f y)"
  let ?f' = "FunctionFrechet I f (?g \<nu>)"
  have hEqFG:  "?h  = ?f  o ?g" by (auto)
  have hEqFG': "?h' = ?f' o ?g'"
    proof -
      have frechet_def:"frechet I (Function f args) \<nu>
          = (\<lambda>v'. FunctionFrechet I f (?g \<nu>) (\<chi> i. frechet I (args i) \<nu> v'))"
      by (auto)
      have composition:
        "(\<lambda>v'. FunctionFrechet I f (?g \<nu>) (\<chi> i. frechet I (args i) \<nu> v'))
      = (FunctionFrechet I f (?g \<nu>)) o (\<lambda> v'. \<chi> i. frechet I (args i) \<nu> v')"
      by (auto)
      from frechet_def and composition show ?thesis by (auto)
    qed
  have fDeriv: "(?f has_derivative ?f') (at (?g \<nu>))"
    using  good_interp is_interp_def by blast
  from IH have gDeriv: "(?g has_derivative ?g') (at \<nu>)" by (auto)
  from fDeriv and gDeriv
  have composeDeriv: "((?f o ?g) has_derivative (?f' o ?g')) (at \<nu>)"
    using diff_chain_at good_interp by blast
  from hEqFG hEqFG' composeDeriv show ?thesis by (auto)
qed

lemma func_lemma2:"\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x) \<Longrightarrow>
    (\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> (sterm_sem I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)) \<Longrightarrow>
    ((\<lambda>v. Functions I f (vec_lambda(\<lambda>i. sterm_sem I (args i) v))) has_derivative frechet I ($f f args) \<nu>) (at \<nu>)"
proof -
  assume a1: "\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x)"
  assume a2: "\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> (sterm_sem I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)"
  have "\<forall>f fa v. (\<exists>fb. \<not> (f (fb::'a) has_derivative fa fb (v::(real, 'a) vec)) (at v)) \<or> ((\<lambda>v. (\<chi> fa. (f fa v::real))) has_derivative (\<lambda>va. (\<chi> f. fa f v va))) (at v)"
    using has_derivative_vec by force
  then have "((\<lambda>v. \<chi> f. sterm_sem I (args f) v) has_derivative (\<lambda>v. \<chi> f. frechet I (args f) \<nu> v)) (at \<nu>)"
    by (auto simp add: a2 has_derivative_vec)
  then show "((\<lambda>v. Functions I f (vec_lambda(\<lambda>f. sterm_sem I (args f) v))) has_derivative frechet I ($f f args) \<nu>) (at \<nu>)"
    using a1 function_case_inner by blast
qed

lemma func_lemma:
  "is_interp I \<Longrightarrow>
  (\<And>\<theta> :: ('a::finite, 'c::finite) trm. \<theta> \<in> range args \<Longrightarrow> (sterm_sem I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)) \<Longrightarrow>
  (sterm_sem I ($f f args) has_derivative frechet I ($f f args) \<nu>) (at \<nu>)"
apply(simp only: sfunction_case is_interp_def function_case_inner)
apply(erule func_lemma2)
apply(auto)
done

(* TODO: Should be able to remove these lemmas by adding some inductive_simp rules *)
lemma dfree_vac1: "\<not> dfree ($' var)"
  by (auto elim: dfree.cases)

lemma dfree_vac2: "\<not> dfree (Differential d)"
  by (auto elim: dfree.cases)

(* Our syntactically-defined derivatives of terms agree with the actual derivatives of the terms.
 Since our definition of derivative is total, this gives us that derivatives are "decidable" for
 terms (modulo computations on reals) and that they obey all the expected identities, which gives
 us the axioms we want for differential terms essentially for free.
 *)
lemma frechet_correctness:
  fixes I :: "('a::finite, 'b::finite, 'c::finite) interp" and \<nu>
  assumes good_interp: "is_interp I"
  shows "dfree \<theta> \<Longrightarrow> FDERIV (sterm_sem I \<theta>) \<nu> :> (frechet I \<theta> \<nu>)"
proof (induct rule: dfree.induct)
  case dfree_Var then show ?case
    by (simp add: svar_case svar_deriv)
next
  case (dfree_Fun args i) with good_interp show ?case
    by (intro func_lemma) auto
qed auto

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

lift_definition blin_frechet::"('sf, 'sc, 'sz) interp \<Rightarrow> ('sf,'sz) trm \<Rightarrow> (real, 'sz) vec  \<Rightarrow> (real, 'sz) vec \<Rightarrow>\<^sub>L real" is "frechet"
  sorry
lemmas [simp] = blin_frechet.rep_eq

lemma frechet_blin:"(\<lambda>v. Blinfun (\<lambda>v'. frechet I \<theta> v v')) = blin_frechet I \<theta>"
  sorry


lemma frechet_continuous:
fixes I :: "('sf, 'sc, 'sz) interp"
assumes good_interp:"is_interp I"
(* TODO: Needs GREAT interp as well, i.e. continuous derivatives *)
shows "dfree \<theta> \<Longrightarrow> continuous_on UNIV (blin_frechet I \<theta>)"    
proof (induction rule: dfree.induct)
  case (dfree_Var i)
  have bounded_linear:"bounded_linear (\<lambda> \<nu>'. \<nu>' \<bullet> basis_vector i )"
    by (simp add: bounded_linear_component)
  have cont:"continuous_on UNIV (\<lambda>\<nu>. Blinfun(\<lambda> \<nu>'. \<nu>' \<bullet> basis_vector i ))"
    using continuous_on_const by blast
  have eq:"\<And>\<nu> \<nu>'. (\<lambda>\<nu>. Blinfun(\<lambda> \<nu>'. \<nu>' \<bullet> basis_vector i)) \<nu> \<nu>' = (blin_frechet I (Var i)) \<nu> \<nu>'"
    apply(simp)
    using bounded_linear 
    by (metis blinfun_inner_left.abs_eq blinfun_inner_left.rep_eq)
  have eq':"(\<lambda>\<nu>. Blinfun(\<lambda> \<nu>'. \<nu>' \<bullet> basis_vector i)) = (blin_frechet I (Var i))"
    apply(rule ext)
    apply(rule blinfun_eqI)
    using eq by auto
  then show ?case by (metis cont)
next
  case (dfree_Const r)
  have bounded_linear:"bounded_linear (\<lambda> \<nu>'. 0)" by (simp)
  have cont:"continuous_on UNIV (\<lambda>\<nu>. Blinfun(\<lambda> \<nu>'. 0))"
    using continuous_on_const by blast
  have eq':"(\<lambda>\<nu>. Blinfun(\<lambda> \<nu>'. 0)) = (blin_frechet I (Const r))"
    apply(rule ext)
    apply(rule blinfun_eqI)
    apply auto
    using bounded_linear
    by (metis zero_blinfun.abs_eq zero_blinfun.rep_eq)
  then show ?case by (metis cont)
next
  case (dfree_Fun args f)
  assume IH:"\<And>i. continuous_on UNIV (blin_frechet I (args i))"
  (* TODO: Use greatness of interpretation here. *)
  have cont:"continuous_on UNIV (\<lambda>v. Blinfun(\<lambda>v'. FunctionFrechet I f (\<chi> i. sterm_sem I (args i) v) (\<chi> i. frechet I (args i) v v')))"
    sorry
  have eq:"(\<lambda>v. Blinfun(\<lambda>v'. FunctionFrechet I f (\<chi> i. sterm_sem I (args i) v) (\<chi> i. frechet I (args i) v v'))) 
    = (blin_frechet I (Function f args))"
    using frechet_blin[of I "(Function f args)"] by auto
  then show ?case by (metis cont)
next
  case (dfree_Plus \<theta>\<^sub>1 \<theta>\<^sub>2)
  assume IH1:"continuous_on UNIV (blin_frechet I \<theta>\<^sub>1)"
  assume IH2:"continuous_on UNIV (blin_frechet I \<theta>\<^sub>2)"
  have bounded_linear:"\<And>v. bounded_linear (\<lambda>v'. frechet I \<theta>\<^sub>1 v v' + frechet I \<theta>\<^sub>2 v v')" sorry
  have eq2:"(\<lambda>v. blin_frechet I \<theta>\<^sub>1 v + blin_frechet I \<theta>\<^sub>2 v) = blin_frechet I (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
    using frechet_blin[of I "(Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"] frechet_blin[of I "\<theta>\<^sub>1"] frechet_blin[of I "\<theta>\<^sub>2"] 
    using bounded_linear sorry
  have cont:"continuous_on UNIV (\<lambda>v. blin_frechet I \<theta>\<^sub>1 v + blin_frechet I \<theta>\<^sub>2 v)"
    using continuous_on_add dfree_Plus.IH(1) dfree_Plus.IH(2) by blast 
  then show ?case using cont eq2 by metis 
next
  case (dfree_Times \<theta>\<^sub>1 \<theta>\<^sub>2)
  assume IH1:"continuous_on UNIV (blin_frechet I \<theta>\<^sub>1)"
  assume IH2:"continuous_on UNIV (blin_frechet I \<theta>\<^sub>2)"
  have bounded_linear:"\<And>v. bounded_linear (\<lambda>v'. sterm_sem I \<theta>\<^sub>1 v * frechet I \<theta>\<^sub>2 v v' + frechet I \<theta>\<^sub>1 v v' * sterm_sem I \<theta>\<^sub>2 v)" sorry
  have cont:"continuous_on UNIV (\<lambda>v. Blinfun (\<lambda>v'. sterm_sem I \<theta>\<^sub>1 v * frechet I \<theta>\<^sub>2 v v' + frechet I \<theta>\<^sub>1 v v' * sterm_sem I \<theta>\<^sub>2 v))"
    using bounded_linear frechet_blin[of I \<theta>\<^sub>1] bounded_linear frechet_blin[of I \<theta>\<^sub>2]
    sorry
  have eq:"(\<lambda>v. Blinfun (\<lambda>v'. sterm_sem I \<theta>\<^sub>1 v * frechet I \<theta>\<^sub>2 v v' + frechet I \<theta>\<^sub>1 v v' * sterm_sem I \<theta>\<^sub>2 v)) = blin_frechet I (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"
    using frechet_blin[of I "(Times \<theta>\<^sub>1 \<theta>\<^sub>2)"]
    by auto
  then show ?case by (metis cont)
qed
end end

