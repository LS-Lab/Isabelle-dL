theory Lib
imports
  Complex_Main HOL
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
begin
(* Lemmas that could be part of the standard libraries and don't have anything to do with dL specifically. *)
lemma vec_extensionality:"(\<And>i. v$i = w$i) \<Longrightarrow> (v = w)"
  by (simp add: vec_eq_iff)

lemma norm_axis: "norm (axis i x) = norm x"
  unfolding axis_def norm_vec_def
  by (simp add: if_distrib[where f=norm] setL2_def if_distrib[where f="\<lambda>x. x\<^sup>2"] setsum.If_cases)

lemma bounded_linear_axis: "bounded_linear (axis i)"
proof
  show "axis i (x + y) = axis i x + axis i y" "axis i (r *\<^sub>R x) = r *\<^sub>R axis i x" for x y :: "'a" and r
    by (auto simp: vec_eq_iff axis_def)
  show "\<exists>K. \<forall>x::'a. norm (axis i x) \<le> norm x * K"
    by (auto simp add: norm_axis intro!: exI[of _ 1])
qed

lemma has_derivative_vec[derivative_intros]:
  assumes "\<And>i. ((\<lambda>x. f i x) has_derivative (\<lambda>h. f' i h)) F"
  shows "((\<lambda>x. \<chi> i. f i x) has_derivative (\<lambda>h. \<chi> i. f' i h)) F"
proof -
  have *: "(\<chi> i. f i x) = (\<Sum>i\<in>UNIV. axis i (f i x))" "(\<chi> i. f' i x) = (\<Sum>i\<in>UNIV. axis i (f' i x))" for x
    by (simp_all add: axis_def setsum.If_cases vec_eq_iff)
  show ?thesis
    unfolding *
    by (intro has_derivative_setsum bounded_linear.has_derivative[OF bounded_linear_axis] assms)
qed

lemma has_derivative_proj:
  fixes j::"('a::finite)" 
  fixes f::"'a \<Rightarrow> real \<Rightarrow> real"
  assumes assm:"((\<lambda>x. \<chi> i. f i x) has_derivative (\<lambda>h. \<chi> i. f' i h)) F"
  shows "((\<lambda>x. f j x) has_derivative (\<lambda>h. f' j h)) F"
  proof -
    have bounded_proj:"bounded_linear (\<lambda> x::(real^'a). x $ j)"
      by (simp add: bounded_linear_component_cart)
    show "?thesis"
      using bounded_linear.has_derivative[OF bounded_proj, of "(\<lambda>x. \<chi> i. f i x)" "(\<lambda>h. \<chi> i. f' i h)", OF assm]
      by auto
  qed
  


lemma has_vector_derivative_zero_constant:
  assumes "convex s"
  assumes "\<And>x. x \<in> s \<Longrightarrow> (f has_vector_derivative 0) (at x within s)"
  obtains c where "\<And>x. x \<in> s \<Longrightarrow> f x = c"
  using has_derivative_zero_constant[of s f] assms
  by (auto simp: has_vector_derivative_def)

lemma has_vderiv_on_zero_constant:
  assumes "convex s"
  assumes "(f has_vderiv_on (\<lambda>h. 0)) s"
  obtains c where "\<And>x. x \<in> s \<Longrightarrow> f x = c"
  using has_vector_derivative_zero_constant[of s f] assms
  by (auto simp: has_vderiv_on_def)

lemma constant_when_zero:
  fixes v::"real \<Rightarrow> (real, 'i::finite) vec"
  assumes x0: "(v 0) $ i = x0"
  assumes sol: "(v solves_ode f) UNIV UNIV"
  assumes f0: "\<And>t x. f t x $ i = 0"
  assumes "0 \<le> t"
  shows "v t $ i = x0"
proof -
  from solves_odeD[OF sol]
  have deriv: "(v has_vderiv_on (\<lambda>t. f t (v t))) UNIV" by simp
  then have "((\<lambda>t. v t $ i) has_vderiv_on (\<lambda>t. 0)) UNIV"
    using f0
    by (auto simp: has_vderiv_on_def has_vector_derivative_def cart_eq_inner_axis
      intro!: derivative_eq_intros)
  from has_vderiv_on_zero_constant[OF convex_UNIV this]
  obtain c where "\<And>x. x \<in> UNIV \<Longrightarrow> v x $ i = c" by blast
  with x0 have "c = x0" "v t $ i = c"using \<open>0 \<le> t\<close> by auto
  then show ?thesis by simp
qed

  
lemma
  solves_ode_subset:
  assumes x: "(x solves_ode f) T X"
  assumes s: "S \<subseteq> T"
  shows "(x solves_ode f) S X"
  apply(rule solves_odeI)
  using has_vderiv_on_subset s solves_ode_vderivD x apply force
  using assms by (auto intro!: solves_odeI dest!: solves_ode_domainD)

lemma
  solves_ode_supset_range:
  assumes x: "(x solves_ode f) T X"
  assumes y: "X \<subseteq> Y"
  shows "(x solves_ode f) T Y"
  apply(rule solves_odeI)
  using has_vderiv_on_subset y solves_ode_vderivD x apply force
  using assms by (auto intro!: solves_odeI dest!: solves_ode_domainD)

lemma
  usolves_ode_subset:
  assumes x: "(x usolves_ode f from t0) T X"
  assumes s: "S \<subseteq> T"
  assumes t0: "t0 \<in> S"
  assumes S: "is_interval S"
  shows "(x usolves_ode f from t0) S X"
    proof (rule usolves_odeI)
  note usolves_odeD[OF x]
  show "(x solves_ode f) S X" by (rule solves_ode_subset; fact)
  show "t0 \<in> S" "is_interval S" by(fact+)
  fix z t
  assume s: "{t0 -- t} \<subseteq> S" and z: "(z solves_ode f) {t0 -- t} X" and z0: "z t0 = x t0"
  then have "t0 \<in> {t0 -- t}" "is_interval {t0 -- t}"
    by auto
  moreover note s
  moreover have "(z solves_ode f) {t0--t} X"
    using solves_odeD[OF z] \<open>S \<subseteq> T\<close>
    by (intro solves_ode_subset_range[OF z]) force
  moreover note z0
  moreover have "t \<in> {t0 -- t}" by simp
  ultimately show "z t = x t"
    by (meson \<open>\<And>z ta T'. \<lbrakk>t0 \<in> T'; is_interval T'; T' \<subseteq> T; (z solves_ode f) T' X; z t0 = x t0; ta \<in> T'\<rbrakk> \<Longrightarrow> z ta = x ta\<close> assms(2) dual_order.trans)
qed

lemma example:
  fixes x t::real and i::"('sz::finite)"
  assumes "t > 0"
  shows "x = (ll_on_open.flow UNIV (\<lambda>t. \<lambda>x. \<chi> (i::('sz::finite)). 0) UNIV 0 (\<chi> i. x) t) $ i"
proof -
  let ?T = UNIV
  let ?f = "(\<lambda>t. \<lambda>x. \<chi> i::('sz::finite). 0)"
  let ?X = UNIV
  let ?t0.0 = 0
  let ?x0.0 = "\<chi> i::('sz::finite). x"
  interpret ll: ll_on_open "UNIV" "(\<lambda>t x. \<chi> i::('sz::finite). 0)" UNIV
    apply unfold_locales
    using gt_ex lipschitz_constI
    by (force simp: interval_def continuous_on_def local_lipschitz_def)+
  have foo1:"?t0.0 \<in> ?T" by auto
  have foo2:"?x0.0 \<in> ?X" by auto
  let ?v = "ll.flow  ?t0.0 ?x0.0"
  from ll.flow_solves_ode[OF foo1 foo2]
  have solves:"(ll.flow  ?t0.0 ?x0.0 solves_ode ?f) (ll.existence_ivl  ?t0.0 ?x0.0) ?X"  by (auto)
  then have solves:"(?v solves_ode ?f) (ll.existence_ivl  ?t0.0 ?x0.0) ?X" by auto
  have thex0: "(?v ?t0.0) $ (i::('sz::finite)) = x" by auto
  have sol_help: "(?v solves_ode ?f) (ll.existence_ivl  ?t0.0 ?x0.0) ?X" using solves by auto
  have ivl:"ll.existence_ivl ?t0.0 ?x0.0 = UNIV"
    by (rule ll.existence_ivl_eq_domain)
     (auto intro!: exI[where x=0] simp: vec_eq_iff)
  have sol: "(?v solves_ode ?f) UNIV ?X" using solves ivl by auto
  have thef0: "\<And>t x. ?f t x $ i = 0" by auto
  have gre:"0 \<le> t" using \<open>0 < t\<close> by auto
  from constant_when_zero [OF thex0 sol thef0 gre] have "?v t $ i = x"
    by auto
  thus ?thesis by auto
 qed

end