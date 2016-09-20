theory Lib
imports
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
begin
subsection \<open>Library of assorted things\<close>
text\<open>General lemmas that don't have anything to do with dL specifically and could be fit for 
  general-purpose libraries, mostly dealing with derivatives, ODEs and vectors.\<close>

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

lemma bounded_linear_vec:
  fixes f::"('a::finite) \<Rightarrow> 'b::real_normed_vector \<Rightarrow> 'c::real_normed_vector"
  assumes bounds:"\<And>i. bounded_linear (f i)"
  shows "bounded_linear (\<lambda>x. \<chi> i. f i x)"
proof -
  let ?g = "(\<lambda>x. \<chi> i. f i x)"
  have additives:"\<And>i. additive (f i)"
    using bounds unfolding bounded_linear_def bounded_linear_axioms_def linear_def by auto
  have additive:"additive (\<lambda>x. \<chi> i. f i x)"
    using additives unfolding additive_def apply auto 
    by (metis (mono_tags, lifting) Cart_lambda_cong plus_vec_def vec_lambda_beta)
  have scales:"\<And>i. (\<forall>r x. f i (r *\<^sub>R x) = r *\<^sub>R f i x)"
    using bounds unfolding bounded_linear_def bounded_linear_axioms_def linear_def linear_axioms_def by auto
  have scale:"(\<forall>r x. ?g (r *\<^sub>R x) = r *\<^sub>R ?g x)"
    using scales
  proof -
    have f1: "\<And>v0_1 v1_0. (\<chi> a. f a (v0_1 *\<^sub>R v1_0)) = (\<chi> a. v0_1 *\<^sub>R (\<chi> a. f a v1_0) $ a)"
      using scales by force
    obtain rr :: real and bb :: 'b where
      "(\<exists>v0 v1. (\<chi> uub. f uub (v0 *\<^sub>R v1)) \<noteq> (\<chi> uub. v0 *\<^sub>R (\<chi> uua. f uua v1) $ uub)) = ((\<chi> uub. f uub (rr *\<^sub>R bb)) \<noteq> (\<chi> uub. rr *\<^sub>R (\<chi> uua. f uua bb) $ uub))"
      by blast
    then show ?thesis
      using f1 by (simp add: scaleR_vec_def)
  qed
  have norms:"\<And>i. (\<exists>K. \<forall>x. norm (f i x) \<le> norm x * K)"
    using bounds unfolding bounded_linear_def bounded_linear_axioms_def by auto
  let ?Ki = "(\<lambda>i. SOME K. \<forall>x. norm (f i x) \<le> norm x * K)"
  have each_norm:"\<And>i.  \<forall>x. norm (f i x) \<le> norm x * (?Ki i)"
    using norms by (smt someI_ex)
  let ?TheK = "(\<Sum> i \<in> (UNIV::'a set).?Ki i)"
  have axes:"\<And>x. (?g x) = (\<Sum> i\<in>(UNIV::'a set). (axis i (f i x)))"
    unfolding axis_def apply(rule vec_extensionality, auto)
    by (simp add: setsum.delta')
  have triangle:"\<And>x. (\<Sum> i \<in> (UNIV::'a set). norm (axis i (f i x))) \<ge> norm (\<Sum> i \<in> (UNIV::('a::finite) set). axis i (f i x))"
    using norm_setsum by blast
  have triangle':"\<And>x. (\<Sum> i \<in> (UNIV::'a set). norm (f i x)) \<ge> norm (\<Sum> i \<in> (UNIV::('a::finite) set). axis i (f i x))"
    using norm_axis
    by (simp add: norm_axis Real_Vector_Spaces.setsum_norm_le)
  have norms':"\<And>x. (\<Sum> i\<in> (UNIV::'a set). norm (f i x)) \<le> norm x * ?TheK"
    using norms  each_norm axes triangle'
    by (simp add: setsum_mono setsum_right_distrib)
  have leq:"\<And>x. norm(?g x) \<le> norm x * ?TheK" using axes triangle' norms' 
    using dual_order.trans by fastforce
  have norm:"(\<exists>K. \<forall>x. norm (\<chi> i. f i x) \<le> norm x * K)"
    using leq by blast
  have linears:"\<And>i. linear (f i)"
    using bounds unfolding bounded_linear_def bounded_linear_axioms_def by auto
  have linear:"linear (\<lambda>x. \<chi> i. f i x)"
    using linears unfolding linear_def linear_axioms_def using additive scale by  auto
  show ?thesis
    unfolding bounded_linear_def bounded_linear_axioms_def
    using linear norm by auto
qed

lift_definition blinfun_vec::"('a::finite \<Rightarrow> 'b::real_normed_vector \<Rightarrow>\<^sub>L real) \<Rightarrow> 'b \<Rightarrow>\<^sub>L (real ^ 'a)" is "(\<lambda>(f::('a \<Rightarrow> 'b \<Rightarrow> real)) (x::'b). \<chi> (i::'a). f i x)"
  by(rule bounded_linear_vec, simp)  
lemmas [simp] = blinfun_vec.rep_eq

lemma continuous_blinfun_vec:"(\<And>i. continuous_on UNIV (blinfun_apply (g i))) \<Longrightarrow> continuous_on UNIV (blinfun_vec g)"
  by (simp add: continuous_on_vec_lambda)  

(*lemma continuous_blinfun_vec':"continuous blinfun_vec"*)

lemma blinfun_elim:"\<And>g. (blinfun_apply (blinfun_vec g)) = (\<lambda>x. \<chi> i. g i x)"
  using blinfun_vec.rep_eq by auto

lemma continuous_vec:
  fixes f::"'a::finite \<Rightarrow> 'b::metric_space \<Rightarrow> real \<Rightarrow>\<^sub>L real"
  fixes S::"'b set"
  assumes conts:"\<And>i. continuous_on UNIV (f i)"
  shows "continuous_on UNIV (\<lambda>x. blinfun_vec (\<lambda> i. f i x))"
proof (auto simp add:  LIM_def continuous_on_def)
  fix x1 and \<epsilon>::real
  assume \<epsilon>:"0 < \<epsilon>"
  let ?n = "card (UNIV::'a set)"
  have conts':" \<And>i x1 \<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<exists>\<delta>>0. \<forall>x2. x2 \<noteq> x1 \<and> dist x2 x1 < \<delta> \<longrightarrow> dist (f i  x2) (f i x1) < \<epsilon>"  
    using conts by(auto  simp add:  LIM_def continuous_on_def)
  have conts'':"\<And>i. \<exists>\<delta>>0. \<forall>x2. x2 \<noteq> x1 \<and> dist x2 x1 < \<delta> \<longrightarrow> dist (f i  x2) (f i x1) < (\<epsilon>/?n)"
    subgoal for i using conts'[of "\<epsilon> / ?n"  x1 i] \<epsilon> by auto done
  let ?f = "(\<lambda>x. blinfun_vec (\<lambda> i. f i x))"
  let ?\<delta>i = "(\<lambda>i. SOME \<delta>. (\<delta>>0 \<and> (\<forall>x2. x2 \<noteq> x1 \<and> dist x2 x1 < \<delta> \<longrightarrow> dist (f i  x2) (f i x1) < (\<epsilon>/?n))))"
  let ?\<delta> = "INF i:UNIV. ?\<delta>i i"
  have conts''':"\<And>i x2. x2 \<noteq> x1 \<Longrightarrow> dist x2 x1 < ?\<delta>i i \<Longrightarrow> dist (f i  x2) (f i x1) < (\<epsilon>/?n)"
    using conts'' sorry
  have \<delta>:"?\<delta> > 0 " sorry
  have \<delta>s:"\<And>i. ?\<delta> \<le> ?\<delta>i i" sorry
  have "\<And>x2. x2 \<noteq> x1 \<and> dist x2 x1 < ?\<delta> \<Longrightarrow> dist (blinfun_vec (\<lambda>i. f i x2)) (blinfun_vec (\<lambda>i. f i x1)) < \<epsilon>"
    proof (auto)
      fix x2
      assume ne:"x2 \<noteq> x1"
      assume dist:"dist x2 x1 < ?\<delta>"
      have dists:"\<And>i. dist x2 x1 < ?\<delta>i i"
        subgoal for i using dist \<delta>s[of i] by linarith done
      have euclid:"\<And>y. norm(?f x1 y - ?f x2 y) = (setL2 (\<lambda>i. norm(f i x1 y - f i x2 y)) UNIV)"
        by (simp add: norm_vec_def)
      have finite:"finite (UNIV::'a set)" by auto
      have nonempty: "(UNIV::'a set) \<noteq> {}" by auto
      have SUP_leq:"\<And>f g S. (\<And>x. x \<in> S \<Longrightarrow> f x \<le> g x) \<Longrightarrow> (SUP x:S. f x) \<le> (SUP x:S. g x)" 
        sorry
      have SUP_sum_comm:"\<And>f R S. finite S \<Longrightarrow> (SUP x:R . (\<Sum>y \<in> S. f x y)) \<le> (\<Sum>y \<in> S. (SUP x:R. f x y))"
        sorry
      have SUM_leq:"\<And>S f g . S \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> f x < g x) \<Longrightarrow> (\<Sum>x\<in>S. f x) < (\<Sum>x\<in>S. g x)"
        sorry
      have L2:"\<And>f S. setL2 (\<lambda>x. norm(f x)) S \<le> (\<Sum>x \<in> S. norm(f x))"
        using setL2_le_setsum norm_ge_zero by metis
      have L2':"\<And>y. (setL2 (\<lambda>i. norm(f i x1 y - f i x2 y)) UNIV)/norm(y) \<le> (\<Sum>i\<in>UNIV. norm(f i x1 y - f i x2 y))/norm(y)"
        subgoal for y
          using L2[of "(\<lambda> x. f x x1 y - f x x2 y)" UNIV]
          by (auto simp add: divide_right_mono)
        done
      have "\<And>i. (SUP y:UNIV.  norm((f i x1 - f i x2) y)/norm(y)) = norm(f i x1 - f i x2)"
        by (simp add: onorm_def norm_blinfun.rep_eq)
      then have each_norm:"\<And>i. (SUP y:UNIV.  norm(f i x1 y - f i x2 y)/norm(y)) = norm(f i x1 - f i x2)"
        by (metis (no_types, lifting) SUP_cong blinfun.diff_left) 
      have "dist (?f x2) (?f x1) = norm((?f x2) - (?f x1))"
        by (simp add: dist_blinfun_def)
      (* TODO: some mess up over whether y is a real or a vector *)
      moreover have "... = (SUP y:UNIV. norm(?f x1 y - ?f x2 y)/norm(y))"
        by (metis (no_types, lifting) SUP_cong blinfun.diff_left norm_blinfun.rep_eq norm_minus_commute onorm_def)
      moreover have "... = (SUP y:UNIV. (setL2 (\<lambda>i. norm(f i x1 y - f i x2 y)) UNIV)/norm(y))"
        using  euclid by auto
      moreover have "... \<le> (SUP y:UNIV. (\<Sum>i\<in>UNIV. norm(f i x1 y - f i x2 y))/norm(y))"
        using L2' SUP_cong SUP_leq[of UNIV "(\<lambda>y. (setL2 (\<lambda>i. norm(f i x1 y - f i x2 y)) UNIV)/norm(y))" "(\<lambda>y. (\<Sum>i\<in>UNIV. norm(f i x1 y - f i x2 y))/norm(y))"]
        by auto
      moreover have "... = (SUP y:UNIV. (\<Sum>i\<in>UNIV. norm(f i x1 y - f i x2 y)/norm(y)))"
        by (simp add: setsum_divide_distrib)
      moreover have "... \<le> (\<Sum>i\<in>UNIV. (SUP y:UNIV.  norm(f i x1 y - f i x2 y)/norm(y)))"
        using SUP_sum_comm[of UNIV "(\<lambda> y i. norm(f i x1 y - f i x2 y)/norm(y))" UNIV, OF finite] 
        by auto
      moreover have "... = (\<Sum>i\<in>UNIV. norm(f i x1 - f i x2))"
        using each_norm by simp
      moreover have "... = (\<Sum>i\<in>UNIV. dist(f i x1) (f i x2))"
          by (simp add: dist_blinfun_def)
      moreover have "... < (\<Sum>i\<in>(UNIV::'a set). \<epsilon> / ?n)"
        using conts'''[OF ne dists] using SUM_leq[OF nonempty, of "(\<lambda>i.  dist (f i x1) (f i x2))" "(\<lambda>i.  \<epsilon> / ?n)"]
        by (simp add: dist_commute)
      moreover have "... = \<epsilon>"
        by(auto)
      ultimately show "dist (?f x2) (?f x1) < \<epsilon>"
        by linarith
    qed
  then show "\<exists>s>0. \<forall>x2. x2 \<noteq> x1 \<and> dist x2 x1 < s \<longrightarrow> dist (blinfun_vec (\<lambda>i. f i x2)) (blinfun_vec (\<lambda>i. f i x1)) < \<epsilon>"
    using \<delta> by auto
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

lemma has_derivative_proj':
  fixes i::"'a::finite"
  shows "\<forall>x. ((\<lambda> x. x $ i) has_derivative (\<lambda>x::(real^'a). x $ i)) (at x)"
  proof -
    have bounded_proj:"bounded_linear (\<lambda> x::(real^'a). x $ i)"
      by (simp add: bounded_linear_component_cart)
    show "?thesis"
      using bounded_proj unfolding has_derivative_def by auto
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

(* Example of using lemmas above to show a lemma that could be useful for dL: The constant ODE
 * 0 does not change the state.  *)
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

 
lemma MVT_ivl:
  fixes f::"'a::ordered_euclidean_space\<Rightarrow>'b::ordered_euclidean_space"
  assumes fderiv: "\<And>x. x \<in> D \<Longrightarrow> (f has_derivative J x) (at x within D)"
  assumes J_ivl: "\<And>x. x \<in> D \<Longrightarrow> J x u \<ge> J0"
  assumes line_in: "\<And>x. x \<in> {0..1} \<Longrightarrow> a + x *\<^sub>R u \<in> D"
  shows "f (a + u) - f a \<ge> J0"
proof -
  from MVT_corrected[OF fderiv line_in] obtain t where
    t: "t\<in>Basis \<rightarrow> {0<..<1}" and
    mvt: "f (a + u) - f a = (\<Sum>i\<in>Basis. (J (a + t i *\<^sub>R u) u \<bullet> i) *\<^sub>R i)"
    by auto
  note mvt
  also have "\<dots> \<ge> J0"
  proof -
    have J: "\<And>i. i \<in> Basis \<Longrightarrow> J0 \<le> J (a + t i *\<^sub>R u) u"
      using J_ivl t line_in by (auto simp: Pi_iff)
    show ?thesis
      using J
      unfolding atLeastAtMost_iff eucl_le[where 'a='b]
      by auto
  qed
  finally show ?thesis .
qed

lemma MVT_ivl':
  fixes f::"'a::ordered_euclidean_space\<Rightarrow>'b::ordered_euclidean_space"
  assumes fderiv: "(\<And>x. x \<in> D \<Longrightarrow> (f has_derivative J x) (at x within D))"
  assumes J_ivl: "\<And>x. x \<in> D \<Longrightarrow> J x (a - b) \<ge> J0"
  assumes line_in: "\<And>x. x \<in> {0..1} \<Longrightarrow> b + x *\<^sub>R (a - b) \<in> D"
  shows "f a \<ge> f b + J0"
proof -
  have "f (b + (a - b)) - f b \<ge> J0"
    apply (rule MVT_ivl[OF fderiv ])
    apply assumption
    apply (rule J_ivl) apply assumption
    using line_in
    apply (auto simp: diff_le_eq le_diff_eq ac_simps)
    done
  thus ?thesis
    by (auto simp: diff_le_eq le_diff_eq ac_simps)
qed
end