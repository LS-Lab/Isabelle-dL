theory Differential_Axioms2
imports
  Differential_Axioms
begin

text \<open>TODO: add to \<open>Differential_Axioms\<close>?\<close> 

\<comment> \<open>
< {c&q(||)} > (f(||)>=0&p(||)) ->
f(||)<=0 ->
<{c&q(||)}>
  (
    f(||)=0 &
    <c&q(||)}>(f(||)>=0&p(||))
  )
\<close>
definition IVTaxiom :: formula
  where "IVTaxiom =
  (let
    c = OVar Ix All;
    q = Pc Ix;
    f = state_fun Ix;
    p = Pc Iy
  in
  (\<langle> EvolveODE c q \<rangle> (p && f \<^bold>\<ge> \<^bold>0)) \<rightarrow> (\<^bold>0 \<^bold>\<ge> f \<rightarrow>
  (\<langle> EvolveODE c q \<rangle> (f \<^bold>= \<^bold>0 && \<langle>EvolveODE c q\<rangle> (f \<^bold>\<ge> \<^bold>0 && p)))))"

lemma FVT_state_fun: "FVT (state_fun f) = range Inl"
  by (auto simp: state_fun_def)

lemma fst_mk_v_vec_nth:
  "fst (mk_v I a b c) $ i =
    (if i \<in> ODE_vars I a then c $ i else fst b $ i)"
  by (auto simp: mk_v_concrete)

lemma continuous_on_sterm_compose[continuous_intros]:
  "continuous_on S (\<lambda>x. sterm_sem I f (g x))" if "continuous_on S g" "is_interp I" "dfree f"
  using continuous_on_compose2[OF sterm_continuous[OF that(2,3)] that(1)] by auto

lemma continuous_on_fst_mk_v[continuous_intros]:
  "continuous_on S (\<lambda>x. fst (mk_v I a b (f x)))" if "continuous_on S f"
  apply (auto simp: mk_v_concrete intro!: continuous_intros split: if_splits)
  subgoal for i
    by (cases "(Inl i::ident+ident) \<in> Inl ` ODE_vars I a \<or> Inl i \<in> Inr ` ODE_vars I a")
      (auto simp: that)
  done

lemma ident_expose_Ix: "ident_expose Ix = Inr (SSENT, ident_cons (CHR ''x'') ident_empty)"
  by transfer (simp add: max_str SSENT_def SSENTINEL_def)

lemma ilength_Ix[simp]: "ilength Ix = 2"
  by transfer simp

lemma dsafe_state_fun_Ix[simp]: "dsafe (state_fun Ix)"
  by (auto simp: state_fun_def ident_expose_Ix max_str)

lemma dfree_state_fun_Ix[simp]: "dfree (state_fun Ix)"
  by (auto simp: state_fun_def ident_expose_Ix max_str)

lemma ident_expose_Iy: "ident_expose Iy = Inr (SSENT, ident_cons (CHR ''y'') ident_empty)"
  by transfer (simp add: max_str SSENT_def SSENTINEL_def)

lemma ilength_Iy[simp]: "ilength Iy = 2"
  by transfer simp

lemma dsafe_Iy: "dsafe (state_fun Iy)"
  by (auto simp: state_fun_def ident_expose_Iy max_str)
  
lemma dfree_state_fun_Iy[simp]: "dfree (state_fun Iy)"
  by (auto simp: state_fun_def ident_expose_Iy max_str)

lemma ident_expose_Iz: "ident_expose Iz = Inr (SSENT, ident_cons (CHR ''z'') ident_empty)"
  by transfer (simp add: max_str SSENT_def SSENTINEL_def)

lemma ilength_Iz[simp]: "ilength Iz = 2"
  by transfer simp

lemma dsafe_Iz: "dsafe (state_fun Iz)"
  by (auto simp: state_fun_def ident_expose_Iz max_str)
  
lemma dfree_state_fun_Iz[simp]: "dfree (state_fun Iz)"
  by (auto simp: state_fun_def ident_expose_Iz max_str)


lemma IVT_valid:"valid IVTaxiom"
  unfolding IVTaxiom_def
proof (clarsimp simp add: Let_def valid_def)
  fix I::interp and sol' x_t x_t' sol t
  let ?ode = "(\<lambda>a b. \<chi> i. if i \<in> ODEBV I Ix None then ODEs I Ix None b $ i else 0)"
  assume H: "is_interp I"
    "mk_v I (OVar Ix None) (sol 0, sol') (sol t) \<in> Contexts I Iy UNIV"
    "0 \<le> dterm_sem I (state_fun Ix) (mk_v I (OVar Ix None) (sol 0, sol') (sol t))"
    "(x_t, x_t') = mk_v I (OVar Ix None) (sol 0, sol') (sol t)"
    "0 \<le> t"
    "(sol solves_ode ?ode) {0..t} {x. mk_v I (OVar Ix None) (sol 0, sol') x \<in> Contexts I Ix UNIV}"
    "dterm_sem I (state_fun Ix) (sol 0, sol') \<le> 0"
  note ode = \<open>(_ solves_ode _) _ _\<close>
  have sol_cont: "continuous_on {0..t} sol"
    by (rule solves_ode_continuous_on[OF ode])
  have sol_const: "sol s $ i = sol 0 $ i" if "0 \<le> s" "s \<le> t" "i \<notin> ODEBV I Ix None" for s i
    by (rule constant_when_zero[OF refl ode]) (use that in auto)
  define f where "f = dterm_sem I (state_fun Ix)"
  have f_sterm: "f x = sterm_sem I (state_fun Ix) (fst x)" for x
    by (auto simp: f_def state_fun_def)
  define phi where "phi t = mk_v I (OVar Ix None) (sol 0, sol') (sol t)" for t
  have fst_phi: "fst (phi s) = sol s" if "0 \<le> s" "s \<le> t" for s
    by (auto simp: phi_def mk_v_concrete vec_eq_iff intro!: sol_const[symmetric] that)
  have continuous_on_fst_phi: "continuous_on {0..t} (\<lambda>x. fst (phi x))"
    unfolding phi_def
    using sol_cont
    by (rule continuous_on_fst_mk_v)
  have "\<exists>x\<ge>0. x \<le> t \<and> (f \<circ> phi) x = 0"
  proof (rule IVT')
    have "dterm_sem I (state_fun Ix) (sol 0, sol') =
      dterm_sem I (state_fun Ix) (mk_v I (OVar Ix None) (sol 0, sol') (sol 0))"
      by (rule coincidence_dterm)
        (auto simp: FVT_state_fun Vagree_def fst_mk_v_vec_nth)
    then show "(f \<circ> phi) 0 \<le> 0"
      using H
      by (auto simp: phi_def f_def)
    show "0 \<le> (f \<circ> phi) t"
      using H
      by (auto simp: f_def phi_def)
    show "0 \<le> t" by fact
    show "continuous_on {0..t} (f \<circ> phi)"
      by (auto simp: f_sterm o_def  intro!: H continuous_on_sterm_compose continuous_on_fst_phi)
  qed
  then obtain s where s: "s\<ge>0" "s \<le> t" "(f \<circ> phi) s = 0"
    by metis
  have *: "(sol solves_ode ?ode) {0..s} {x. mk_v I (OVar Ix None) (sol 0, sol') x \<in> Contexts I Ix UNIV}"
    using \<open>(_ solves_ode _) _ _\<close>
    by (rule solves_ode_subset) (use \<open>s \<le> t\<close> in auto)
  have **: "f (phi s) = 0"
    using s by auto
  from H have ***: "0 \<le> dterm_sem I (state_fun Ix) (phi t)"
    by (auto simp: phi_def)
  have 4: "fst (phi s) = sol s"
    using H(2) sol_const[OF \<open>0 \<le> s\<close> \<open>s \<le> t\<close>]
    by (auto simp: phi_def vec_eq_iff fst_mk_v_vec_nth)
  have 5: "mk_v I (OVar Ix None) (sol s, snd (phi s)) (sol t) =
      mk_v I (OVar Ix None) (phi s) (fst (phi t))"
    using \<open>0 \<le> t\<close> \<open>0 \<le> s\<close> \<open>s \<le> t\<close>
    by (auto simp: mk_v_concrete vec_eq_iff fst_phi)
  have mk_v_shift: "mk_v I (OVar Ix None) (sol 0, sol') = mk_v I (OVar Ix None) (sol s, snd (phi s))"
    using \<open>0 \<le> s\<close> \<open>s \<le> t\<close>
    by (auto simp: phi_def mk_v_concrete vec_eq_iff fun_eq_iff intro!: sol_const[symmetric])
  have 6: "((\<lambda>t. fst (phi (s + t))) solves_ode ?ode) {0..t - s}
     {x. mk_v I (OVar Ix None) (sol s, snd (phi s)) x \<in> Contexts I Ix UNIV}"
  proof -
    from shift_autonomous_solution[OF H(6) refl, of s]
    have "((\<lambda>t. sol (s + t)) solves_ode ?ode) ((\<lambda>t. t - s) ` {0..t})
      {x. mk_v I (OVar Ix None) (sol 0, sol') x \<in> Contexts I Ix UNIV}"
      unfolding add.commute[of s] .
    also have "((\<lambda>t. t - s) ` {0..t}) = {-s .. t - s}" by auto
    finally have "((\<lambda>t. sol (s + t)) solves_ode ?ode) {- s..t - s}
      {x. mk_v I (OVar Ix None) (sol 0, sol') x \<in> Contexts I Ix UNIV}" .
    then have "((\<lambda>t. sol (s + t)) solves_ode ?ode) {0..t - s}
      {x. mk_v I (OVar Ix None) (sol s, snd (phi s)) x \<in> Contexts I Ix UNIV}"
      unfolding mk_v_shift
      by (rule solves_ode_on_subset) (use \<open>0 \<le> s\<close> in auto)
    then show ?thesis
      apply (subst solves_ode_cong[OF _ _ refl refl])
        apply (subst fst_phi)
      subgoal using \<open>0 \<le> s\<close> by auto
      subgoal by auto
        apply (rule refl)
       apply (rule refl)
      by auto
  qed
  have 7: "phi t \<in> Contexts I Iy UNIV"
    using H by (auto simp: phi_def)
  show "\<exists>a ba.
          (\<exists>sola.
              sol 0 = sola 0 \<and>
              (\<exists>t. (a, ba) = mk_v I (OVar Ix None) (sola 0, sol') (sola t) \<and>
                   0 \<le> t \<and>
                   (sola solves_ode ?ode) {0..t}
                    {x. mk_v I (OVar Ix None) (sola 0, sol') x \<in> Contexts I Ix UNIV})) \<and>
          dterm_sem I (state_fun Ix) (a, ba) = 0 \<and>
          (\<exists>aa b.
              (\<exists>sol. a = sol 0 \<and>
                     (\<exists>t. (aa, b) = mk_v I (OVar Ix None) (sol 0, ba) (sol t) \<and>
                          0 \<le> t \<and>
                          (sol solves_ode ?ode) {0..t}
                           {x. mk_v I (OVar Ix None) (sol 0, ba) x \<in> Contexts I Ix UNIV})) \<and>
              0 \<le> dterm_sem I (state_fun Ix) (aa, b) \<and> (aa, b) \<in> Contexts I Iy UNIV)"
    apply (rule exI[where x="fst (phi s)"])
    apply (rule exI[where x="snd (phi s)"])
    apply safe
      apply (rule exI[where x="sol"])
    apply safe
      apply (rule exI[where x="s"])
    subgoal using * \<open>0 \<le> s\<close> by (auto simp: phi_def)
    subgoal using ** by (auto simp: f_def)
    apply (rule exI[where x="fst (mk_v I (OVar Ix None) (sol s, snd (phi s)) (sol t))"])
    apply (rule exI[where x="snd (mk_v I (OVar Ix None) (sol s, snd (phi s)) (sol t))"])
    apply safe
      apply (rule exI[where x="\<lambda>t. fst (phi (s + t))"])
      apply safe
    subgoal by auto
      apply (rule exI[where x="t - s"])
    subgoal
      using \<open>0 \<le> s\<close>  \<open>s \<le> t\<close> 6
      by (auto simp: 5 fst_phi cong: solves_ode_cong)
    subgoal
      using ***
      by (auto simp flip: mk_v_shift phi_def)
    subgoal
      using 7
      by (auto simp flip: mk_v_shift phi_def)
    done
qed


end
