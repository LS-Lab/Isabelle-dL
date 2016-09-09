theory "Differential_Axioms" 
imports
  Complex_Main HOL
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
  "./Ids"
  "./Lib"
  "./Syntax"                                                                                                                  
  "./Denotational_Semantics"
  "./Frechet_Correctness"
  "./Coincidence"
begin context ids begin
section \<open>Differential Axioms\<close>
text \<open>Differential axioms fall into two categories:
Axioms for computing the derivatives of terms and axioms for proving properties of ODEs.
The derivative axioms are all corollaries of the frechet correctness theorem. The ODE
axioms are more involved, often requiring extensive use of the ODE libraries.\<close> 

subsection \<open>Differentiation Axioms\<close>
definition diff_const_axiom :: "('sf, 'sc, 'sz) formula"
  where "diff_const_axiom \<equiv> Equals (Differential ($f fid1 empty)) (Const 0)"

definition diff_var_axiom :: "('sf, 'sc, 'sz) formula"
  where "diff_var_axiom \<equiv> Equals (Differential (Var vid1)) (DiffVar vid1)"
  
definition state_fun ::"'sf \<Rightarrow> ('sf, 'sz) trm"
  where "state_fun f = ($f f (\<lambda>i. Var i))"
  
definition diff_plus_axiom :: "('sf, 'sc, 'sz) formula"
  where "diff_plus_axiom \<equiv> Equals (Differential (Plus (state_fun fid1) (state_fun fid2))) 
      (Plus (Differential (state_fun fid1)) (Differential (state_fun fid2)))"

definition diff_times_axiom :: "('sf, 'sc, 'sz) formula"
  where "diff_times_axiom \<equiv> Equals (Differential (Times (state_fun fid1) (state_fun fid2))) 
      (Plus (Times (Differential (state_fun fid1)) (state_fun fid2)) 
            (Times (state_fun fid1) (Differential (state_fun fid2))))"

(* [y=g(x)][y'=1](f(g(x))' = f(y)')*)
definition diff_chain_axiom::"('sf, 'sc, 'sz) formula"
  where "diff_chain_axiom \<equiv> [[Assign vid2 (f1 fid2 vid1)]]([[DiffAssign vid2 (Const 1)]] 
    (Equals (Differential ($f fid1 (singleton (f1 fid2 vid1)))) (Times (Differential (f1 fid1 vid2)) (Differential (f1 fid2 vid1)))))"

subsection \<open>ODE Axioms\<close>
definition DWaxiom :: "('sf, 'sc, 'sz) formula"
  where "DWaxiom = ([[EvolveODE (OVar vid1) (Predicational pid1)]](Predicational pid1))"

definition DWaxiom' :: "('sf, 'sc, 'sz) formula"
  where "DWaxiom' = ([[EvolveODE (OSing vid1 (Function fid1 (singleton (Var vid1)))) (Prop vid2 (singleton (Var vid1)))]](Prop vid2 (singleton (Var vid1))))"
  
definition DCaxiom :: "('sf, 'sc, 'sz) formula"
  where "DCaxiom = (
([[EvolveODE (OVar vid1) (Predicational pid1)]]Predicational pid3) \<rightarrow>
(([[EvolveODE (OVar vid1) (Predicational pid1)]](Predicational pid2)) 
  \<leftrightarrow>  
       ([[EvolveODE (OVar vid1) (And (Predicational pid1) (Predicational pid3))]]Predicational pid2)))"

definition DEaxiom :: "('sf, 'sc, 'sz) formula"
  where "DEaxiom = 
(([[EvolveODE (OSing vid1 (f1 fid1 vid1)) (p1 vid2 vid1)]] (P pid1))
\<leftrightarrow>
 ([[EvolveODE (OSing vid1 (f1 fid1 vid1)) (p1 vid2 vid1)]]
    [[DiffAssign vid1 (f1 fid1 vid1)]]P pid1))"
  
definition DSaxiom :: "('sf, 'sc, 'sz) formula"
  where "DSaxiom = 
(([[EvolveODE (OSing vid1 (f0 fid1)) (p1 vid2 vid1)]]p1 vid3 vid1)
\<leftrightarrow> 
(Forall vid2 
 (Implies (Geq (Var vid2) (Const 0)) 
 (Implies 
   (Forall vid3 
     (Implies (And (Geq (Var vid3) (Const 0)) (Geq (Var vid2) (Var vid3)))
        (Prop vid2 (singleton (Plus (Var vid1) (Times (f0 fid1) (Var vid3)))))))
   ([[Assign vid1 (Plus (Var vid1) (Times (f0 fid1) (Var vid2)))]]p1 vid3 vid1)))))"

(* 
g(x)\<ge> h(x) \<rightarrow> p(x) \<and> [x'=f(x), c & p(x)](g(x)' \<ge> h(x)') \<rightarrow> [x'=f(x), c]g(x) \<ge> h(x)
*)
definition DIGeqaxiom :: "('sf, 'sc, 'sz) formula"
  where "DIGeqaxiom = 
    (Implies (Geq (f1 fid2 vid1) (f1 fid3 vid1)) (Implies (And (p1 vid1 vid1) ([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (p1 vid1 vid1)]]
    (Geq (Differential (f1 fid2  vid1)) (Differential (f1 fid3 vid1)))
    )) ([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (p1 vid1 vid1)]](Geq (f1 fid2 vid1) (f1 fid3 vid1)))))"

definition DGaxiom :: "('sf, 'sc, 'sz) formula"
  where "DGaxiom = (([[EvolveODE (OVar vid1) (Predicational pid1)]]Predicational pid2) \<leftrightarrow> 
  (Exists vid2 
    ([[EvolveODE (OProd (OVar vid1) (OSing vid2 (Plus (Times (Function fid1 empty) (Var vid2)) (Function fid2 empty)))) (Predicational pid1)]]
       Predicational pid2)))"

subsection \<open>Proofs for Differentiation Axioms\<close>
lemma constant_deriv_inner:
 assumes interp:"\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x)"
 shows "FunctionFrechet I id1 (vec_lambda (\<lambda>i. sterm_sem I (empty i) (fst \<nu>))) (vec_lambda(\<lambda>i. frechet I (empty i) (fst \<nu>) (snd \<nu>)))= 0"
  proof -
    have empty_zero:"(vec_lambda(\<lambda>i. frechet I (empty i) (fst \<nu>) (snd \<nu>))) = 0"
    using local.empty_def Cart_lambda_cong frechet.simps(5) zero_vec_def
      by smt
    let ?x = "(vec_lambda (\<lambda>i. sterm_sem I (empty i) (fst \<nu>)))"
    from interp
    have has_deriv:"(Functions I id1 has_derivative FunctionFrechet I id1 ?x) (at ?x)"
    by auto
    then have f_linear:"linear (FunctionFrechet I id1 ?x)"
    using Deriv.has_derivative_linear by auto
    then
    show ?thesis using empty_zero f_linear Linear_Algebra.linear_0 by (auto)
  qed

lemma constant_deriv_zero:"is_interp I \<Longrightarrow> directional_derivative I ($f id1 empty) \<nu> = 0"
  apply(simp only: is_interp_def directional_derivative_def frechet.simps frechet_correctness)
  apply(rule constant_deriv_inner)
  apply(auto)
done

theorem diff_const_axiom_valid: "valid diff_const_axiom"
  apply(simp only: valid_def diff_const_axiom_def equals_sem)
  apply(rule allI | rule impI)+
  apply(simp only: dterm_sem.simps constant_deriv_zero sterm_sem.simps)
done

theorem diff_var_axiom_valid: "valid diff_var_axiom"
  apply(auto simp add: diff_var_axiom_def valid_def directional_derivative_def)
  by (metis basis_vector.simps inner_prod_eq)
  
theorem diff_plus_axiom_valid: "valid diff_plus_axiom"
   apply(auto simp add: diff_plus_axiom_def valid_def)
   subgoal for I a b
      using frechet_correctness[of I "(Plus (state_fun fid1) (state_fun fid2))" b] 
      unfolding state_fun_def apply (auto intro: dfree.intros)
      unfolding directional_derivative_def by auto
  done
  
theorem diff_times_axiom_valid: "valid diff_times_axiom"
   apply(auto simp add: diff_times_axiom_def valid_def)
   subgoal for I a b
      using frechet_correctness[of I "(Times (state_fun fid1) (state_fun fid2))" b] 
      unfolding state_fun_def apply (auto intro: dfree.intros)
      unfolding directional_derivative_def by auto
  done
  
theorem diff_chain_axiom_valid: "valid diff_chain_axiom"
   apply(auto simp add: diff_chain_axiom_def valid_def f1_def)
   subgoal for I a b
     proof -
       assume good_interp:"is_interp I"
       have free1:"dfree ($f fid1 (singleton ($f fid2 (singleton (trm.Var vid1)))))" by (auto intro: dfree.intros)
       have free2:"dfree ($f fid1 (singleton (Var vid2)))" by (auto intro: dfree.intros)
       have free3:"dfree ($f fid2 (singleton (Var vid1)))" by (auto intro: dfree.intros)
       note frech1 = frechet_correctness[OF good_interp free1]
       note frech2 = frechet_correctness[OF good_interp free2]
       note frech3 = frechet_correctness[OF good_interp free3]
    show "?thesis"
     using frech1 frech2 frech3 
      unfolding state_fun_def local.singleton.simps  apply (auto intro: dfree.intros)
      unfolding directional_derivative_def
      sorry
    qed
    done
  
subsection \<open>Proofs for ODE Axioms\<close>
 
lemma DW_valid:"valid DWaxiom"
  apply(unfold DWaxiom_def valid_def Let_def impl_sem )
  apply(safe)
  apply(auto simp only: fml_sem.simps prog_sem.simps box_sem)
  subgoal for I aa ba ab bb sol t using mk_v_agree[of I "(OVar vid1)" "(ab,bb)" "sol t"]
    Vagree_univ[of "aa" "ba" "sol t" "ODEs I vid1 (sol t)"] solves_ode_domainD
    by (fastforce)
  done

lemma DE_lemma:
fixes ab bb::"'sz simple_state"
and sol::"real \<Rightarrow> 'sz simple_state"
and I::"('sf, 'sc, 'sz) interp"
shows
"repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1 (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))
 = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)"
proof
  have set_eq:" {Inl vid1, Inr vid1} = {Inr vid1, Inl vid1}" by auto
  have agree:"Vagree (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) (mk_xode I (OSing vid1 (f1 fid1 vid1)) (sol t))
      {Inl vid1, Inr vid1}" 
    using mk_v_agree[of I "(OSing vid1 (f1 fid1 vid1))" "(ab, bb)" "(sol t)"] 
    unfolding semBV.simps using set_eq by auto
  have fact:"dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t))
          = snd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) $ vid1"
    using agree apply(simp only: Vagree_def dterm_sem.simps f1_def mk_xode.simps)
    proof -
      assume alls:"(\<forall>i. Inl i \<in> {Inl vid1, Inr vid1} \<longrightarrow>
          fst (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t)) $ i =
          fst (sol t, ODE_sem I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (sol t)) $ i) \<and>
        (\<forall>i. Inr i \<in> {Inl vid1, Inr vid1} \<longrightarrow>
          snd (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t)) $ i =
          snd (sol t, ODE_sem I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (sol t)) $ i)"
      hence atVid'':"snd (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t)) $ vid1 = sterm_sem I ($f fid1 (singleton (trm.Var vid1))) (sol t)" 
        by auto
      have argsEq:"(\<chi> i. dterm_sem I (singleton (trm.Var vid1) i)
            (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t)))
            = (\<chi> i.  sterm_sem I (singleton (trm.Var vid1) i) (sol t))"
        using agree by (simp add: vec_extensionality Vagree_def f1_def)
      thus "Functions I fid1 (\<chi> i. dterm_sem I (singleton (trm.Var vid1) i)
            (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t))) 
          = snd (mk_v I (OSing vid1 ($f fid1 (singleton (trm.Var vid1)))) (ab, bb) (sol t)) $ vid1"
        by (simp only: atVid'' ODE_sem.simps sterm_sem.simps dterm_sem.simps)
    qed
  have eqSnd:"(\<chi> y. if vid1 = y then snd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) $ vid1
        else snd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) $ y) = snd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t))"
    by (simp add: vec_extensionality)
  have truth:"repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
        (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))
      = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)"
    using fact by (auto simp only: eqSnd repd.simps fact prod.collapse split: if_split)
  thus "fst (repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
          (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))) =
    fst (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t))"

    "snd (repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
      (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))) =
    snd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) " 
    by auto
qed

lemma DE_valid:"valid DEaxiom"
  proof -
    have dsafe:"dsafe ($f fid1 (singleton (trm.Var vid1)))" unfolding singleton_def by(auto intro: dsafe.intros)
    have osafe:"osafe(OSing vid1 (f1 fid1 vid1))" unfolding f1_def empty_def singleton_def using dsafe osafe.intros dsafe.intros
      by (simp add: osafe_Sing dfree_Const) 
    have fsafe:"fsafe (p1 vid2 vid1)" unfolding p1_def singleton_def using hpsafe_fsafe.intros(10)
      using dsafe dsafe_Fun_simps image_iff
      by (simp add: dfree_Const)
    show "valid DEaxiom"
    apply(auto simp only: DEaxiom_def valid_def Let_def iff_sem impl_sem)
    apply(auto simp only: fml_sem.simps prog_sem.simps mem_Collect_eq box_sem) (* simp del: prog_sem.simps(8) simp add: ode_alt_sem[OF osafe fsafe] *)
  proof -
    fix I::"('sf,'sc,'sz) interp"
    and aa ba ab bb sol 
    and t::real
    and ac bc
     assume "is_interp I"
     assume allw:"\<forall>\<omega>. (\<exists>\<nu> sol t.
                  ((ab, bb), \<omega>) = (\<nu>, mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> (sol t)) \<and>
                  0 \<le> t \<and>
                  (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f1 fid1 vid1)))) {0..t}
                   {x. mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> x \<in> fml_sem I (p1 vid2 vid1)} \<and>
                  (sol 0) = (fst \<nu>) ) \<longrightarrow>
              \<omega> \<in> fml_sem I (P pid1)"
      assume t:"0 \<le> t"
      assume aaba:"(aa, ba) = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)"
      assume solve:" (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f1 fid1 vid1)))) {0..t}
          {x. mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) x \<in> fml_sem I (p1 vid2 vid1)}"
      assume sol0:" (sol 0) = (fst (ab, bb)) "
      assume rep:"   (ac, bc) =
         repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
          (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))"
      have aaba_sem:"(aa,ba) \<in> fml_sem I (P pid1)" using allw t aaba solve sol0 rep by blast
      have truth:"repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
          (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))
     = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)"
        using DE_lemma by auto
      show "
         repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1
          (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))
         \<in> fml_sem I (P pid1)" using aaba aaba_sem truth by (auto)
  next
    fix I::"('sf,'sc,'sz) interp" and  aa ba ab bb sol and t::real
       assume "is_interp I"
       assume all:"\<forall>\<omega>. (\<exists>\<nu> sol t.
                ((ab, bb), \<omega>) = (\<nu>, mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> (sol t)) \<and>
                0 \<le> t \<and>
                (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f1 fid1 vid1)))) {0..t}
                 {x. mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> x \<in> fml_sem I (p1 vid2 vid1)} \<and>
                 (sol 0) = (fst \<nu>) ) \<longrightarrow>
            (\<forall>\<omega>'. \<omega>' = repd \<omega> vid1 (dterm_sem I (f1 fid1 vid1) \<omega>) \<longrightarrow> \<omega>' \<in> fml_sem I (P pid1))"
       hence justW:"(\<exists>\<nu> sol t.
                ((ab, bb), (aa, ba)) = (\<nu>, mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> (sol t)) \<and>
                0 \<le> t \<and>
                (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f1 fid1 vid1)))) {0..t}
                 {x. mk_v I (OSing vid1 (f1 fid1 vid1)) \<nu> x \<in> fml_sem I (p1 vid2 vid1)} \<and>
                (sol 0) = (fst \<nu>)) \<longrightarrow>
            (\<forall>\<omega>'. \<omega>' = repd (aa, ba) vid1 (dterm_sem I (f1 fid1 vid1) (aa, ba)) \<longrightarrow> \<omega>' \<in> fml_sem I (P pid1))"
         by (rule allE)
       assume t:"0 \<le> t"
       assume aaba:"(aa, ba) = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)"
       assume sol:"(sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f1 fid1 vid1)))) {0..t}
        {x. mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) x \<in> fml_sem I (p1 vid2 vid1)}"
       assume sol0:" (sol 0) = (fst (ab, bb))"
       have "repd (aa, ba) vid1 (dterm_sem I (f1 fid1 vid1) (aa, ba)) \<in> fml_sem I (P pid1)"
         using justW t aaba sol sol0 by auto
       hence foo:"repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1 (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t))) \<in> fml_sem I (P pid1)"
         using aaba by auto
       hence "repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1 (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))
             = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)" using DE_lemma by auto
       thus "mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t) \<in> fml_sem I (P pid1)" using foo by auto
  qed
qed
  
lemma DC_valid:"valid DCaxiom" 
  proof (auto simp only: fml_sem.simps prog_sem.simps DCaxiom_def valid_def iff_sem impl_sem box_sem, auto)
    fix I::"('sf,'sc,'sz) interp" and aa ba bb sol t
       assume "is_interp I"
       and all3:"\<forall>a b. (\<exists>sola. sol 0 = sola 0 \<and>
                     (\<exists>t. (a, b) = mk_v I (OVar vid1) (sola 0, bb) (sola t) \<and>
                          0 \<le> t \<and> (sola solves_ode (\<lambda>a. ODEs I vid1)) {0..t} {x. mk_v I (OVar vid1) (sola 0, bb) x \<in> Contexts I pid1 UNIV})) \<longrightarrow>
             (a, b) \<in> Contexts I pid3 UNIV"
       and all2:"\<forall>a b. (\<exists>sola. sol 0 = sola 0 \<and>
                     (\<exists>t. (a, b) = mk_v I (OVar vid1) (sola 0, bb) (sola t) \<and>
                          0 \<le> t \<and> (sola solves_ode (\<lambda>a. ODEs I vid1)) {0..t} {x. mk_v I (OVar vid1) (sola 0, bb) x \<in> Contexts I pid1 UNIV})) \<longrightarrow>
             (a, b) \<in> Contexts I pid2 UNIV"
       and t:"0 \<le> t"
       and aaba:"(aa, ba) = mk_v I (OVar vid1) (sol 0, bb) (sol t)"
       and sol:"(sol solves_ode (\<lambda>a. ODEs I vid1)) {0..t}
         {x. mk_v I (OVar vid1) (sol 0, bb) x \<in> Contexts I pid1 UNIV \<and> mk_v I (OVar vid1) (sol 0, bb) x \<in> Contexts I pid3 UNIV}"
       from sol have
             sol1:"(sol solves_ode (\<lambda>a. ODEs I vid1)) {0..t} {x. mk_v I (OVar vid1) (sol 0, bb) x \<in> Contexts I pid1 UNIV}"
         by (metis (mono_tags, lifting) Collect_mono solves_ode_supset_range)
       from all2 have all2':"\<And>v. (\<exists>sola. sol 0 = sola 0 \<and>
                     (\<exists>t. v = mk_v I (OVar vid1) (sola 0, bb) (sola t) \<and>
                          0 \<le> t \<and> (sola solves_ode (\<lambda>a. ODEs I vid1)) {0..t} {x. mk_v I (OVar vid1) (sola 0, bb) x \<in> Contexts I pid1 UNIV})) \<Longrightarrow>
             v \<in> Contexts I pid2 UNIV" by auto
       show "mk_v I (OVar vid1) (sol 0, bb) (sol t) \<in> Contexts I pid2 UNIV" 
         apply(rule all2'[of "mk_v I (OVar vid1) (sol 0, bb) (sol t)"])
         apply(rule exI[where x=sol])
         apply(rule conjI)
         subgoal by (rule refl)
         subgoal using t sol1 by auto
       done
  next
    fix I::"('sf,'sc,'sz) interp" and  aa ba bb sol t
       assume "is_interp I"
       and all3:"\<forall>a b. (\<exists>sola. sol 0 = sola 0 \<and>
                     (\<exists>t. (a, b) = mk_v I (OVar vid1) (sola 0, bb) (sola t) \<and>
                          0 \<le> t \<and> (sola solves_ode (\<lambda>a. ODEs I vid1)) {0..t} {x. mk_v I (OVar vid1) (sola 0, bb) x \<in> Contexts I pid1 UNIV})) \<longrightarrow>
             (a, b) \<in> Contexts I pid3 UNIV"
       and all2:"\<forall>a b. (\<exists>sola. sol 0 = sola 0 \<and>
                     (\<exists>t. (a, b) = mk_v I (OVar vid1) (sola 0, bb) (sola t) \<and>
                          0 \<le> t \<and>
                          (sola solves_ode (\<lambda>a. ODEs I vid1)) {0..t}
                           {x. mk_v I (OVar vid1) (sola 0, bb) x \<in> Contexts I pid1 UNIV \<and>
                               mk_v I (OVar vid1) (sola 0, bb) x \<in> Contexts I pid3 UNIV})) \<longrightarrow>
             (a, b) \<in> Contexts I pid2 UNIV"
       and t:"0 \<le> t"
       and aaba:"(aa, ba) = mk_v I (OVar vid1) (sol 0, bb) (sol t)"
       and sol:"(sol solves_ode (\<lambda>a. ODEs I vid1)) {0..t} {x. mk_v I (OVar vid1) (sol 0, bb) x \<in> Contexts I pid1 UNIV}"
       from all2 
       have all2':"\<And>v. (\<exists>sola. sol 0 = sola 0 \<and>
                     (\<exists>t. v = mk_v I (OVar vid1) (sola 0, bb) (sola t) \<and>
                          0 \<le> t \<and>
                          (sola solves_ode (\<lambda>a. ODEs I vid1)) {0..t}
                           {x. mk_v I (OVar vid1) (sola 0, bb) x \<in> Contexts I pid1 UNIV \<and>
                               mk_v I (OVar vid1) (sola 0, bb) x \<in> Contexts I pid3 UNIV})) \<Longrightarrow>
             v \<in> Contexts I pid2 UNIV"
         by auto
       from all3
       have all3':"\<And>v. (\<exists>sola. sol 0 = sola 0 \<and>
                     (\<exists>t. v = mk_v I (OVar vid1) (sola 0, bb) (sola t) \<and>
                          0 \<le> t \<and> (sola solves_ode (\<lambda>a. ODEs I vid1)) {0..t} {x. mk_v I (OVar vid1) (sola 0, bb) x \<in> Contexts I pid1 UNIV})) \<Longrightarrow>
             v \<in> Contexts I pid3 UNIV"
         by auto
       have inp1:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> mk_v I (OVar vid1) (sol 0, bb) (sol s) \<in> Contexts I pid1 UNIV"
         using sol solves_odeD atLeastAtMost_iff by blast
       have inp3:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> mk_v I (OVar vid1) (sol 0, bb) (sol s) \<in> Contexts I pid3 UNIV"
         apply(rule all3')
         subgoal for s 
           apply(rule exI [where x=sol])
           apply(rule conjI)
           subgoal by (rule refl)
           apply(rule exI [where x=s])
           apply(rule conjI)
           subgoal by (rule refl)
           apply(rule conjI)
           subgoal by assumption
           subgoal using sol by (meson atLeastatMost_subset_iff order_refl solves_ode_subset)
           done
         done
       have inp13:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> mk_v I (OVar vid1) (sol 0, bb) (sol s) \<in> Contexts I pid1 UNIV \<and> mk_v I (OVar vid1) (sol 0, bb) (sol s) \<in> Contexts I pid3 UNIV"
         using inp1 inp3 by auto
       have sol13:"(sol solves_ode (\<lambda>a. ODEs I vid1)) {0..t}
         {x. mk_v I (OVar vid1) (sol 0, bb) x \<in> Contexts I pid1 UNIV \<and> mk_v I (OVar vid1) (sol 0, bb) x \<in> Contexts I pid3 UNIV}"
         apply(rule solves_odeI)
         subgoal using sol by (rule solves_odeD)
         subgoal for s using inp13[of s] by auto
         done
       show "mk_v I (OVar vid1) (sol 0, bb) (sol t) \<in> Contexts I pid2 UNIV"
         using t sol13 all2'[of "mk_v I (OVar vid1) (sol 0, bb) (sol t)"] by auto
         
  qed

lemma DS_valid:"valid DSaxiom"
  proof -
    have dsafe:"dsafe($f fid1 (\<lambda>i. Const 0))"
      using dsafe_Const by auto
    have osafe:"osafe(OSing vid1 (f0 fid1))"
      unfolding f0_def empty_def
      using dsafe osafe.intros
      by (simp add: osafe_Sing dfree_Const)
    have fsafe:"fsafe(p1 vid2 vid1)"
      unfolding p1_def
      apply(rule fsafe_Prop)
      using singleton.simps dsafe_Const by (auto intro: dfree.intros)
    show "valid DSaxiom"
  apply(auto simp only: DSaxiom_def valid_def Let_def iff_sem impl_sem box_sem)
  apply(auto simp only: fml_sem.simps prog_sem.simps mem_Collect_eq  iff_sem impl_sem box_sem forall_sem
       (*simp del: prog_sem.simps(8) simp add: ode_alt_sem[OF osafe fsafe]*))
  proof -
    fix I::"('sf,'sc,'sz) interp" 
    and a b r aa ba
   assume good_interp:"is_interp I"
   assume allW:"\<forall>\<omega>. (\<exists>\<nu> sol t.
              ((a, b), \<omega>) = (\<nu>, mk_v I (OSing vid1 (f0 fid1)) \<nu> (sol t)) \<and>
              0 \<le> t \<and>
              (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..t}
               {x. mk_v I (OSing vid1 (f0 fid1)) \<nu> x \<in> fml_sem I (p1 vid2 vid1)} \<and>
               (sol 0) = (fst \<nu>)) \<longrightarrow>
          \<omega> \<in> fml_sem I (p1 vid3 vid1)"
   assume "dterm_sem I (Const 0) (repv (a, b) vid2 r) \<le> dterm_sem I (trm.Var vid2) (repv (a, b) vid2 r)"
     hence leq:"0 \<le> r" by (auto)
   assume "\<forall>ra. repv (repv (a, b) vid2 r) vid3 ra
          \<in> {v. dterm_sem I (Const 0) v \<le> dterm_sem I (trm.Var vid3) v} \<inter>
             {v. dterm_sem I (trm.Var vid3) v \<le> dterm_sem I (trm.Var vid2) v} \<longrightarrow>
          Predicates I vid2
           (\<chi> i. dterm_sem I (singleton (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3))) i)
                  (repv (repv (a, b) vid2 r) vid3 ra))"
   hence constraint:"\<forall>ra. (0 \<le> ra \<and> ra \<le> r) \<longrightarrow> 
          (repv (repv (a, b) vid2 r) vid3 ra) 
        \<in> fml_sem I (Prop vid2 (singleton (Plus (Var vid1) (Times (f0 fid1) (Var vid3)))))"
       using leq by auto
  assume aaba:" (aa, ba) =
     repv (repv (a, b) vid2 r) vid1
      (dterm_sem I (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid2))) (repv (a, b) vid2 r))"
  let ?abba = "repv (repd (a, b) vid1 (Functions I fid1 (\<chi> i. 0))) vid1
      (dterm_sem I (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid2))) (repv (a, b) vid2 r))"
  from allW have thisW:"(\<exists>\<nu> sol t.
             ((a, b), ?abba) = (\<nu>, mk_v I (OSing vid1 (f0 fid1)) \<nu> (sol t)) \<and>
             0 \<le> t \<and>
             (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..t}
              {x. mk_v I (OSing vid1 (f0 fid1)) \<nu> x \<in> fml_sem I (p1 vid2 vid1)} \<and>
              (sol 0) = (fst \<nu>)) \<longrightarrow>
         ?abba \<in> fml_sem I (p1 vid3 vid1)" by blast
  let ?c = "Functions I fid1 (\<chi> _. 0)"
  let ?sol = "(\<lambda>t. \<chi> i. if i = vid1 then (a $ i) + ?c * t else (a $ i))"
  have 
  agrees:"Vagree (mk_v I (OSing vid1 (f0 fid1)) (a, b) (?sol r)) (a, b) (- semBV I (OSing vid1 (f0 fid1))) 
  \<and> Vagree (mk_v I (OSing vid1 (f0 fid1)) (a, b) (?sol r))
   (mk_xode I (OSing vid1 (f0 fid1)) (?sol r)) (semBV I (OSing vid1 (f0 fid1)))" 
    using mk_v_agree[of "I" "(OSing vid1 (f0 fid1))" "(a,b)" "(?sol r)"] by auto
  
  have prereq1a:"fst ?abba
  = fst (mk_v I (OSing vid1 (f0 fid1)) (a,b) (?sol r))"
    using  agrees aaba 
    apply (auto simp add: aaba Vagree_def)
    apply (rule vec_extensionality)
    subgoal for i
      apply (cases "i = vid1")
      using vne12 agrees Vagree_def  apply (auto simp add: aaba f0_def empty_def)
      done
    apply (rule vec_extensionality)
      subgoal for i
        apply (cases "i = vid1")
        apply(auto  simp add: f0_def empty_def)
      done
    done
  have prereq1b:"snd (?abba) = snd (mk_v I (OSing vid1 (f0 fid1)) (a,b) (?sol r))"
    using  agrees aaba 
    apply (auto simp add: aaba Vagree_def)
    apply (rule vec_extensionality)
    subgoal for i
      apply (cases "i = vid1")
      using vne12 agrees Vagree_def  apply (auto simp add: aaba f0_def empty_def )
      done
    done
  
  have "?abba = mk_v I (OSing vid1 (f0 fid1)) (a,b) (?sol r)"
    using prod_eq_iff prereq1a prereq1b by blast
  hence req1:"((a, b), ?abba) = ((a, b), mk_v I (OSing vid1 (f0 fid1)) (a,b) (?sol r))" by auto
  have "sterm_sem I ($f fid1 (\<lambda>i. Const 0)) b = Functions I fid1 (\<chi> i. 0)" by auto
  hence vec_simp:"(\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I ($f fid1 (\<lambda>i. Const 0)) b else 0) 
      = (\<lambda>a b. \<chi> i. if i = vid1 then Functions I fid1 (\<chi> i. 0) else 0)"
    by (auto simp add: vec_eq_iff cong: if_cong)
    (* TODO: have a solution that exists everywhere, want to restrict the domain. Fabian says this
       should be true but has not been formalized just yet. *)
  (*interpret ll:ll_on_open_it "{0 .. r}" "(\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))" "{x. mk_v I (OSing vid1 (f0 fid1)) (a,b) x \<in> fml_sem I (p1 vid2 vid1)}"*)
  have sub: "{0..r} \<subseteq> UNIV" by auto
  have sub2:"{x. mk_v I (OSing vid1 (f0 fid1)) (a,b) x \<in> fml_sem I (p1 vid2 vid1)} \<subseteq> UNIV" by auto
  have req3:"(?sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..r}
            {x. mk_v I (OSing vid1 (f0 fid1)) (a,b) x \<in> fml_sem I (p1 vid2 vid1)}" 
    apply(auto simp add: f0_def empty_def vec_simp) 
    apply(rule solves_odeI)
    apply(auto simp only: has_vderiv_on_def has_vector_derivative_def box_sem)
    apply (rule has_derivative_vec[THEN has_derivative_eq_rhs])
    defer
    apply (rule ext)
    apply (subst scaleR_vec_def)
    apply (rule refl)
    apply (auto intro!: derivative_eq_intros)
    (* Domain constraint satisfied*)
    using constraint apply (auto)
    subgoal for t
      apply(erule allE[where x="t"])
      apply(auto simp add: p1_def)
    proof -
      have eq:"(\<chi> i. dterm_sem I (if i = vid1 then Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3)) else Const 0)
            (\<chi> y. if vid3 = y then t else fst (\<chi> y. if vid2 = y then r else fst (a, b) $ y, b) $ y, b)) =
            (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
              (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. Const 0))) (a, b)
                (\<chi> i. if i = vid1 then a $ i + Functions I fid1 (\<chi> _. 0) * t else a $ i)))"
        using vne12 vne13 mk_v_agree[of "I" "(OSing vid1 ($f fid1 (\<lambda>i. Const 0)))" "(a, b)" "(\<chi> i. if i = vid1 then a $ i + Functions I fid1 (\<chi> _. 0) * t else a $ i)"]
        by (auto simp add: vec_eq_iff f0_def empty_def Vagree_def)
      show "0 \<le> t \<Longrightarrow>
    t \<le> r \<Longrightarrow>
    Predicates I vid2
     (\<chi> i. dterm_sem I (if i = vid1 then Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3)) else Const 0)
            (\<chi> y. if vid3 = y then t else fst (\<chi> y. if vid2 = y then r else fst (a, b) $ y, b) $ y, b)) \<Longrightarrow>
    Predicates I vid2
     (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
            (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. Const 0))) (a, b)
              (\<chi> i. if i = vid1 then a $ i + Functions I fid1 (\<chi> _. 0) * t else a $ i)))" using eq by auto
    qed
    done
  have req4':"?sol 0 = fst (a,b)" by (auto simp: vec_eq_iff)
  then have req4: " (?sol 0) = (fst (a,b))"
    using VSagree_refl[of a] req4' unfolding VSagree_def by auto
  have inPred:"?abba \<in> fml_sem I (p1 vid3 vid1)"  
    using req1 leq req3 req4 thisW by fastforce
  have sem_eq:"?abba \<in> fml_sem I (p1 vid3 vid1) \<longleftrightarrow> (aa,ba) \<in> fml_sem I (p1 vid3 vid1)"
    apply(rule coincidence_formula)
    apply (auto simp add: aaba Vagree_def p1_def f0_def empty_def)
    subgoal by (auto intro: dfree.intros)
    subgoal using Iagree_refl by auto
    done
  from inPred sem_eq have  inPred':"(aa,ba) \<in> fml_sem I (p1 vid3 vid1)"
    by auto
  (* thus by lemma 6 consequence for formulas *)
  show "repv (repv (a, b) vid2 r) vid1
       (dterm_sem I (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid2))) (repv (a, b) vid2 r))
       \<in> fml_sem I (p1 vid3 vid1)" 
    using aaba inPred' by (auto)
next
  fix I::"('sf,'sc,'sz) interp"
  and aa ba ab bb sol 
  and t:: real
  assume good_interp:"is_interp I"
  assume all:"
       \<forall>r. dterm_sem I (Const 0) (repv (ab, bb) vid2 r) \<le> dterm_sem I (trm.Var vid2) (repv (ab, bb) vid2 r) \<longrightarrow>
           (\<forall>ra. repv (repv (ab, bb) vid2 r) vid3 ra
                 \<in> {v. dterm_sem I (Const 0) v \<le> dterm_sem I (trm.Var vid3) v} \<inter>
                    {v. dterm_sem I (trm.Var vid3) v \<le> dterm_sem I (trm.Var vid2) v} \<longrightarrow>
                 Predicates I vid2
                  (\<chi> i. dterm_sem I (singleton (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3))) i)
                         (repv (repv (ab, bb) vid2 r) vid3 ra))) \<longrightarrow>
                         
           (\<forall>\<omega>. \<omega> = repv (repv (ab, bb) vid2 r) vid1
                      (dterm_sem I (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid2))) (repv (ab, bb) vid2 r)) \<longrightarrow>
                 \<omega> \<in> fml_sem I (p1 vid3 vid1))"
  assume t:"0 \<le> t"
  assume aaba:"(aa, ba) = mk_v I (OSing vid1 (f0 fid1)) (ab, bb) (sol t)"
  assume sol:"(sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..t}
        {x. mk_v I (OSing vid1 (f0 fid1)) (ab, bb) x \<in> fml_sem I (p1 vid2 vid1)}"
  hence constraint:"\<And>s. s \<in> {0 .. t} \<Longrightarrow> sol s \<in> {x. mk_v I (OSing vid1 (f0 fid1)) (ab, bb) x \<in> fml_sem I (p1 vid2 vid1)}"
    using solves_ode_domainD by fastforce
  (* sol 0 = fst (ab, bb)*)
  assume sol0:"  (sol 0) = (fst (ab, bb)) "
  have impl:"dterm_sem I (Const 0) (repv (ab, bb) vid2 t) \<le> dterm_sem I (trm.Var vid2) (repv (ab, bb) vid2 t) \<longrightarrow>
           (\<forall>ra. repv (repv (ab, bb) vid2 t) vid3 ra
                 \<in> {v. dterm_sem I (Const 0) v \<le> dterm_sem I (trm.Var vid3) v} \<inter>
                    {v. dterm_sem I (trm.Var vid3) v \<le> dterm_sem I (trm.Var vid2) v} \<longrightarrow>
                 Predicates I vid2
                  (\<chi> i. dterm_sem I (singleton (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3))) i)
                         (repv (repv (ab, bb) vid2 t) vid3 ra))) \<longrightarrow>
           (\<forall>\<omega>. \<omega> = repv (repv (ab, bb) vid2 t) vid1
                      (dterm_sem I (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid2))) (repv (ab, bb) vid2 t)) \<longrightarrow>
                 \<omega> \<in> fml_sem I (p1 vid3 vid1))" using all by auto
  interpret ll:ll_on_open_it UNIV "(\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))" "UNIV" 0
    apply(standard)
    apply(auto)
    unfolding local_lipschitz_def f0_def empty_def sterm_sem.simps apply(safe)
    using gt_ex lipschitz_constI apply blast
    by (simp add: continuous_on_const)
  have eq_UNIV:"ll.existence_ivl 0 (sol 0) = UNIV"
    apply(rule ll.existence_ivl_eq_domain)
    apply(auto)
    subgoal for tm tM t
      apply(unfold f0_def empty_def sterm_sem.simps)
      by(metis add.right_neutral mult_zero_left order_refl)
    done
  (* Combine with flow_usolves_ode and equals_flowI to get uniqueness of solution *)
  let ?f = "(\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))"
  have sol_UNIV: "\<And>t x. (ll.flow 0 x usolves_ode ?f from 0) (ll.existence_ivl 0 x) UNIV"
    using ll.flow_usolves_ode by auto    
  from sol have sol':
    "(sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..t} UNIV"
    apply (rule solves_ode_supset_range)
    by auto
  from sol' have sol'':"\<And>s. s \<ge> 0 \<Longrightarrow> s \<le> t \<Longrightarrow> (sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..s} UNIV"
    by (simp add: solves_ode_subset)
  have sol0_eq:"sol 0 = ll.flow  0 (sol 0) 0"
    using ll.general.flow_initial_time_if by auto
  have isFlow:"\<And>s. s \<ge> 0 \<Longrightarrow> s \<le> t \<Longrightarrow> sol s = ll.flow 0 (sol 0) s"
    apply(rule ll.equals_flowI)
    apply(auto)
    subgoal using eq_UNIV by auto
    subgoal using sol'' closed_segment_eq_real_ivl t by (auto simp add: solves_ode_singleton)
    subgoal using eq_UNIV sol sol0_eq by auto
    done
  let ?c = "Functions I fid1 (\<chi> _. 0)"
  let ?sol = "(\<lambda>t. \<chi> i. if i = vid1 then (ab $ i) + ?c * t else (ab $ i))"
  have vec_simp:"(\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I ($f fid1 (\<lambda>i. Const 0)) b else 0) 
      = (\<lambda>a b. \<chi> i. if i = vid1 then Functions I fid1 (\<chi> i. 0) else 0)"
    by (auto simp add: vec_eq_iff cong: if_cong)
  have exp_sol:"(?sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..t}
    UNIV"
    apply(auto simp add: f0_def empty_def vec_simp) 
    apply(rule solves_odeI)
    apply(auto simp only: has_vderiv_on_def has_vector_derivative_def box_sem)
    apply (rule has_derivative_vec[THEN has_derivative_eq_rhs])
    defer
    apply (rule ext)
    apply (subst scaleR_vec_def)
    apply (rule refl)
    apply (auto intro!: derivative_eq_intros)
    done
  from exp_sol have exp_sol':"\<And>s. s \<ge> 0 \<Longrightarrow> s \<le> t \<Longrightarrow> (?sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..s} UNIV"
    by (simp add: solves_ode_subset)
  have exp_sol0_eq:"?sol 0 = ll.flow  0 (?sol 0) 0"
    using ll.general.flow_initial_time_if by auto
  have more_eq:"(\<chi> i. if i = vid1 then ab $ i + Functions I fid1 (\<chi> _. 0) * 0 else ab $ i) = sol 0"
    using sol0 
    apply auto 
    apply(rule vec_extensionality)
    by(auto)
  have exp_isFlow:"\<And>s. s \<ge> 0 \<Longrightarrow> s \<le> t \<Longrightarrow> ?sol s = ll.flow 0 (sol 0) s"
    apply(rule ll.equals_flowI)
    apply(auto)
    subgoal using eq_UNIV by auto
    defer
    subgoal for s 
      using eq_UNIV apply auto
      subgoal using exp_sol exp_sol0_eq more_eq 
        apply(auto)
        done
    done
    using exp_sol' closed_segment_eq_real_ivl t apply(auto)
    by (simp add: solves_ode_singleton)
  have sol_eq_exp:"\<And>s. s \<ge> 0 \<Longrightarrow> s \<le> t \<Longrightarrow> ?sol s = sol s"
    unfolding exp_isFlow isFlow by auto
  then have sol_eq_exp_t:"?sol t = sol t"
    using t by auto
  then have sol_eq_exp_t':"sol t $ vid1 = ?sol t $ vid1" by auto
  then have useful:"?sol t $ vid1 = ab $ vid1 + Functions I fid1 (\<chi> i. 0) * t"
    by auto
  from sol_eq_exp_t' useful have useful':"sol t $ vid1 = ab $ vid1 + Functions I fid1 (\<chi> i. 0) * t"
    by auto
  have sol_int:"((ll.flow 0 (sol 0)) usolves_ode ?f from 0) {0..t} {x. mk_v I (OSing vid1 (f0 fid1)) (ab, bb) x \<in> fml_sem I (p1 vid2 vid1)}"
    apply (rule usolves_ode_subset_range[of "(ll.flow 0 (sol 0))" "?f" "0" "{0..t}" "UNIV" "{x. mk_v I (OSing vid1 (f0 fid1)) (ab, bb) x \<in> fml_sem I (p1 vid2 vid1)}"]) 
    subgoal using eq_UNIV sol_UNIV[of "(sol 0)"] apply (auto)
      apply (rule usolves_ode_subset)
      using t by(auto)
    apply(auto)
    using sol apply(auto  dest!: solves_ode_domainD)
    subgoal for xa using isFlow[of xa] by(auto)
    done
  have thing:"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> fst (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. Const 0))) (ab, bb) (?sol s)) $ vid1 = ab $ vid1 + Functions I fid1 (\<chi> i. 0) * s"
    subgoal for s
      using mk_v_agree[of I "(OSing vid1 ($f fid1 (\<lambda>i. Const 0)))" "(ab, bb)" "(?sol s)"] apply auto
      unfolding Vagree_def by auto
    done
  have thing':"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow>  fst (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. Const 0))) (ab, bb) (sol s)) $ vid1 = ab $ vid1 + Functions I fid1 (\<chi> i. 0) * s"
    subgoal for s using thing[of s] sol_eq_exp[of s] by auto done
  have another_eq:"\<And>i s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                (mk_v I (OSing vid1 (f0 fid1)) (ab, bb) (sol s))

        =  dterm_sem I (if i = vid1 then Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3)) else Const 0)
                (\<chi> y. if vid3 = y then s else fst (\<chi> y. if vid2 = y then s else fst (ab, bb) $ y, bb) $ y, bb)"
    using mk_v_agree[of "I" "(OSing vid1 (f0 fid1))" "(ab, bb)" "(sol s)"]  vne12 vne23 vne13
    apply(auto simp add: f0_def p1_def empty_def)
    unfolding Vagree_def apply(simp add: f0_def empty_def)
    subgoal for s using thing' by auto
    done
  have allRa':"(\<forall>ra. repv (repv (ab, bb) vid2 t) vid3 ra
               \<in> {v. dterm_sem I (Const 0) v \<le> dterm_sem I (trm.Var vid3) v} \<inter>
                  {v. dterm_sem I (trm.Var vid3) v \<le> dterm_sem I (trm.Var vid2) v} \<longrightarrow>
               Predicates I vid2
                (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                (mk_v I (OSing vid1 (f0 fid1)) (ab, bb) (sol ra))))"
    apply(rule allI)
    subgoal for ra
      using mk_v_agree[of "I" "(OSing vid1 (f0 fid1))" "(ab, bb)" "(sol ra)"]
         vne23 constraint[of ra] apply(auto simp add: Vagree_def p1_def)
    done
  done
  have anotherFact:"\<And>ra. 0 \<le> ra \<Longrightarrow> ra \<le> t \<Longrightarrow> (\<chi> i. if i = vid1 then ab $ i + Functions I fid1 (\<chi> _. 0) * ra else ab $ i) $ vid1 =
     ab $ vid1 + dterm_sem I (f0 fid1) (\<chi> y. if vid3 = y then ra else fst (\<chi> y. if vid2 = y then t else fst (ab, bb) $ y, bb) $ y, bb) * ra "
    subgoal for ra
      apply simp
      apply(rule disjI2)
      by (auto simp add: f0_def empty_def)
    done
  have thing':"\<And>ra i. 0 \<le> ra \<Longrightarrow> ra \<le> t \<Longrightarrow> dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. Const 0))) (ab, bb) (sol ra))
      =  dterm_sem I (if i = vid1 then Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3)) else Const 0)
            (\<chi> y. if vid3 = y then ra else fst (\<chi> y. if vid2 = y then t else fst (ab, bb) $ y, bb) $ y, bb) "
    subgoal for ra i
      using vne12 vne13 mk_v_agree[of I "OSing vid1 ($f fid1 (\<lambda>i. Const 0))" "(ab,bb)" "(sol ra)"] 
      apply (auto)
      unfolding Vagree_def apply(safe)
      apply(erule allE[where x="vid1"])+
      using sol_eq_exp[of ra] anotherFact[of ra] by auto
    done
  have allRa:"(\<forall>ra. repv (repv (ab, bb) vid2 t) vid3 ra
               \<in> {v. dterm_sem I (Const 0) v \<le> dterm_sem I (trm.Var vid3) v} \<inter>
                  {v. dterm_sem I (trm.Var vid3) v \<le> dterm_sem I (trm.Var vid2) v} \<longrightarrow>
               Predicates I vid2
                (\<chi> i. dterm_sem I (singleton (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3))) i)
                       (repv (repv (ab, bb) vid2 t) vid3 ra)))"
    apply(rule allI)
    subgoal for ra
      using mk_v_agree[of "I" "(OSing vid1 (f0 fid1))" "(ab, bb)" "(sol ra)"]
         vne23 constraint[of ra] apply(auto simp add: Vagree_def p1_def)
      using sol_eq_exp[of ra]  apply (auto simp add: f0_def empty_def Vagree_def vec_eq_iff)
      using thing' by auto
    done
  have fml3:"\<And>ra. 0 \<le> ra \<Longrightarrow> ra \<le> t \<Longrightarrow>
           (\<forall>\<omega>. \<omega> = repv (repv (ab, bb) vid2 t) vid1
                      (dterm_sem I (Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid2))) (repv (ab, bb) vid2 t)) \<longrightarrow>
                 \<omega> \<in> fml_sem I (p1 vid3 vid1))"
    using impl allRa by auto
       
  have someEq:"(\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
            (\<chi> y. if vid1 = y then (if vid2 = vid1 then t else fst (ab, bb) $ vid1) + Functions I fid1 (\<chi> i. 0) * t
                  else fst (\<chi> y. if vid2 = y then t else fst (ab, bb) $ y, bb) $ y,
             bb)) 
             = (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. Const 0))) (ab, bb) (sol t)))"
    apply(rule vec_extensionality)
    using vne12 sol_eq_exp t thing by auto
  
  show "mk_v I (OSing vid1 (f0 fid1)) (ab, bb) (sol t) \<in> fml_sem I (p1 vid3 vid1)"
    using mk_v_agree[of I "OSing vid1 (f0 fid1)" "(ab, bb)" "sol t"] fml3[of t]
    unfolding f0_def p1_def empty_def Vagree_def 
    using someEq by(auto simp add:  sol_eq_exp_t' t vec_extensionality  vne12)
qed qed


(* have cont':"\<And>s'. s' \<in> {0..s} \<Longrightarrow> isCont f s'"
        subgoal for s  
          using has_derivative_continuous[OF f'[of s]]
          unfolding isCont_def using sub[of s] sorry
        done
      then have cont:"\<forall>x. 0 \<le> x \<and> x \<le> s \<longrightarrow> isCont f x" by auto
      have "\<And>s'. 0 < s' \<and> s' < s \<Longrightarrow> f differentiable at s'  within {0..t}"
        subgoal for s' using f'[of s'] 
          using Derivative.differentiableI sub[of s'] by auto
        done
      then have diff:"\<forall>x. 0 < x \<and> x < s \<longrightarrow> f differentiable at x"
        sorry
        *)

lemma MVT0_within:
fixes f ::"real \<Rightarrow> real"
  and f'::"real \<Rightarrow> real \<Rightarrow> real"
  and s t :: real
assumes f':"\<And>x. x \<in> {0..t} \<Longrightarrow> (f has_derivative (f' x)) (at x  within {0..t})"
assumes geq':"\<And>x. x \<in> {0..t} \<Longrightarrow> f' x s \<ge> 0"
assumes int_s:"s > 0 \<and> s \<le> t"
assumes t: "0 < t"
shows "f s \<ge> f 0"
proof -
  have "f 0 + 0 \<le> f s"   
    apply (rule Lib.MVT_ivl'[OF f', of 0 s 0])
    subgoal for x by assumption
    subgoal for x using geq' by auto 
    using t int_s t apply auto
    subgoal for x
      by (metis int_s mult.commute mult.right_neutral order.trans real_mult_le_cancel_iff2)
    done
  then show "?thesis" by auto 
qed

(*
lemma MVT_ivl_restricted:
  fixes f::"'a::ordered_euclidean_space\<Rightarrow>'b::ordered_euclidean_space"
  assumes fderiv: "\<And>x. x \<in> D \<Longrightarrow> (f has_derivative J x) (at x within D)"
  assumes J_ivl: "\<And>x. x \<in> D \<Longrightarrow> J x x \<ge> J0"
  assumes line_in: "\<And>x. x \<in> {0..1} \<Longrightarrow> a + x *\<^sub>R u \<in> D"
  shows "f a - f 0 \<ge> J0"
proof -
  from MVT_corrected[OF fderiv line_in] obtain t where
    t: "t\<in>Basis \<rightarrow> {0<..<1}" and
    mvt: "f a - f a = (\<Sum>i\<in>Basis. (J (a + t i *\<^sub>R u) u \<bullet> i) *\<^sub>R i)"
    sorry
  note mvt
  also have "\<dots> \<ge> J0"
  proof -
    have J: "\<And>i. i \<in> Basis \<Longrightarrow> J0 \<le> J (a + t i *\<^sub>R u) u"
      using J_ivl t line_in sorry (*by (auto simp: Pi_iff)*)
    show ?thesis
      using J
      unfolding atLeastAtMost_iff eucl_le[where 'a='b]
      by auto
  qed
  finally show ?thesis sorry
qed


lemma MVT_ivl'_restricted:
  fixes f::"'a::ordered_euclidean_space\<Rightarrow>'b::ordered_euclidean_space"
  assumes fderiv: "(\<And>x. x \<in> D \<Longrightarrow> (f has_derivative J x) (at x within D))"
  assumes J_ivl: "\<And>x. x \<in> D \<Longrightarrow> J x x \<ge> J0"
  assumes line_in: "\<And>x. x \<in> {0..1} \<Longrightarrow> b + x *\<^sub>R a \<in> D"
  shows "f a \<ge> f 0 + J0"
proof -
  have "f a - f 0 \<ge> J0"
    apply (rule MVT_ivl_restricted)
    apply (rule fderiv)
    apply assumption
    apply (rule J_ivl) apply assumption
    using line_in
    apply (auto simp: diff_le_eq le_diff_eq ac_simps)
    sorry
  thus ?thesis
    by (auto simp: diff_le_eq le_diff_eq ac_simps)
qed
lemma MVT0_within_restricted:
fixes f ::"real \<Rightarrow> real"
  and f'::"real \<Rightarrow> real \<Rightarrow> real"
  and s t :: real
assumes f':"\<And>x. x \<in> {0..t} \<Longrightarrow> (f has_derivative (f' x)) (at x  within {0..t})"
assumes geq':"\<And>x. x \<in> {0..t} \<Longrightarrow> f' x x \<ge> 0"
assumes int_s:"s > 0 \<and> s \<le> t"
assumes t: "0 < t"
shows "f t \<ge> f 0"
proof -
  have "f 0 + 0 \<le> f t"   
    apply (rule Lib.MVT_ivl'[OF f', of 0 s 0])
    subgoal for x by assumption
    subgoal for x using geq' by auto 
    using t int_s t apply auto
    subgoal for x
      by (metis int_s mult.commute mult.right_neutral order.trans real_mult_le_cancel_iff2)
    done
  then show "?thesis" by auto 
qed
*)
(*lemma MVT':
fixes f g ::"real \<Rightarrow> real"
fixes f' g'::"real \<Rightarrow> real \<Rightarrow> real"
fixes s t ::real
assumes f':"\<And>s. s \<in> {0..t} \<Longrightarrow> (f has_derivative (f' s)) (at s within {0..t})"
assumes g':"\<And>s. s \<in> {0..t} \<Longrightarrow> (g has_derivative (g' s)) (at s within {0..t})"
assumes geq':"\<And>x. x \<in> {0..t} \<Longrightarrow> f' x s \<ge> g' x s"
assumes geq0:"f 0 \<ge> g 0"
assumes int_s:"s > 0 \<and> s \<le> t"
assumes t:"t > 0"
shows "f s \<ge> g s"
proof -
  let ?h = "(\<lambda>x. f x - g x)"
  let ?h' = "(\<lambda>s x. f' s x - g' s x)"
  have "?h s \<ge> ?h 0"
    apply(rule MVT0_within[of t ?h "?h'" s])
    subgoal for s using f'[of s] g'[of s] by auto
    subgoal for sa using geq'[of sa] by auto
    subgoal using int_s by auto
    subgoal using t by auto
    done
  then show "?thesis" using geq0 by auto
qed
*)

lemma MVT':
fixes f g ::"real \<Rightarrow> real"
fixes f' g'::"real \<Rightarrow> real"
fixes s t ::real
assumes f':"\<And>s. s \<in> {0..t} \<Longrightarrow> (f has_derivative f') (at s within {0..t})"
assumes g':"\<And>s. s \<in> {0..t} \<Longrightarrow> (g has_derivative g') (at s within {0..t})"
assumes geq':"\<And>s. s \<in> {0..t} \<Longrightarrow> f' s \<ge> g' s"
assumes geq0:"f 0 \<ge> g 0"
assumes int_s:"s > 0 \<and> s \<le> t"
assumes t:"t > 0"
shows "f s \<ge> g s"
sorry


(*lemma vector_diff_chain_within:
  assumes "(f has_vector_derivative f') (at x within s)"
    and "(g has_vector_derivative g') (at (f x) within f ` s)"
  shows "((g \<circ> f) has_vector_derivative (f' *\<^sub>R g')) (at x within s)"
*)
(* f(g(x))' = f'(g(x))* g'(x)*)
lemma mychain:
fixes f::"real \<Rightarrow>'a::finite Rvec"
fixes g::"'a Rvec \<Rightarrow> real"
fixes f'::"real \<Rightarrow>'a::finite Rvec"
fixes g'::"'a Rvec \<Rightarrow> real"
assumes "\<And>s. (f has_derivative f') (at s within {0..t})"
assumes "\<And>s. (g has_derivative g') (at (f s) within f ` {0..t})"
shows "((g \<circ> f) has_derivative (g' \<circ> f')) (at s within {0..t})"
  sorry

lemma vec_chain:
assumes f:"(f has_vector_derivative f') (at s within {0..t})"
assumes g:"(g has_vector_derivative g') (at (f s) within f ` {0..t})"
shows "((g \<circ> f) has_vector_derivative g' *\<^sub>R f') (at s within {0..t})"
  apply(rule vector_diff_chain_within)
  using f g sledgehammer
  sledgehammer
  oops

lemma rift_in_space_time:
  fixes sol I ODE \<psi> \<theta> t s b
  assumes good_interp:"is_interp I"
  assumes free:"dfree \<theta>"
  assumes sol:"(sol solves_ode (\<lambda>_ \<nu>'. ODE_sem I ODE \<nu>')) {0..t} 
          {x. mk_v I ODE (sol 0, b) x \<in> fml_sem I \<psi>}"
  assumes FVT:"FVT \<theta> \<subseteq> semBV I ODE"  
  assumes ivl:"s \<in> {0..t}"
  shows "((\<lambda>t. sterm_sem I \<theta> (fst (mk_v I ODE (sol 0, b) (sol t))))
    (* This is Frechet derivative, so equivalent to
       has_real_derivative frechet I \<theta> (fst((mk_v I ODE (sol 0, b) (sol s)))) (snd (mk_v I ODE (sol 0, b) (sol s))))) (at s within {0..t})*)
    has_derivative (\<lambda>t'. t' * frechet I \<theta> (fst((mk_v I ODE (sol 0, b) (sol s)))) (snd (mk_v I ODE (sol 0, b) (sol s))))) (at s within {0..t})"
  proof -
    let ?\<phi> = "(\<lambda>t. (mk_v I ODE (sol 0, b) (sol t)))"
    let ?\<phi>s = "(\<lambda>t. fst (?\<phi> t))"
    have sol_deriv:"\<And>s. s \<in> {0..t} \<Longrightarrow> (sol has_derivative (\<lambda>xa. xa *\<^sub>R ODE_sem I ODE (sol s))) (at s within {0..t})"
      using sol apply simp 
      apply (drule solves_odeD(1))
      unfolding has_vderiv_on_def has_vector_derivative_def
      by auto
    have sol_dom:"\<And>s. s\<in> {0..t} \<Longrightarrow> ?\<phi> s \<in> fml_sem I \<psi>"
      using sol apply simp
      apply (drule solves_odeD(2))
      by auto
    let ?h = "(\<lambda>t. sterm_sem I \<theta> (?\<phi>s t))"
    let ?g = "(\<lambda>\<nu>. sterm_sem I \<theta> \<nu>)"
    let ?f = "?\<phi>s"
    let ?f' = "(\<lambda>t'. t' *\<^sub>R (\<chi> i. if i \<in> ODE_vars I ODE then ODE_sem I ODE (sol s) $ i else 0))"
    let ?g' = "(frechet I \<theta> (?\<phi>s s))"
    have heq:"?h = ?g \<circ> ?f" by (auto)
    have fact1:"\<And>i. i \<in> ODE_vars I ODE \<Longrightarrow> (\<lambda>t. ?\<phi>s(t) $ i) = (\<lambda>t. sol t $ i)"
      subgoal for i
        apply(rule ext)
        subgoal for t
          using mk_v_agree[of I ODE "(sol 0, b)" "sol t"]
          unfolding Vagree_def by auto
        done done
    have fact2:"\<And>i. i \<in> ODE_vars I ODE \<Longrightarrow> (\<lambda>t. if i \<in> ODE_vars I ODE then ODE_sem I ODE (sol t) $ i else 0) = (\<lambda>t. ODE_sem I ODE (sol t) $ i)"
      subgoal for i
        apply(rule ext)
        subgoal for t
          using mk_v_agree[of I ODE "(sol 0, b)" "sol t"]
          unfolding Vagree_def by auto
        done done
    have fact3:"\<And>i. i \<in> (-ODE_vars I ODE) \<Longrightarrow> (\<lambda>t. ?\<phi>s(t) $ i) = (\<lambda>t. sol 0 $ i)"
      subgoal for i
        apply(rule ext)
        subgoal for t
          using mk_v_agree[of I ODE "(sol 0, b)" "sol t"]
          unfolding Vagree_def by auto
        done done
    have fact4:"\<And>i. i \<in> (-ODE_vars I ODE) \<Longrightarrow> (\<lambda>t. if i \<in> ODE_vars I ODE then ODE_sem I ODE (sol t) $ i else 0) = (\<lambda>t. 0)"
      subgoal for i
        apply(rule ext)
        subgoal for t
          using mk_v_agree[of I ODE "(sol 0, b)" "sol t"]
          unfolding Vagree_def by auto
        done done
    have some_eq:"(\<lambda>v'. \<chi> i. v' *\<^sub>R ODE_sem I ODE (sol s) $ i) = (\<lambda>v'. v' *\<^sub>R ODE_sem I ODE (sol s))"
      apply(rule ext)
      apply(rule vec_extensionality)
      by auto
    have some_sol:"(sol has_derivative (\<lambda>v'. v' *\<^sub>R ODE_sem I ODE (sol s))) (at s within {0..t})"
      using sol ivl unfolding solves_ode_def has_vderiv_on_def has_vector_derivative_def by auto
    have some_eta:"(\<lambda>t. \<chi> i. sol t $ i) = sol" by (rule ext, rule vec_extensionality, auto)
    have ode_deriv:"\<And>i. i \<in> ODE_vars I ODE \<Longrightarrow> 
      ((\<lambda>t. sol t $ i) has_derivative (\<lambda> v'. v' *\<^sub>R ODE_sem I ODE (sol s) $ i)) (at s within {0..t})"
      subgoal for i
        apply(rule has_derivative_proj)
        using some_eq some_sol some_eta by auto
      done
    have eta:"(\<lambda>t. (\<chi> i. ?f t $ i)) = ?f" by(rule ext, rule vec_extensionality, auto)
    have eta_esque:"(\<lambda>t'. \<chi> i. t' * (if i \<in> ODE_vars I ODE then ODE_sem I ODE (sol s) $ i else 0)) =  
                    (\<lambda>t'. t' *\<^sub>R (\<chi> i. if i \<in> ODE_vars I ODE then ODE_sem I ODE (sol s) $ i else 0))"
      apply(rule ext | rule vec_extensionality)+
      subgoal for t' i by auto done
    have "((\<lambda>t. (\<chi> i. ?f t $ i)) has_derivative (\<lambda>t'. (\<chi> i. ?f' t' $ i))) (at s within {0..t})"
      apply (rule has_derivative_vec)
      subgoal for i       
        apply(cases "i \<in> ODE_vars I ODE")
        subgoal using fact1[of i] fact2[of i] ode_deriv[of i] by auto 
        subgoal using fact3[of i] fact4[of i] by auto 
      done
    done
    then have fderiv:"(?f has_derivative ?f') (at s within {0..t})" using eta eta_esque by auto
    have gderiv:"(?g has_derivative ?g') (at (?f s) within ?f ` {0..t})"
       using Derivative.has_derivative_at_within 
       using frechet_correctness free good_interp 
       by blast
    have chain:"((?g \<circ> ?f) has_derivative (?g' \<circ> ?f')) (at s within {0..t})"
      using fderiv gderiv diff_chain_within by blast
    (* (\<chi>i. if i \<in> ODE_vars I ODE then ODE_sem I ODE (sol sa) $ i else 0)
     (ODE_sem I ODE (\<chi>i. if i \<in> ODE_vars I ODE then ODE_sem I ODE (sol sa) $ i else 0))*)
      (* (fst (mk_v I ODE (sol 0, b) (sol sa))) (snd (mk_v I ODE (sol 0, b) (sol sa)))*)
      
    let ?co\<nu>1 = "(fst (mk_v I ODE (sol 0, b) (sol s)), ODE_sem I ODE (fst (mk_v I ODE (sol 0, b) (sol s))))"
    let ?co\<nu>2 = "(fst (mk_v I ODE (sol 0, b) (sol s)), snd (mk_v I ODE (sol 0, b) (sol s)))"
    have sub_cont:"\<And>a .a \<notin> ODE_vars I ODE \<Longrightarrow> Inl a \<in> FVT \<theta> \<Longrightarrow> False"
      using FVT by auto
    have sub_cont2:"\<And>a .a \<notin> ODE_vars I ODE \<Longrightarrow> Inr a \<in> FVT \<theta> \<Longrightarrow> False"
      using FVT by auto
    have co_agree:"Vagree (?co\<nu>1) (?co\<nu>2) (FVDiff \<theta>)"
      using mk_v_agree[of I ODE "(sol 0, b)" "sol s"]
      unfolding Vagree_def apply auto
      subgoal for i x
        apply(cases x)
        subgoal for a
          apply(cases "a \<in> ODE_vars I ODE")
          subgoal
            apply(erule allE[where x=i])+
            apply(simp)
            (* TODO: use coincidence *)
            using sub_cont[of a] coincidence_ode sorry
        subgoal for ba
          apply(erule allE[where x=i])+
          apply(simp)
          using sub_cont2[of ba] sorry
        done
        sorry
      done
        
    have frech_linear:"\<And>x \<theta> \<nu> \<nu>' I. x * frechet I \<theta> \<nu> \<nu>' = frechet I \<theta> \<nu> (x *\<^sub>R \<nu>')" sorry
    have heq'':"(?g' \<circ> ?f') = 
      (\<lambda>t'. t' *\<^sub>R frechet I \<theta> (?\<phi>s s) (snd (?\<phi> s)))
      (*(\<lambda>t. frechet I \<theta> (?\<phi>s t) (snd (?\<phi> t)))*)
      "
        using mk_v_agree[of I ODE "(sol 0, b)" "sol s"]
        unfolding comp_def
        using coincidence_frechet[OF free, of "(?co\<nu>1)" "(?co\<nu>2)", OF co_agree, of I]
        apply auto
        apply(rule ext | rule vec_extensionality)+
        subgoal for x
          using frech_linear[of x I \<theta> "(fst (mk_v I ODE (sol 0, b) (sol s)))" "(snd (mk_v I ODE (sol 0, b) (sol s)))"]
          apply auto
          using coincidence_frechet (* ... *)
          sorry
        sorry
    (*have "(\<lambda>s. (?g' (?f s) \<circ> ?f') s) = (\<lambda>s. ?g' (?f s) (?f' s))"
      by (rule ext, auto)*)
    have "((?g \<circ> ?f) has_derivative (?g' \<circ> ?f')) (at s within {0..t})"
      using chain by auto
    then have "((?g \<circ> ?f) has_derivative (\<lambda>t'. t' * frechet I \<theta> (?\<phi>s s) (snd (?\<phi> s)))) (at s within {0..t})"
      using heq'' by auto
    then have result:"((\<lambda>t. sterm_sem I \<theta> (?\<phi>s t))  has_derivative (\<lambda>t. t * frechet I \<theta> (?\<phi>s s) (snd (?\<phi> s)))) (at s within {0..t})"
      using heq by auto
    then show "?thesis" by auto
  qed

(*  
g(x)\<ge> h(x) \<rightarrow> p(x) \<and> [x'=f(x), c & p(x)](g(x)' \<ge> h(x)') \<rightarrow> [x'=f(x), c]g(x) \<ge> h(x)
*)
lemma DIGeq_valid:"valid DIGeqaxiom"
  (*  f1_def p1_def local.singleton.simps local.empty_def  *)
  apply(unfold DIGeqaxiom_def valid_def impl_sem iff_sem)
  apply(auto)
  proof -
    fix I::"('sf,'sc,'sz) interp" and  b aa ba 
      and sol::"real \<Rightarrow> 'sz simple_state" 
      and t::real
       let ?ODE = "OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)"
       let ?\<phi> = "(\<lambda>t. mk_v I (?ODE) (sol 0, b) (sol t))"
       assume good_interp:"is_interp I"
       and geq0:"dterm_sem I (f1 fid3 vid1) (sol 0, b) \<le> dterm_sem I (f1 fid2 vid1) (sol 0, b)"
       and ev0:"(sol 0, b) \<in> fml_sem I (p1 vid1 vid1)"
       and box:"\<forall>a ba. (\<exists>sola. sol 0 = sola 0 \<and>
                      (\<exists>t. (a, ba) = mk_v I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (sola 0, b) (sola t) \<and>
                           0 \<le> t \<and>
                           (sola solves_ode (\<lambda>a b. (\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0) + ODEs I vid1 b)) {0..t}
                            {x. mk_v I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (sola 0, b) x \<in> fml_sem I (p1 vid1 vid1)})) \<longrightarrow>
              directional_derivative I (f1 fid3 vid1) (a, ba) \<le> directional_derivative I (f1 fid2 vid1) (a, ba)"
       and aaba:"(aa, ba) = ?\<phi> t"
       and t:"0 \<le> t"
       and sol:"(sol solves_ode (\<lambda>a b. (\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0) + ODEs I vid1 b)) {0..t}
        {x. mk_v I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (sol 0, b) x \<in> fml_sem I (p1 vid1 vid1)}"
       from geq0 
       have geq0':"sterm_sem I (f1 fid3 vid1) (sol 0) \<le> sterm_sem I (f1 fid2 vid1) (sol 0)"
         sorry
       let ?\<phi>s = "\<lambda>x. fst (?\<phi> x)"
       let ?\<phi>t = "\<lambda>x. snd (?\<phi> x)"
       let ?df1 = "(\<lambda>t. dterm_sem I (f1 fid3 vid1) (?\<phi> t))"
       let ?f1 = "(\<lambda>t. sterm_sem I (f1 fid3 vid1) (?\<phi>s t))"
       let ?f1' = "(\<lambda>s. frechet I (f1 fid3 vid1) (?\<phi>s s) (?\<phi>t s))"
       have dfeq:"?df1 = ?f1" sorry
       have free1:"dfree ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))"
         by (auto intro: dfree.intros)
       have free2:"dfree ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))"
         by (auto intro: dfree.intros)
       have free3:"dfree (f1 fid3 vid1)" unfolding f1_def by (auto intro: dfree.intros)
       let ?df2 = "(\<lambda>t. dterm_sem I (f1 fid2 vid1) (?\<phi> t))"
       let ?f2 = "(\<lambda>t. sterm_sem I (f1 fid2 vid1) (?\<phi>s t))"
       let ?f2' = "(\<lambda>s. frechet I (f1 fid2 vid1) (?\<phi>s s) (?\<phi>t s))"
       let ?int = "{0..t}"
       have bluh:"\<And>x i. (Functions I i has_derivative (THE f'. \<forall>x. (Functions I i has_derivative f' x) (at x)) x) (at x)"
         using good_interp unfolding is_interp_def by auto
       have blah:"(Functions I fid3 has_derivative (THE f'. \<forall>x. (Functions I fid3 has_derivative f' x) (at x)) (\<chi> i. if i = vid1 then sol t $ vid1 else 0)) (at (\<chi> i. if i = vid1 then sol t $ vid1 else 0))"
         using bluh by auto
       have bigEx:"\<And>s. s \<in> {0..t} \<Longrightarrow>(\<exists>sola. sol 0 = sola 0 \<and>
            (\<exists>ta. (fst (?\<phi> s),
                   snd (?\<phi> s)) =
                  mk_v I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (sola 0, b) (sola ta) \<and>
                  0 \<le> ta \<and>
                  (sola solves_ode (\<lambda>a b. (\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0) + ODEs I vid1 b)) {0..ta}
                   {x. mk_v I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (sola 0, b) x \<in> fml_sem I (p1 vid1 vid1)}))"
         subgoal for s
           apply(rule exI[where x=sol])
           apply(rule conjI)
           subgoal by (rule refl)
           apply(rule exI[where x=s])
           apply(rule conjI)
           subgoal by auto 
           apply(rule conjI)
           subgoal by auto
           using sol
           by (meson atLeastAtMost_iff atLeastatMost_subset_iff order_refl solves_ode_on_subset)
         done
       have box':"\<And>s. s \<in> {0..t} \<Longrightarrow> directional_derivative I (f1 fid3 vid1) (?\<phi>s s, ?\<phi>t s) \<le> directional_derivative I (f1 fid2 vid1) (?\<phi>s s, ?\<phi>t s)"
         subgoal for s
         using box 
         apply simp
         apply (erule allE[where x="?\<phi>s s"])
         apply (erule allE[where x="?\<phi>t s"])
         using bigEx by auto
       done
       (*have eq_vid1:"fst (mk_v I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (sol 0, b) (sol 0)) $ vid1 = sol 0 $ vid1"
         using mk_v_agree[of I "(OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1))" "(sol 0, b)" "sol 0"]
         unfolding Vagree_def by auto*)
       have dsafe1:"dsafe (f1 fid3 vid1)" unfolding f1_def by (auto intro: dsafe.intros)
       have dsafe2:"dsafe (f1 fid2 vid1)" unfolding f1_def by (auto intro: dsafe.intros)
       have agree1:"Vagree (sol 0, b) (?\<phi> 0) (FVT (f1 fid3 vid1))"
           using mk_v_agree[of I "(OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1))" "(sol 0, b)" "sol 0"]
           unfolding f1_def Vagree_def expand_singleton by auto
       have agree2:"Vagree (sol 0, b) (?\<phi> 0) (FVT (f1 fid2 vid1))"
           using mk_v_agree[of I "(OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1))" "(sol 0, b)" "sol 0"]
           unfolding f1_def Vagree_def expand_singleton by auto
       have sem_eq1:"dterm_sem I (f1 fid3 vid1) (sol 0, b) = dterm_sem I (f1 fid3 vid1) (?\<phi> 0)"
         using coincidence_dterm[OF dsafe1 agree1] by auto
       then have sem_eq1':"sterm_sem I (f1 fid3 vid1) (sol 0) = sterm_sem I (f1 fid3 vid1) (?\<phi>s 0)"
         sorry
       have sem_eq2:"dterm_sem I (f1 fid2 vid1) (sol 0, b) = dterm_sem I (f1 fid2 vid1) (?\<phi> 0)"
         using coincidence_dterm[OF dsafe2 agree2] by auto
       then have sem_eq2':"sterm_sem I (f1 fid2 vid1) (sol 0) = sterm_sem I (f1 fid2 vid1) (?\<phi>s 0)"
         sorry
       have good_interp':"\<And>i x. (Functions I i has_derivative (THE f'. \<forall>x. (Functions I i has_derivative f' x) (at x)) x) (at x)"
         using good_interp unfolding is_interp_def by auto
       (*(?f has_derivative ?f') (at ?x) \<Longrightarrow> (?g has_derivative ?g') (at (?f ?x)) \<Longrightarrow> (?g \<circ> ?f has_derivative ?g' \<circ> ?f') (at ?x)*) 
       note chain = Deriv.derivative_intros(105)
        
       have sol1:"(sol solves_ode (\<lambda>_. ODE_sem I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)))) {0..t}
   {x. mk_v I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (sol 0, b) x \<in> fml_sem I (p1 vid1 vid1)}"
         using sol by auto
       
       have FVTsub1:"FVT ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) \<subseteq> semBV I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1))"
         apply auto
         subgoal for x xa
           apply(cases "xa = vid1")
           by auto
         done
       have FVTsub2:"FVT ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) \<subseteq> semBV I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1))"
         apply auto
         subgoal for x xa
           apply(cases "xa = vid1")
           by auto
         done
       have deriv1:"\<And>s. s \<in> ?int \<Longrightarrow> (?f1 has_derivative (?f1')) (at s within {0..t})"
         subgoal for s
           using  rift_in_space_time[OF good_interp free1  sol1 FVTsub1] 
           by (auto simp add: f1_def expand_singleton directional_derivative_def)
         done
       have deriv2:"\<And>s. s \<in> ?int \<Longrightarrow> (?f2 has_derivative (?f2')) (at s within {0..t})"
         subgoal for s
           using  rift_in_space_time[OF good_interp free2 sol1 FVTsub2] by (auto simp add: f1_def expand_singleton directional_derivative_def)
         done
       have leq:"\<And>s . s \<in> ?int \<Longrightarrow> ?f1' s \<le> ?f2' s"
         subgoal for s using box'[of s] 
           by (simp add: directional_derivative_def)
         done
       
       have "?f1 t \<le> ?f2 t"
         apply(cases "t = 0")
         subgoal using geq0' sem_eq1' sem_eq2' by auto  
         subgoal
           apply (rule MVT'[of t ?f2 "?f2'" ?f1 "?f1'" t])
           subgoal using deriv2 by auto
           subgoal using deriv1 by auto
           subgoal for sa 
             subgoal using leq[of sa] 
               by blast
           done
         subgoal using geq0 sorry (* think i can actually do this one *)
         subgoal using t by auto
         subgoal using t by auto
         done
       done
       then show
       " dterm_sem I (f1 fid3 vid1) (mk_v I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (sol 0, b) (sol t))
       \<le> dterm_sem I (f1 fid2 vid1) (mk_v I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (sol 0, b) (sol t))"
         using t sorry (* think i can actually do this one *)
  qed
(*
       have hmm1:"\<exists>f. ((\<lambda>t. dterm_sem I (if vid1 = vid1 then trm.Var vid1 else Const 0)
                (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (OVar vid1)) (sol 0, b)
                  (sol t))) has_derivative
          f vid1)
          (at t)"
         apply(rule exI)
         apply(auto intro: derivative_eq_intros)
         using frechet_correctness 
         sorry
       have hmm2:"\<exists>f. ((\<lambda>t. dterm_sem I (Const 0)
                (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (OVar vid1)) (sol 0, b)
                  (sol t))) has_derivative
          f vid1)
          (at t)"
         apply(rule exI)
         by(auto intro: derivative_eq_intros)*)
       
lemma DG_valid:"valid DGaxiom"
  apply(auto simp add: DGaxiom_def valid_def Let_def)
  sorry
end end

