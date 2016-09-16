theory "Differential_Axioms" 
imports
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

(* [{1' = 1(1) & 1(1)}]2(1) <->
   \<exists>2. [{1'=1(1), 2' = 2(1)*2 + 3(1) & 1(1)}]2(1)*)
definition DGaxiom :: "('sf, 'sc, 'sz) formula"
  where "DGaxiom = (([[EvolveODE (OSing vid1 (f1 fid1 vid1)) (p1 vid1 vid1)]]p1 vid2 vid1) \<leftrightarrow> 
  (Exists vid2 
    ([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1)) (OSing vid2 (Plus (Times (f1 fid2 vid1) (Var vid2)) (f1 fid3 vid1)))) (p1 vid1 vid1)]]
       p1 vid2 vid1)))"

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

lemma MVT':
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

lemma frech_linear:
  fixes x \<theta> \<nu> \<nu>' I
  assumes good_interp:"is_interp I"
  shows "dfree \<theta> \<Longrightarrow> x * frechet I \<theta> \<nu> \<nu>' = frechet I \<theta> \<nu> (x *\<^sub>R \<nu>')"
  proof(induction rule: dfree.induct)
    case (dfree_Var i)
    then show ?case by auto
  next
    case (dfree_Const r)
    then show ?case by auto
  next
    case (dfree_Fun args i)
      assume frees:"\<And>i. dfree (args i)"
      assume IH:"\<And>i. x * frechet I (args i) \<nu> \<nu>' = frechet I (args i) \<nu> (x *\<^sub>R \<nu>')"
      have IH':"(\<chi> i. x * frechet I (args i) \<nu> \<nu>') = (\<chi> i. frechet I (args i) \<nu> (x *\<^sub>R \<nu>'))"
        by(rule vec_extensionality, auto simp add: IH)
      have frech:"(Functions I i has_derivative FunctionFrechet I i (\<chi> i. sterm_sem I (args i) \<nu>)) (at (\<chi> i. sterm_sem I (args i) \<nu>))"
        using good_interp unfolding is_interp_def by blast
      then have blin:"bounded_linear (FunctionFrechet I i (\<chi> i. sterm_sem I (args i) \<nu>))"
        using has_derivative_bounded_linear by auto
      show ?case using blin IH' unfolding frechet.simps
        by (metis (mono_tags) dfree_Fun_simps frechet.simps(2) frechet_correctness frees good_interp has_derivative_bounded_linear linear_simps(5) real_scaleR_def)
  next
    case (dfree_Plus \<theta>\<^sub>1 \<theta>\<^sub>2)
    then show ?case 
      by (simp add: semiring_normalization_rules(34))
  next
    case (dfree_Times \<theta>\<^sub>1 \<theta>\<^sub>2)
    then show ?case 
      by (simp add: semiring_normalization_rules)
  qed
    
lemma rift_in_space_time:
  fixes sol I ODE \<psi> \<theta> t s b
  assumes good_interp:"is_interp I"
  assumes free:"dfree \<theta>"
  assumes osafe:"osafe ODE"
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
    let ?co\<nu>1 = "(fst (mk_v I ODE (sol 0, b) (sol s)), ODE_sem I ODE (fst (mk_v I ODE (sol 0, b) (sol s))))"
    let ?co\<nu>2 = "(fst (mk_v I ODE (sol 0, b) (sol s)), snd (mk_v I ODE (sol 0, b) (sol s)))"
    have sub_cont:"\<And>a .a \<notin> ODE_vars I ODE \<Longrightarrow> Inl a \<in> FVT \<theta> \<Longrightarrow> False"
      using FVT by auto
    have sub_cont2:"\<And>a .a \<notin> ODE_vars I ODE \<Longrightarrow> Inr a \<in> FVT \<theta> \<Longrightarrow> False"
      using FVT by auto
    have "Vagree (mk_v I ODE (sol 0, b) (sol s)) (sol s, b) (Inl ` ODE_vars I ODE)"
      using mk_v_agree[of I ODE "(sol 0, b)" "sol s"]
      unfolding Vagree_def by auto
    let ?co'\<nu>1 = "(\<lambda>x. (fst (mk_v I ODE (sol 0, b) (sol s)), x *\<^sub>R (\<chi> i. if i \<in> ODE_vars I ODE then ODE_sem I ODE (sol s) $ i else 0)))"
    let ?co'\<nu>2 = "(\<lambda>x. (fst (mk_v I ODE (sol 0, b) (sol s)), x *\<^sub>R snd (mk_v I ODE (sol 0, b) (sol s))))"
    have co_agree_sem:"\<And>s. Vagree (?co'\<nu>1 s) (?co'\<nu>2 s) (semBV I ODE)"
      subgoal for sa
      using mk_v_agree[of I ODE "(sol 0, b)" "sol s"]
      unfolding Vagree_def by auto
      done
    have co_agree_help:"\<And>s. Vagree (?co'\<nu>1 s) (?co'\<nu>2 s) (FVT \<theta>)"
      using agree_sub[OF FVT co_agree_sem] by auto
    have co_agree':"\<And>s. Vagree (?co'\<nu>1 s) (?co'\<nu>2 s) (FVDiff \<theta>)"
      subgoal for s
      using mk_v_agree[of I ODE "(sol 0, b)" "sol s"]
      unfolding Vagree_def apply auto
      subgoal for i x
        apply(cases x)
        subgoal for a
          apply(cases "a \<in> ODE_vars I ODE")
          subgoal
            apply(erule allE[where x=i])+
            apply(simp)
            by (metis (no_types, lifting) FVT ODE_vars_lr Vagree_def mk_v_agree mk_xode.elims set_mp snd_conv)
          subgoal
            apply(erule allE[where x=i])+
            by(simp)
        done
        subgoal for a
             apply(cases "a \<in> ODE_vars I ODE")
          subgoal
            apply(erule allE[where x=i])+
            apply(simp)
            by (metis (no_types, lifting) FVT ODE_vars_lr Vagree_def mk_v_agree mk_xode.elims set_mp snd_conv)
          subgoal
            apply(erule allE[where x=i])+
            by(simp)
          done
        done
      subgoal for i x
        apply(cases x)
        subgoal for a
          apply(cases "a \<in> ODE_vars I ODE")
          subgoal
            apply(erule allE[where x=i])+
            by(simp)
            
          subgoal
            apply(erule allE[where x=i])+
            using FVT ODE_vars_lr Vagree_def mk_v_agree mk_xode.elims set_mp snd_conv
            by auto
        done
        subgoal for a
          apply(cases "a \<in> ODE_vars I ODE")
          subgoal
            apply(erule allE[where x=i])+
            by(simp)
          subgoal
            apply(erule allE[where x=i])+
            using FVT ODE_vars_lr Vagree_def mk_v_agree mk_xode.elims set_mp snd_conv
            by auto
          done
        done
      done
    done 
    have heq'':"(?g' \<circ> ?f') = (\<lambda>t'. t' *\<^sub>R frechet I \<theta> (?\<phi>s s) (snd (?\<phi> s)))"
        using mk_v_agree[of I ODE "(sol 0, b)" "sol s"]
        unfolding comp_def
        apply auto
        apply(rule ext | rule vec_extensionality)+
        subgoal for x
          using frech_linear[of I \<theta> x "(fst (mk_v I ODE (sol 0, b) (sol s)))" "(snd (mk_v I ODE (sol 0, b) (sol s)))", OF good_interp free]
          apply auto
          using coincidence_frechet[OF free, of "(?co'\<nu>1 x)" "(?co'\<nu>2 x)", OF co_agree'[of x], of I]
          by auto
        done
    have "((?g \<circ> ?f) has_derivative (?g' \<circ> ?f')) (at s within {0..t})"
      using chain by auto
    then have "((?g \<circ> ?f) has_derivative (\<lambda>t'. t' * frechet I \<theta> (?\<phi>s s) (snd (?\<phi> s)))) (at s within {0..t})"
      using heq'' by auto
    then have result:"((\<lambda>t. sterm_sem I \<theta> (?\<phi>s t))  has_derivative (\<lambda>t. t * frechet I \<theta> (?\<phi>s s) (snd (?\<phi> s)))) (at s within {0..t})"
      using heq by auto
    then show "?thesis" by auto
  qed

lemma dterm_sterm_dfree:
   "dfree \<theta> \<Longrightarrow> (\<And>\<nu> \<nu>'. sterm_sem I \<theta> \<nu> = dterm_sem I \<theta> (\<nu>, \<nu>'))"
  by(induction rule: dfree.induct, auto)
    
(*  
g(x)\<ge> h(x) \<rightarrow> p(x) \<and> [x'=f(x), c & p(x)](g(x)' \<ge> h(x)') \<rightarrow> [x'=f(x), c]g(x) \<ge> h(x)
*)
lemma DIGeq_valid:"valid DIGeqaxiom"
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
       have free1:"dfree ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))"
         by (auto intro: dfree.intros)
       have free2:"dfree ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))"
         by (auto intro: dfree.intros)
       from geq0 
       have geq0':"sterm_sem I (f1 fid3 vid1) (sol 0) \<le> sterm_sem I (f1 fid2 vid1) (sol 0)"
         unfolding f1_def using dterm_sterm_dfree[OF free1, of I "sol 0" b] dterm_sterm_dfree[OF free2, of I "sol 0" b] by auto  
       let ?\<phi>s = "\<lambda>x. fst (?\<phi> x)"
       let ?\<phi>t = "\<lambda>x. snd (?\<phi> x)"
       let ?df1 = "(\<lambda>t. dterm_sem I (f1 fid3 vid1) (?\<phi> t))"
       let ?f1 = "(\<lambda>t. sterm_sem I (f1 fid3 vid1) (?\<phi>s t))"
       let ?f1' = "(\<lambda> s t'. t' * frechet I (f1 fid3 vid1) (?\<phi>s s) (?\<phi>t s))"
       have dfeq:"?df1 = ?f1" 
         apply(rule ext)
         subgoal for t
          using dterm_sterm_dfree[OF free1, of I "?\<phi>s t" "snd (?\<phi> t)"] unfolding f1_def expand_singleton by auto
        done
       have free3:"dfree (f1 fid3 vid1)" unfolding f1_def by (auto intro: dfree.intros)
       let ?df2 = "(\<lambda>t. dterm_sem I (f1 fid2 vid1) (?\<phi> t))"
       let ?f2 = "(\<lambda>t. sterm_sem I (f1 fid2 vid1) (?\<phi>s t))"
       let ?f2' = "(\<lambda>s t' . t' * frechet I (f1 fid2 vid1) (?\<phi>s s) (?\<phi>t s))"
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
         using dterm_sterm_dfree[OF free1, of I "sol 0" "b"] dterm_sterm_dfree[OF free1, of I "(?\<phi>s 0)" "snd (?\<phi> 0)"]
         unfolding f1_def expand_singleton by auto
       have sem_eq2:"dterm_sem I (f1 fid2 vid1) (sol 0, b) = dterm_sem I (f1 fid2 vid1) (?\<phi> 0)"
         using coincidence_dterm[OF dsafe2 agree2] by auto
       then have sem_eq2':"sterm_sem I (f1 fid2 vid1) (sol 0) = sterm_sem I (f1 fid2 vid1) (?\<phi>s 0)" 
         using dterm_sterm_dfree[OF free2, of I "sol 0" "b"] dterm_sterm_dfree[OF free2, of I "(?\<phi>s 0)" "snd (?\<phi> 0)"]
         unfolding f1_def expand_singleton by auto
       have good_interp':"\<And>i x. (Functions I i has_derivative (THE f'. \<forall>x. (Functions I i has_derivative f' x) (at x)) x) (at x)"
         using good_interp unfolding is_interp_def by auto
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
       have osafe:"osafe (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1))"
         apply (rule osafe_Prod)
         apply (rule osafe_Sing)
         subgoal unfolding f1_def expand_singleton
           apply(rule dfree_Fun)
           subgoal for i apply(cases "i = vid1") apply (auto, rule dfree_Const) done
           done
         apply (rule osafe_Var)
         by auto
       have deriv1:"\<And>s. s \<in> ?int \<Longrightarrow> (?f1 has_derivative (?f1' s)) (at s within {0..t})"
         subgoal for s
           using  rift_in_space_time[OF good_interp free1 osafe sol1 FVTsub1, of s] 
           unfolding f1_def expand_singleton directional_derivative_def
           by blast
         done
       have deriv2:"\<And>s. s \<in> ?int \<Longrightarrow> (?f2 has_derivative (?f2' s)) (at s within {0..t})"
         subgoal for s
           using rift_in_space_time[OF good_interp free2 osafe sol1 FVTsub2, of s] 
           unfolding f1_def expand_singleton directional_derivative_def
           by blast
         done
       have leq:"\<And>s . s \<in> ?int \<Longrightarrow> ?f1' s 1 \<le> ?f2' s 1"
         subgoal for s using box'[of s] 
           by (simp add: directional_derivative_def)
         done
       have "?f1 t \<le> ?f2 t"
         apply(cases "t = 0")
         subgoal using geq0' sem_eq1' sem_eq2' by auto  
         subgoal
           apply (rule MVT'[OF deriv2 deriv1, of t])
           subgoal by auto
           subgoal by auto
           subgoal for s using deriv2[of s] using leq by auto
           subgoal using geq0' sem_eq1' sem_eq2' by auto
           using t by auto
         done
       then show
       " dterm_sem I (f1 fid3 vid1) (mk_v I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (sol 0, b) (sol t))
       \<le> dterm_sem I (f1 fid2 vid1) (mk_v I (OProd (OSing vid1 (f1 fid1 vid1)) (OVar vid1)) (sol 0, b) (sol t))"
         using t 
         dterm_sterm_dfree[OF free2, of I "?\<phi>s t" "snd (?\<phi> t)"]
         dterm_sterm_dfree[OF free1, of I "?\<phi>s t" "snd (?\<phi> t)"]
         by (simp add: f1_def)
  qed

lemma DG_valid:"valid DGaxiom"
  proof -
    have osafe:"osafe (OSing vid1 (f1 fid1 vid1))" 
      by(auto simp add: osafe_Sing dfree_Fun dfree_Const f1_def expand_singleton)
    have fsafe:"fsafe (p1 vid1 vid1)" 
      by(auto simp add: p1_def dfree_Const)
    have osafe2:"osafe (OProd (OSing vid1 (f1 fid1 vid1)) (OSing vid2 (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1))))"
      apply(auto simp add: f1_def expand_singleton)
      apply(rule osafe_Prod)
      apply(rule osafe_Sing)
      apply(rule dfree_Fun)
      subgoal for i by (auto simp add: dfree_Const)
      apply(rule osafe_Sing)
      apply(rule dfree_Plus)
      apply(rule dfree_Times)
      apply(rule dfree_Fun)
      subgoal for i by (auto simp add: dfree_Const)
      apply(rule dfree_Var)
      apply(rule dfree_Fun)
      subgoal for i by (auto simp add: dfree_Const)
      by (auto simp add: vne12)
    note sem = ode_alt_sem[OF osafe fsafe]
    note sem2 = ode_alt_sem[OF osafe2 fsafe]

    have p2safe:"fsafe (p1 vid2 vid1)" by(auto simp add: p1_def dfree_Const)
    show "valid DGaxiom"
    apply(auto simp  del: prog_sem.simps(8) simp add: DGaxiom_def valid_def sem sem2)
    apply(rule exI[where x=0], auto simp add: f1_def p1_def expand_singleton)
    subgoal for I a b aa ba sol t
      proof -
        assume good_interp:"is_interp I"
        assume "
 \<forall>aa ba. (\<exists>sol t. (aa, ba) = mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (sol t) \<and>
                        0 \<le> t \<and>
                        (sol solves_ode (\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0)) {0..t}
                         {x. Predicates I vid1
                              (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                                     (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) x))} \<and>
                        VSagree (sol 0) a {uu. uu = vid1 \<or> (\<exists>x. Inl uu \<in> FVT (if x = vid1 then trm.Var vid1 else Const 0))}) \<longrightarrow>
               Predicates I vid2 (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) (aa, ba))"
        then have 
          bigAll:"
\<And>aa ba. (\<exists>sol t. (aa, ba) = mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (sol t) \<and>
                        0 \<le> t \<and>
                        (sol solves_ode (\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0)) {0..t}
                         {x. Predicates I vid1
                              (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                                     (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) x))} \<and>
                        VSagree (sol 0) a {uu. uu = vid1 \<or> (\<exists>x. Inl uu \<in> FVT (if x = vid1 then trm.Var vid1 else Const 0))}) \<longrightarrow>
               Predicates I vid2 (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) (aa, ba))"
          by (auto)
       assume aaba:"(aa, ba) =
    mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
             (OSing vid2
               (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                 ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
     (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b) (sol t)"
     assume t:"0 \<le> t"
     assume sol:"
       (sol solves_ode
     (\<lambda>a b. (\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0) +
            (\<chi> i. if i = vid2 then sterm_sem I (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1)) b else 0)))
     {0..t} {x. Predicates I vid1
                 (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                        (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                                  (OSing vid2
                                    (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                                      ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
                          (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b) x))}"
     assume VSag:"VSagree (sol 0) (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y) {x. x = vid2 \<or> x = vid1 \<or> x = vid2 \<or> x = vid1}"
     let ?sol = "(\<lambda>t. \<chi> i. if i = vid1 then sol t $ vid1 else 0)"
     let ?aaba' = "mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (?sol t)"
     from bigAll[of "fst ?aaba'" "snd ?aaba'"] 
     have bigEx:"(\<exists>sol t. ?aaba' = mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (sol t) \<and>
                        0 \<le> t \<and>
                        (sol solves_ode (\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0)) {0..t}
                         {x. Predicates I vid1
                              (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                                     (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) x))} \<and>
                        VSagree (sol 0) a {uu. uu = vid1 \<or> (\<exists>x. Inl uu \<in> FVT (if x = vid1 then trm.Var vid1 else Const 0))}) \<longrightarrow>
               Predicates I vid2 (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) (?aaba'))" 
          by simp
        have pre1:"?aaba' = mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (?sol t)" 
          by (rule refl)
        have agreeL:"\<And>s. fst (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                      (OSing vid2
                        (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                          ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
              (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b) (sol s)) $ vid1 = sol s $ vid1"
          subgoal for s
            using mk_v_agree[of I "(OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                      (OSing vid2
                        (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                          ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))" "(\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b)" "(sol s)"]
          unfolding Vagree_def by auto done
        have agreeR:"\<And>s. fst (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (\<chi> i. if i = vid1 then sol s $ vid1 else 0)) $ vid1 = sol s $ vid1" 
          subgoal for s
            using mk_v_agree[of "I" "(OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))" "(a, b)" "(\<chi> i. if i = vid1 then sol s $ vid1 else 0)"]
            unfolding Vagree_def by auto
          done
        have FV:"(FVF (p1 vid1 vid1)) = {Inl vid1}" unfolding p1_def expand_singleton
            apply auto subgoal for x xa apply(cases "xa = vid1") by auto done
        have agree:"\<And>s. Vagree (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                      (OSing vid2
                        (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                          ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
              (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b) (sol s)) (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (\<chi> i. if i = vid1 then sol s $ vid1 else 0)) (FVF (p1 vid1 vid1))"
          using agreeR agreeL unfolding Vagree_def FV by auto
        note con_sem_eq = coincidence_formula[OF fsafe Iagree_refl agree]
        have constraint:"\<And>s. 0 \<le> s \<and> s \<le> t \<Longrightarrow>
          Predicates I vid1
          (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (\<chi> i. if i = vid1 then sol s $ vid1 else 0)))"
          using sol apply simp
          apply(drule solves_odeD(2))
          apply auto[1]
          subgoal for s using con_sem_eq by (auto simp add: p1_def expand_singleton)
          done
        have eta:"sol = (\<lambda>t. \<chi> i. sol t $ i)" by (rule ext, rule vec_extensionality, simp)
        have yet_another_eq:"\<And>x. (\<lambda>xa. xa *\<^sub>R ((\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) (sol x) else 0) +
                           (\<chi> i. if i = vid2 then sterm_sem I (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1)) (sol x) else 0)))
= (\<lambda>xa. (\<chi> i. (xa *\<^sub>R ((\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) (sol x) else 0) +
                           (\<chi> i. if i = vid2 then sterm_sem I (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1)) (sol x) else 0))) $ i))"
          subgoal for x by (rule ext, rule vec_extensionality, simp) done
        have sol_deriv:"\<And>x. x \<in>{0..t} \<Longrightarrow>
            (sol has_derivative
             (\<lambda>xa. xa *\<^sub>R ((\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) (sol x) else 0) +
                           (\<chi> i. if i = vid2 then sterm_sem I (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1)) (sol x) else 0))))
             (at x within {0..t})"
          using sol apply simp
          apply(drule solves_odeD(1))
          unfolding has_vderiv_on_def has_vector_derivative_def by auto
        then have sol_deriv:"\<And>x. x \<in> {0..t} \<Longrightarrow>
            ((\<lambda>t. \<chi> i. sol t $ i) has_derivative
             (\<lambda>xa. (\<chi> i. (xa *\<^sub>R ((\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) (sol x) else 0) +
                           (\<chi> i. if i = vid2 then sterm_sem I (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1)) (sol x) else 0))) $ i)))
             (at x within {0..t})" using yet_another_eq eta by auto
         have sol_deriv1: "\<And>x. x \<in> {0..t} \<Longrightarrow>
            ((\<lambda>t. sol t $ vid1) has_derivative
             (\<lambda>xa. (xa *\<^sub>R ((\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) (sol x) else 0) +
                           (\<chi> i. if i = vid2 then sterm_sem I (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1)) (sol x) else 0)) $ vid1)))
             (at x within {0..t})"
           subgoal for s
             (* I heard higher-order unification is hard.*)
           apply(rule has_derivative_proj[of "(\<lambda> i t. sol t $ i)" "(\<lambda>j xa. (xa *\<^sub>R ((\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) (sol s) else 0) +
                           (\<chi> i. if i = vid2 then sterm_sem I (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1)) (sol s) else 0)) $ j))" "at s within {0..t}""vid1"])
           using sol_deriv[of s] by auto done
       have hmm:"\<And>s. (\<chi> i. sterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) (sol s)) = (\<chi> i. sterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) (\<chi> i. if i = vid1 then sol s $ vid1 else 0))"
         by(rule vec_extensionality, auto)
       have aha:"\<And>s. (\<lambda>xa. xa * sterm_sem I (f1 fid1 vid1) (sol s)) = (\<lambda>xa. xa * sterm_sem I (f1 fid1 vid1) (\<chi> i. if i = vid1 then sol s $ vid1 else 0))"
         subgoal for s
         apply(rule ext)
         subgoal for  xa using hmm by (auto simp add: f1_def) done done 
        let ?sol' = "(\<lambda>s. (\<lambda>xa. \<chi> i. if i = vid1 then xa * sterm_sem I (f1 fid1 vid1) (\<chi> i. if i = vid1 then sol s $ vid1 else 0) else 0))"
        let ?project_me_plz = "(\<lambda>t. (\<chi> i. if i = vid1 then ?sol t $ vid1 else 0))"
        have sol_deriv_eq:"\<And>s. s \<in>{0..t} \<Longrightarrow>
       ((\<lambda>t. (\<chi> i. if i = vid1 then ?sol t $ vid1 else 0)) has_derivative ?sol' s) (at s within {0..t})"
          subgoal for s
            apply(rule has_derivative_vec)
            subgoal for i
              apply (cases "i = vid1", cases "i = vid2", auto)
              using vne12 apply simp
              using sol_deriv1[of s] using aha by auto
            done done
          have yup:"(\<lambda>t. (\<chi> i. if i = vid1 then ?sol t $ vid1 else 0) $ vid1) = (\<lambda>t. sol t $ vid1)"
            by(rule ext, auto)
          have maybe:"\<And>s. (\<lambda>xa. xa * sterm_sem I (f1 fid1 vid1) (\<chi> i. if i = vid1 then sol s $ vid1 else 0)) = (\<lambda>xa. (\<chi> i. if i = vid1 then xa * sterm_sem I (f1 fid1 vid1) (\<chi> i. if i = vid1 then sol s $ vid1 else 0) else 0) $ vid1) "
            by(rule ext, auto)
          have almost:"(\<lambda>x. if vid1 = vid1 then (\<chi> i. if i = vid1 then sol x $ vid1 else 0) $ vid1 else 0) =
(\<lambda>x.  (\<chi> i. if i = vid1 then sol x $ vid1 else 0) $ vid1)" by(rule ext, auto)

          have almost':"\<And>s. (\<lambda>h. if vid1 = vid1 then h * sterm_sem I (f1 fid1 vid1) (\<chi> i. if i = vid1 then sol s $ vid1 else 0) else 0) = (\<lambda>h. h * sterm_sem I (f1 fid1 vid1) (\<chi> i. if i = vid1 then sol s $ vid1 else 0))"
            by(rule ext, auto)
        have deriv':" \<And>x. x \<in> {0..t} \<Longrightarrow>
       ((\<lambda>t. \<chi> i. if i = vid1 then sol t $ vid1 else 0) has_derivative
        (\<lambda>xa. (\<chi> i. xa *\<^sub>R (if i = vid1 then sterm_sem I (f1 fid1 vid1) (\<chi> i. if i = vid1 then sol x $ vid1 else 0) else 0))))
        (at x within {0..t})"
          subgoal for s
            apply(rule has_derivative_vec)
            subgoal for i
              apply(cases "i = vid1")
              prefer 2 subgoal by auto
              apply auto              
              using has_derivative_proj[OF sol_deriv_eq[of s], of vid1] using  yup maybe[of s] almost almost'[of s] 
              by fastforce
            done 
          done
        have derEq:"\<And>s. (\<lambda>xa. (\<chi> i. xa *\<^sub>R (if i = vid1 then sterm_sem I (f1 fid1 vid1) (\<chi> i. if i = vid1 then sol s $ vid1 else 0) else 0)))
   = (\<lambda>xa. xa *\<^sub>R (\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) (\<chi> i. if i = vid1 then sol s $ vid1 else 0) else 0))"
          subgoal for s apply (rule ext, rule vec_extensionality) by auto done
        have "\<And>x. x \<in> {0..t} \<Longrightarrow>
       ((\<lambda>t. \<chi> i. if i = vid1 then sol t $ vid1 else 0) has_derivative
        (\<lambda>xa. xa *\<^sub>R (\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) (\<chi> i. if i = vid1 then sol x $ vid1 else 0) else 0)))
        (at x within {0..t})" subgoal for s using deriv'[of s] derEq[of s] by auto done
        then have deriv:"((\<lambda>t. \<chi> i. if i = vid1 then sol t $ vid1 else 0) has_vderiv_on
          (\<lambda>t. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) (\<chi> i. if i = vid1 then sol t $ vid1 else 0) else 0))
          {0..t}"
          unfolding has_vderiv_on_def has_vector_derivative_def
          by auto 
        have pre2:"(?sol solves_ode (\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0)) {0..t}
       {x. Predicates I vid1
            (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                   (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) x))}"
          apply(rule solves_odeI)
          subgoal by (rule deriv)
          subgoal for s using constraint by auto
          done
        have pre3:"VSagree (?sol 0) a {u. u = vid1 \<or> (\<exists>x. Inl u \<in> FVT (if x = vid1 then trm.Var vid1 else Const 0))}"
          using vne12 VSag unfolding VSagree_def by simp 
        have bigPre:"(\<exists>sol t. ?aaba' = mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then Var vid1 else Const 0))) (a, b) (sol t) \<and>
                        0 \<le> t \<and>
                        (sol solves_ode (\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0)) {0..t}
                         {x. Predicates I vid1
                              (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                                     (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then Var vid1 else Const 0))) (a, b) x))} \<and>
                        VSagree (sol 0) a {u. u = vid1 \<or> (\<exists>x. Inl u \<in> FVT (if x = vid1 then Var vid1 else Const 0))})"
          apply(rule exI[where x="?sol"])
          apply(rule exI[where x=t])
          apply(rule conjI)
          apply(rule pre1)
          apply(rule conjI)
          apply(rule t)
          apply(rule conjI)
          apply(rule pre2)
          by(rule pre3)
        have pred2:"Predicates I vid2 (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) ?aaba')"
          using bigEx bigPre by auto
        then have pred2':"?aaba' \<in> fml_sem I (p1 vid2 vid1)" unfolding p1_def expand_singleton by auto
        let ?res_state = "(mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                      (OSing vid2
                        (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                          ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
              (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b) (sol t))"
        have aabaX:"(fst ?aaba') $ vid1 = sol t $ vid1" 
          using aaba mk_v_agree[of "I" "(OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))"
   "(a, b)" "(?sol t)"] 
        proof -
          assume " Vagree (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (?sol t)) (a, b)
     (- semBV I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))) \<and>
    Vagree (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (?sol t))
     (mk_xode I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (?sol t))
     (semBV I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))))"
          then have ag:" Vagree (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (?sol t))
     (mk_xode I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (?sol t))
     (semBV I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))))"
            by auto
          have sembv:"(semBV I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))) = {Inl vid1, Inr vid1}"
            by auto
          have sub:"{Inl vid1} \<subseteq> {Inl vid1, Inr vid1}" by auto
          have ag':"Vagree (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (?sol t))
            (mk_xode I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (?sol t)) {Inl vid1}" 
            using ag agree_sub[OF sub] sembv by auto
          then have eq1:"fst (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (?sol t)) $ vid1 
            = fst (mk_xode I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (?sol t)) $ vid1" unfolding Vagree_def by auto
          moreover have "... = sol t $ vid1" by auto
          ultimately show ?thesis by auto
        qed
        have res_stateX:"(fst ?res_state) $ vid1 = sol t $ vid1" 
          using mk_v_agree[of I "(OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                      (OSing vid2
                        (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                          ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))"
              "(\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b)" "(sol t)"]
          proof -
            assume "Vagree (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                     (OSing vid2
                       (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                         ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
             (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b) (sol t))
     (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b)
     (- semBV I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                  (OSing vid2
                    (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                      ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))) \<and>
    Vagree (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                     (OSing vid2
                       (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                         ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
             (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b) (sol t))
     (mk_xode I
       (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
         (OSing vid2
           (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
             ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
       (sol t))
     (semBV I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                (OSing vid2
                  (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                    ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))))))"
            then have ag:" Vagree (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                     (OSing vid2
                       (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                         ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
             (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b) (sol t))
     (mk_xode I
       (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
         (OSing vid2
           (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
             ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
       (sol t))
     (semBV I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                (OSing vid2
                  (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                    ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))))))" by auto
            have sembv:"(semBV I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                (OSing vid2
                  (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                    ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))) = {Inl vid1, Inr vid1, Inl vid2, Inr vid2}" by auto
            have sub:"{Inl vid1} \<subseteq> {Inl vid1, Inr vid1, Inl vid2, Inr vid2}" by auto
            have ag':"Vagree (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                     (OSing vid2
                       (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                         ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
             (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b) (sol t))
     (mk_xode I
       (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
         (OSing vid2
           (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
             ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
       (sol t)) {Inl vid1}" using ag sembv agree_sub[OF sub] by auto
            then have "fst ?res_state $ vid1 = fst ((mk_xode I
       (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
         (OSing vid2
           (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
             ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
       (sol t))) $ vid1" unfolding Vagree_def by blast
        moreover have "... = sol t $ vid1" by auto
        ultimately show "?thesis" by linarith
        qed
       have agree:"Vagree ?aaba' (?res_state) (FVF (p1 vid2 vid1))"
         unfolding p1_def Vagree_def using aabaX res_stateX by auto
       have fml_sem_eq:"(?res_state \<in> fml_sem I (p1 vid2 vid1)) = (?aaba' \<in> fml_sem I (p1 vid2 vid1))"
           using coincidence_formula[OF p2safe Iagree_refl agree, of I] by auto
       then show "Predicates I vid2
     (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
            (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                      (OSing vid2
                        (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                          ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
              (\<chi> y. if vid2 = y then 0 else fst (a, b) $ y, b) (sol t)))"
        using pred2 unfolding p1_def expand_singleton by auto
    qed
  subgoal for I a b r aa ba sol t
    proof -
      assume good_interp:"is_interp I"
      assume bigAll:"\<forall>aa ba. (\<exists>sol t. (aa, ba) =
                        mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                                 (OSing vid2
                                   (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                                     ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
                         (\<chi> y. if vid2 = y then r else fst (a, b) $ y, b) (sol t) \<and>
                        0 \<le> t \<and>
                        (sol solves_ode
                         (\<lambda>a b. (\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0) +
                                (\<chi> i. if i = vid2 then sterm_sem I (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1)) b else 0)))
                         {0..t} {x. Predicates I vid1
                                     (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                                            (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                                                      (OSing vid2
                                                        (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                                                          ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
                                              (\<chi> y. if vid2 = y then r else fst (a, b) $ y, b) x))} \<and>
                        VSagree (sol 0) (\<chi> y. if vid2 = y then r else fst (a, b) $ y)
                         {y. y = vid2 \<or>
                               y = vid1 \<or> y = vid2 \<or> y = vid1 \<or> (\<exists>x. Inl y \<in> FVT (if x = vid1 then trm.Var vid1 else Const 0))}) \<longrightarrow>
               Predicates I vid2 (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) (aa, ba))"
        assume aaba:"(aa, ba) = mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (sol t)"
        assume t:"0 \<le> t"
        assume sol:"(sol solves_ode (\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0)) {0..t}
         {x. Predicates I vid1
              (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                     (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) x))}"
        assume VSA:"VSagree (sol 0) a {y. y = vid1 \<or> (\<exists>x. Inl y \<in> FVT (if x = vid1 then trm.Var vid1 else Const 0))}"
        (* Construct solution to ODE for y' here: *)
        let ?yode = "(\<lambda>t y. y * sterm_sem I (f1 fid2 vid1) (sol t) + sterm_sem I (f1 fid3 vid1) (sol t))"
        let ?ysol0 = r
        (* Time constraint: {0..t} because we need to know that the original solution is nice everywhere,
         * no evolution domain constraint because the constraint we eventually want doesn't mention y in the first place. *)
        (* Picard_Lindeloef_Qualitative.ll_on_open_it.flow_solves_ode:
          ll_on_open_it ?T ?f ?X \<Longrightarrow>
            ?t0.0 \<in> ?T \<Longrightarrow> ?x0.0 \<in> ?X \<Longrightarrow> 
            (ll_on_open.flow ?T ?f ?X ?t0.0 ?x0.0 solves_ode ?f) (ll_on_open.existence_ivl ?T ?f ?X ?t0.0 ?x0.0) ?X *)
(*        have ll:"local_lipschitz (ll_old.existence_ivl 0 (sol 0)) UNIV (\<lambda>t y. y * sterm_sem I (f1 fid2 vid1) (sol t) + sterm_sem I (f1 fid3 vid1) (sol t))"
          sorry*)
        let ?f2arg = "(\<lambda> x. (\<chi> i. sterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) x))"
        have f2_deriv:"\<And>s. ((\<lambda>s. Functions I fid2 (?f2arg  s)) has_derivative (FunctionFrechet I fid2 (?f2arg (sol s)))) (at (sol s) within (sol ` {0..t}))"
          using good_interp unfolding is_interp_def
          sorry
        let ?xode = "(\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0)"
        let ?xconstraint = UNIV
        let ?ivl = "ll_on_open.existence_ivl {0 .. t} ?xode ?xconstraint 0 (sol 0)"
        (* (\<And>t x. t \<in> ?T \<Longrightarrow> x \<in> ?X \<Longrightarrow> (?f t has_derivative blinfun_apply (?f' (t, x))) (at x)) \<Longrightarrow>
    continuous_on (?T \<times> ?X) ?f' \<Longrightarrow> open ?T \<Longrightarrow> open ?X \<Longrightarrow> local_lipschitz ?T ?X ?f*)
        have old_lipschitz:"local_lipschitz UNIV UNIV (\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0)"
          sorry
        have old_continuous:" \<And>x. x \<in> UNIV \<Longrightarrow> continuous_on UNIV (\<lambda>t. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) x else 0)"
            by(rule continuous_on_const)
        interpret ll_old: ll_on_open_it "UNIV" ?xode ?xconstraint 0 
          apply(standard)
          subgoal by auto
          prefer 3 subgoal by auto
          prefer 3 subgoal by auto
          apply(rule old_lipschitz)
          by (rule old_continuous)
        have sol_old:"(ll_old.flow 0 (sol 0) solves_ode ?xode) (ll_old.existence_ivl 0 (sol 0)) UNIV"
          by(rule ll_old.flow_solves_ode, auto)
        have con1:"\<And>x. continuous_on {0..t} (\<lambda>x. Functions I fid2 (\<chi> i. sterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) (sol x)))"
          sorry
        have con2:"\<And>x. continuous_on {0..t} (\<lambda>x. Functions I fid3 (\<chi> i. sterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) (sol x)))"
          sorry
        have con:"\<And>x. continuous_on (ll_old.existence_ivl 0 (sol 0)) (\<lambda>t. x * sterm_sem I (f1 fid2 vid1) (sol t) + sterm_sem I (f1 fid3 vid1) (sol t))"
          sorry
        have ll:"local_lipschitz (ll_old.existence_ivl 0 (sol 0)) UNIV (\<lambda>t y. y * sterm_sem I (f1 fid2 vid1) (sol t) + sterm_sem I (f1 fid3 vid1) (sol t))"
          sorry
          (*subgoal for x
          unfolding f1_def expand_singleton apply auto
          apply(rule continuous_on_add)
          apply(rule continuous_on_mult_left)
          apply(rule con1)
          by(rule con2)*)
          (* continuous_on_mult_left continuous_on_add*)
        let ?ivl = "ll_old.existence_ivl 0 (sol 0)"
        have tclosed:"{0..t} = {0--t}" using t sorry
        have "(sol  solves_ode (\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0)) {0..t} UNIV"
          apply(rule solves_ode_supset_range)
          apply(rule sol)
          by auto
        then have sol':"(sol  solves_ode (\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0)) {0--t} UNIV"
          using tclosed by auto
        (* solves_ode_supset_range *)
        have sub:"{0--t} \<subseteq> ll_old.existence_ivl 0 (sol 0)"
          apply(rule ll_old.closed_segment_subset_existence_ivl)
          apply(rule ll_old.existence_ivl_maximal_segment)
          apply(rule sol')
          apply(rule refl)
          by auto
        interpret ll_new: ll_on_open_it "?ivl" "?yode" "UNIV" 0
          apply(standard)
          apply(auto)
          apply(rule ll)
          by(rule con)
          (*unfolding local_lipschitz_def f0_def empty_def sterm_sem.simps apply(safe)
          using gt_ex lipschitz_constI apply blast*)
        (*by (simp add: continuous_on_const)*)
        have sol_new:"(ll_new.flow 0 r solves_ode ?yode) (ll_new.existence_ivl 0 r) UNIV"
          by(rule ll_new.flow_solves_ode, auto)
        have more_lipschitz:"\<And>tm tM. tm \<in> ll_old.existence_ivl 0 (sol 0) \<Longrightarrow>
             tM \<in> ll_old.existence_ivl 0 (sol 0) \<Longrightarrow>
             \<exists>M L. \<forall>t\<in>{tm..tM}. \<forall>x. \<bar>x * sterm_sem I (f1 fid2 vid1) (sol t) + sterm_sem I (f1 fid3 vid1) (sol t)\<bar> \<le> M + L * \<bar>x\<bar>"
          sorry
        have ivls_eq:"(ll_new.existence_ivl 0 r) = (ll_old.existence_ivl 0 (sol 0))"
          apply(rule ll_new.existence_ivl_eq_domain)
          apply auto
          apply (rule more_lipschitz)
          by auto
        have sub':"{0--t} \<subseteq> ll_new.existence_ivl 0 r"
          using sub ivls_eq by auto
        have sol_new':"(ll_new.flow 0 r solves_ode ?yode) {0--t} UNIV"
          by(rule solves_ode_subset, rule sol_new, rule sub')
        (* TODO: ?sol' needs to be sol except with the solution for y added. *)
        let ?sol' = sol 
        let ?aaba' = "mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                                 (OSing vid2
                                   (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                                     ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))))) 
                             (\<chi> y. if vid2 = y then r else fst (a, b) $ y, b) 
                             (?sol' t)"
        have bigEx:"(\<exists>sol t. (fst ?aaba', snd ?aaba') =
                        mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                                 (OSing vid2
                                   (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                                     ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
                         ((\<chi> y. if vid2 = y then r else fst (a,b) $ y), b) (sol t) \<and>
                        0 \<le> t \<and>
                        (sol solves_ode
                         (\<lambda>a b. (\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0) +
                                (\<chi> i. if i = vid2 then sterm_sem I (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1)) b else 0)))
                         {0..t} {x. Predicates I vid1
                                     (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                                            (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                                                      (OSing vid2
                                                        (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                                                          ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
                                              ((\<chi> y. if vid2 = y then r else (fst (a,b)) $ y), b) x))} \<and>
                        VSagree (sol 0) (\<chi> y. if vid2 = y then r else fst (a,b) $ y)
                         {y. y = vid2 \<or>
                               y = vid1 \<or> y = vid2 \<or> y = vid1 \<or> (\<exists>x. Inl y \<in> FVT (if x = vid1 then trm.Var vid1 else Const 0))}) \<longrightarrow>
               Predicates I vid2 (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) ?aaba')"
            using bigAll apply simp 
            apply(erule allE[where x = "fst (?aaba')"])
            apply(erule allE[where x = "snd (?aaba')"])
            by auto
         have sol':"(?sol' solves_ode
     (\<lambda>a b. (\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0) +
            (\<chi> i. if i = vid2 then sterm_sem I (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1)) b else 0)))
     {0..t} {x. Predicates I vid1
                 (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                        (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                                  (OSing vid2
                                    (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                                      ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
                          (\<chi> y. if vid2 = y then r else fst (a, b) $ y, b) x))}"
           sorry
         have set_eq:"{y. y = vid2 \<or> y = vid1 \<or> y = vid2 \<or> y = vid1 \<or> (\<exists>x. Inl y \<in> FVT (if x = vid1 then trm.Var vid1 else Const 0))} = {vid1, vid2}"
           by auto
         (* Needs correct definition of ?sol' *)
         have "VSagree (?sol' 0) (\<chi> y. if vid2 = y then r else fst (a, b) $ y) {vid1, vid2}"
           using VSA unfolding VSagree_def apply simp 
           sorry
         then have VSA':" VSagree (?sol' 0) (\<chi> y. if vid2 = y then r else fst (a, b) $ y)
           
     {y. y = vid2 \<or> y = vid1 \<or> y = vid2 \<or> y = vid1 \<or> (\<exists>x. Inl y \<in> FVT (if x = vid1 then trm.Var vid1 else Const 0))} "
           by (auto simp add: set_eq)
           have bigPre:"(\<exists>sol t. (fst ?aaba', snd ?aaba') =
                        mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                                 (OSing vid2
                                   (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                                     ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
                         ((\<chi> y. if vid2 = y then r else fst (a,b) $ y), b) (sol t) \<and>
                        0 \<le> t \<and>
                        (sol solves_ode
                         (\<lambda>a b. (\<chi> i. if i = vid1 then sterm_sem I (f1 fid1 vid1) b else 0) +
                                (\<chi> i. if i = vid2 then sterm_sem I (Plus (Times (f1 fid2 vid1) (trm.Var vid2)) (f1 fid3 vid1)) b else 0)))
                         {0..t} {x. Predicates I vid1
                                     (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                                            (mk_v I (OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                                                      (OSing vid2
                                                        (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                                                          ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))
                                              ((\<chi> y. if vid2 = y then r else (fst (a,b)) $ y), b) x))} \<and>
                        VSagree (sol 0) (\<chi> y. if vid2 = y then r else fst (a,b) $ y)
                         {y. y = vid2 \<or>
                               y = vid1 \<or> y = vid2 \<or> y = vid1 \<or> (\<exists>x. Inl y \<in> FVT (if x = vid1 then trm.Var vid1 else Const 0))})"
           apply(rule exI[where x="?sol'"])
           apply(rule exI[where x=t])
           apply(rule conjI)
           subgoal by simp
           apply(rule conjI)
           subgoal by (rule t)
           apply(rule conjI)
           apply(rule sol')
           by(rule VSA')
         have pred_sem:"Predicates I vid2 (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) ?aaba')"
           using bigPre bigEx by auto
         let ?other_state = "(mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (sol t))"
         have agree:"Vagree (?aaba') (?other_state) {Inl vid1} "
           using mk_v_agree [of "I" "(OProd (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))
                     (OSing vid2
                       (Plus (Times ($f fid2 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)) (trm.Var vid2))
                         ($f fid3 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))))"
             "(\<chi> y. if vid2 = y then r else fst (a, b) $ y, b)" "(sol t)"]
           using mk_v_agree [of "I" "(OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0)))" "(a, b)" "(sol t)"]
           unfolding Vagree_def by auto
         have sub:"\<And>i. FVT (if i = vid1 then trm.Var vid1 else Const 0) \<subseteq> {Inl vid1}"
           by auto
         have agree':"\<And>i. Vagree (?aaba') (?other_state) (FVT (if i = vid1 then trm.Var vid1 else Const 0)) "
           subgoal for i using agree_sub[OF sub[of i] agree] by auto done
         have silly_safe:"\<And>i. dsafe (if i = vid1 then trm.Var vid1 else Const 0)"
           subgoal for i
             apply(cases "i = vid1")
             by (auto simp add: dsafe_Var dsafe_Const)
           done
         have dsem_eq:"(\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) ?aaba')  = 
            (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0) ?other_state)"
           apply(rule vec_extensionality)
           subgoal for i
             using coincidence_dterm[OF silly_safe[of i] agree'[of i], of I] by auto
           done         
       show"
       Predicates I vid2
        (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
               (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. if i = vid1 then trm.Var vid1 else Const 0))) (a, b) (sol t)))"
         using pred_sem dsem_eq by auto
qed
done
qed

end end

