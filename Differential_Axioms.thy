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

subsection \<open>Differentiation Axioms\<close>
definition diff_const_axiom :: "('sf, 'sc, 'sz) formula"
  where "diff_const_axiom \<equiv> Equals (Differential ($f fid1 sempty)) (Const 0)"

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

definition DIaxiom :: "('sf, 'sc, 'sz) formula"
  where "DIaxiom = (((Predicational pid1) \<rightarrow> (And (Predicational pid2) ([[EvolveODE (OVar vid1) (Predicational pid1)]](DiffFormula (Predicational pid2))))) 
\<rightarrow> ([[EvolveODE (OVar vid1) (Predicational pid1)]]Predicational pid2))"

definition DGaxiom :: "('sf, 'sc, 'sz) formula"
  where "DGaxiom = (([[EvolveODE (OVar vid1) (Predicational pid1)]]Predicational pid2) \<leftrightarrow> 
  (Exists vid2 
    ([[EvolveODE (OProd (OVar vid1) (OSing vid2 (Plus (Times (Function fid1 empty) (Var vid2)) (Function fid2 empty)))) (Predicational pid1)]]
       Predicational pid2)))"

subsection \<open>Proofs for Differentiation Axioms\<close>
lemma constant_deriv_inner:
 assumes interp:"\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x)"
 shows "FunctionFrechet I id1 (vec_lambda (\<lambda>i. sterm_sem I (sempty i) (fst \<nu>))) (vec_lambda(\<lambda>i. frechet I (sempty i) (fst \<nu>) (snd \<nu>)))= 0"
  proof -
    have empty_zero:"(vec_lambda(\<lambda>i. frechet I (sempty i) (fst \<nu>) (snd \<nu>))) = 0"
    using sempty_def Cart_lambda_cong frechet.simps(5) zero_vec_def
    by fastforce
    let ?x = "(vec_lambda (\<lambda>i. sterm_sem I (sempty i) (fst \<nu>)))"
    from interp
    have has_deriv:"(Functions I id1 has_derivative FunctionFrechet I id1 ?x) (at ?x)"
    by auto
    then have f_linear:"linear (FunctionFrechet I id1 ?x)"
    using Deriv.has_derivative_linear by auto
    then
    show ?thesis using empty_zero f_linear Linear_Algebra.linear_0 by (auto)
  qed

lemma constant_deriv_zero:"is_interp I \<Longrightarrow> directional_derivative I ($f id1 sempty) \<nu> = 0"
  apply(simp only: is_interp_def directional_derivative_def frechet.simps frechet_correctness)
  apply(rule constant_deriv_inner)
  apply(auto)
done

theorem diff_const_axiom_valid: "valid diff_const_axiom"
  apply(simp only: valid_def diff_const_axiom_def equals_sem)
  apply(rule allI | rule impI)+
  apply(simp only: dterm_sem.simps constant_deriv_zero sterm_sem.simps)
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
"repd (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) vid1 (dterm_sem I (f1 fid1 vid1) (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)))
 = mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)"
proof
  have agree:"Vagree (mk_v I (OSing vid1 (f1 fid1 vid1)) (ab, bb) (sol t)) (mk_xode I (OSing vid1 (f1 fid1 vid1)) (sol t))
      {Inl vid1, Inr vid1}" 
    using mk_v_agree[of I "(OSing vid1 (f1 fid1 vid1))" "(ab, bb)" "(sol t)"] by auto
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
      by (metis (no_types, lifting) dsafe dsafe_Fun_simps image_iff)
    show "valid DEaxiom"
    apply(auto simp only: DEaxiom_def valid_def Let_def iff_sem impl_sem)
    apply(auto simp only: fml_sem.simps prog_sem.simps mem_Collect_eq box_sem simp del: prog_sem.simps(8) simp add: ode_alt_sem[OF osafe fsafe])
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
  apply(auto simp only: fml_sem.simps prog_sem.simps DCaxiom_def valid_def iff_sem impl_sem box_sem)
  apply(auto)
  sorry

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
      using singleton.simps dsafe_Const by auto
    show "valid DSaxiom"
  apply(auto simp only: DSaxiom_def valid_def Let_def iff_sem impl_sem box_sem)
  apply(auto simp only: fml_sem.simps prog_sem.simps mem_Collect_eq  iff_sem impl_sem box_sem forall_sem
       simp del: prog_sem.simps(8) simp add: ode_alt_sem[OF osafe fsafe])
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
  agrees:"Vagree (mk_v I (OSing vid1 (f0 fid1)) (a, b) (?sol r)) (a, b) (- ODE_vars (OSing vid1 (f0 fid1))) 
  \<and> Vagree (mk_v I (OSing vid1 (f0 fid1)) (a, b) (?sol r))
   (mk_xode I (OSing vid1 (f0 fid1)) (?sol r)) (ODE_vars (OSing vid1 (f0 fid1)))" 
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
    subgoal by (standard, auto intro: hpsafe_fsafe.intros dsafe.intros)
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
    defer
    subgoal using eq_UNIV apply auto
      subgoal using sol sol0_eq by auto
    done
    using sol'' closed_segment_eq_real_ivl t apply(auto)
    by (simp add: solves_ode_singleton)
  let ?c = "Functions I fid1 (\<chi> _. 0)"
  let ?sol = "(\<lambda>t. \<chi> i. if i = vid1 then (ab $ i) + ?c * t else (ab $ i))"
  have vec_simp:"(\<lambda>a b. \<chi> i. if i = vid1 then sterm_sem I ($f fid1 (\<lambda>i. Const 0)) b else 0) 
      = (\<lambda>a b. \<chi> i. if i = vid1 then Functions I fid1 (\<chi> i. 0) else 0)"
    by (auto simp add: vec_eq_iff cong: if_cong)
  have exp_sol:"(?sol solves_ode (\<lambda>_. ODE_sem I (OSing vid1 (f0 fid1)))) {0..t}
    UNIV"
            (*{x. mk_v I (OSing vid1 (f0 fid1)) (ab,bb) x \<in> fml_sem I (p1 vid2 vid1)}*) 
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
    apply(unfold exp_isFlow)
    apply(unfold isFlow)
    by (auto)
  then have sol_eq_exp_t:"?sol t = sol t"
    using t by auto
  then have sol_eq_exp_t':"sol t $ vid1 = ?sol t $ vid1" by auto
  then have useful:"?sol t $ vid1 = ab $ vid1 + Functions I fid1 (\<chi> i. 0) * t"
    by auto
  from sol_eq_exp_t' useful have useful':"sol t $ vid1 = ab $ vid1 + Functions I fid1 (\<chi> i. 0) * t"
    by auto
  have sol_int:"((ll.flow 0 (sol 0)) usolves_ode ?f from 0) {0..t} {x. mk_v I (OSing vid1 (f0 fid1)) (ab, bb) x \<in> fml_sem I (p1 vid2 vid1)}"
    (*(\<And>x f t0 T X Y. (x usolves_ode f from t0) T X \<Longrightarrow> x ` T \<subseteq> Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> (x usolves_ode f from t0) T Y) \<Longrightarrow>*)
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
      unfolding Vagree_def apply auto
      done
    done
  have thing':"\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow>  fst (mk_v I (OSing vid1 ($f fid1 (\<lambda>i. Const 0))) (ab, bb) (sol s)) $ vid1 = ab $ vid1 + Functions I fid1 (\<chi> i. 0) * s"
    subgoal for s using thing[of s] sol_eq_exp[of s] by auto done
  have another_eq:"\<And>i s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> dterm_sem I (if i = vid1 then trm.Var vid1 else Const 0)
                (mk_v I (OSing vid1 (f0 fid1)) (ab, bb) (sol s))

        =  dterm_sem I (if i = vid1 then Plus (trm.Var vid1) (Times (f0 fid1) (trm.Var vid3)) else Const 0)
                (\<chi> y. if vid3 = y then s else fst (\<chi> y. if vid2 = y then s else fst (ab, bb) $ y, bb) $ y, bb)"
    using mk_v_agree[of "I" "(OSing vid1 (f0 fid1))" "(ab, bb)" "(sol s)"]  vne12 vne23 vne13
    apply(auto simp add: f0_def p1_def empty_def)
    apply(unfold Vagree_def)
    apply(simp add: f0_def empty_def)
    (*using aaba apply(simp add: f0_def empty_def)*)
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
      using vne12 vne13 apply(auto)
      using mk_v_agree[of I "OSing vid1 ($f fid1 (\<lambda>i. Const 0))" "(ab,bb)" "(sol ra)"]
      apply(auto)
      apply(unfold Vagree_def)
      apply(safe)
      apply(erule allE[where x="vid1"])+
      apply(auto)
      using sol_eq_exp[of ra]
      apply(auto)
      using anotherFact[of ra] apply auto
      done
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
      using sol_eq_exp[of ra] apply auto
      apply (auto simp add: f0_def empty_def Vagree_def vec_eq_iff)
      using thing' apply auto
      done
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
    subgoal for i
      using vne12 apply(auto)
      using sol_eq_exp t thing by auto
    done  
  show "mk_v I (OSing vid1 (f0 fid1)) (ab, bb) (sol t) \<in> fml_sem I (p1 vid3 vid1)"
    using mk_v_agree[of I "OSing vid1 (f0 fid1)" "(ab, bb)" "sol t"] fml3[of t]
    unfolding f0_def p1_def empty_def
    unfolding Vagree_def apply auto
    apply(auto simp add:  sol_eq_exp_t' t vec_extensionality  vne12)
    using someEq by auto
qed qed

(* TODO:  differential formula semantics actually bogus right now
 * I believe the only correct semantics to give a DiffFormula(Predicational P)
 * is THE x. DI_is_valid_for (x). So the validity of this axiom will be a trivial
 * appeal to the validity of the interpretation. But then in substitution we will do the
 * real work by showing that adjoints are valid interpretations, so in adjoints all of the
 * DI_is_valid_for(x)'s actually exist.
*)
lemma DI_valid:"valid DIaxiom"
  apply(unfold DIaxiom_def valid_def impl_sem iff_sem)
  sorry

lemma DG_valid:"valid DGaxiom"
  apply(auto simp add: DGaxiom_def valid_def Let_def)
  sorry
end end
