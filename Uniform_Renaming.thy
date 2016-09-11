theory "Uniform_Renaming" 
imports
  Complex_Main
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
  "./Ids"
  "./Lib"
  "./Syntax"
  "./Denotational_Semantics"
  "./Frechet_Correctness"
  "./Static_Semantics"
  "./Coincidence"
  "./Bound_Effect"
begin context ids begin
fun swap ::"'sz \<Rightarrow> 'sz \<Rightarrow> 'sz \<Rightarrow> 'sz"
where "swap x y z = (if z = x then  y else if z = y then x else z)"
  
primrec TUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> ('sf, 'sz) trm"
where 
  "TUrename x y (Var z) = Var (swap x y z)"
| "TUrename x y (DiffVar z) = DiffVar (swap x y z)"
| "TUrename x y (Const r) = (Const r)"
| "TUrename x y (Function f args) = Function f (\<lambda>i. TUrename x y (args i))"
| "TUrename x y (Plus \<theta>1 \<theta>2) = Plus (TUrename x y \<theta>1) (TUrename x y \<theta>2)"
| "TUrename x y (Times \<theta>1 \<theta>2) = Times (TUrename x y \<theta>1) (TUrename x y \<theta>2)"
| "TUrename x y (Differential \<theta>) = Differential (TUrename x y \<theta>)"
  
primrec OUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sz) ODE \<Rightarrow> ('sf, 'sz) ODE"
where
  "OUrename x y (OVar c) = undefined"
| "OUrename x y (OSing z \<theta>) = OSing (swap x y z) (TUrename x y \<theta>)"
| "OUrename x y (OProd ODE1 ODE2) = OProd (OUrename x y ODE1) (OUrename x y ODE2)"
  
inductive ORadmit :: "('sf, 'sz) ODE \<Rightarrow> bool"
where
  ORadmit_Sing:"ORadmit (OSing x \<theta>)"
| ORadmit_Prod:"ORadmit ODE1 \<Longrightarrow> ORadmit ODE2 \<Longrightarrow> ORadmit (OProd ODE1 ODE2)"
  
primrec PUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sc, 'sz) hp \<Rightarrow> ('sf, 'sc, 'sz) hp"
and FUrename :: "'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sc, 'sz) formula \<Rightarrow> ('sf, 'sc, 'sz) formula"
where
  "PUrename x y (Pvar a) = undefined"
| "PUrename x y (Assign z \<theta>) = Assign (swap x y z) (TUrename x y \<theta>)"
| "PUrename x y (DiffAssign z \<theta>) = DiffAssign (swap x y z) (TUrename x y \<theta>)"
| "PUrename x y (Test \<phi>) = Test (FUrename x y \<phi>)"
| "PUrename x y (EvolveODE ODE \<phi>) = EvolveODE (OUrename x y ODE) (FUrename x y \<phi>)"
| "PUrename x y (Choice a b) = Choice (PUrename x y a) (PUrename x y b)"
| "PUrename x y (Sequence a b) = Sequence (PUrename x y a) (PUrename x y b)"
| "PUrename x y (Loop a) = Loop (PUrename x y a)"

| "FUrename x y (Geq \<theta>1 \<theta>2) = Geq (TUrename x y \<theta>1) (TUrename x y \<theta>2)"
| "FUrename x y (Prop p args) = Prop p (\<lambda>i. TUrename x y (args i))"
| "FUrename x y (Not \<phi>) = Not (FUrename x y \<phi>)"
| "FUrename x y (And \<phi> \<psi>) = And (FUrename x y \<phi>) (FUrename x y \<psi>)"
| "FUrename x y (Exists z \<phi>) = Exists (swap x y z) (FUrename x y \<phi>)"
| "FUrename x y (Diamond \<alpha> \<phi>) = Diamond (PUrename x y \<alpha>) (FUrename x y \<phi>)"
| "FUrename x y (DiffFormula \<phi>) = undefined"
| "FUrename x y (InContext C \<phi>) = undefined"

inductive PRadmit :: "('sf, 'sc, 'sz) hp \<Rightarrow> bool"
and FRadmit ::"('sf, 'sc, 'sz) formula \<Rightarrow> bool"
where
  PRadmit_Assign:"PRadmit (Assign x \<theta>)"
| PRadmit_DiffAssign:"PRadmit (DiffAssign x \<theta>)"
| PRadmit_Test:"FRadmit \<phi> \<Longrightarrow> PRadmit (Test \<phi>)"
| PRadmit_EvolveODE:"ORadmit ODE \<Longrightarrow> FRadmit \<phi> \<Longrightarrow> PRadmit (EvolveODE ODE \<phi>)"
| PRadmit_Choice:"PRadmit a \<Longrightarrow> PRadmit b \<Longrightarrow> PRadmit (Choice a b)"
| PRadmit_Sequence:"PRadmit a \<Longrightarrow> PRadmit b \<Longrightarrow> PRadmit (Sequence a b)"
| PRadmit_Loop:"PRadmit a \<Longrightarrow> PRadmit (Loop a)"

| FRadmit_Geq:"FRadmit (Geq \<theta>1 \<theta>2)"
| FRadmit_Prop:"FRadmit (Prop p args)"
| FRadmit_Not:"FRadmit \<phi> \<Longrightarrow> FRadmit (Not \<phi>)"
| FRadmit_And:"FRadmit \<phi> \<Longrightarrow> FRadmit \<psi> \<Longrightarrow> FRadmit (And \<phi> \<psi>)"
| FRadmit_Exists:"FRadmit \<phi> \<Longrightarrow> FRadmit (Exists x \<phi>)"
| FRadmit_Diamond:"PRadmit \<alpha> \<Longrightarrow> FRadmit \<phi> \<Longrightarrow> FRadmit (Diamond \<alpha> \<phi>)"

definition RSadj :: "'sz \<Rightarrow> 'sz \<Rightarrow> 'sz simple_state \<Rightarrow> 'sz simple_state"
where "RSadj x y \<nu> = (\<chi> z. \<nu> $ (swap x y z))" 

definition Radj :: "'sz \<Rightarrow> 'sz \<Rightarrow> 'sz state \<Rightarrow> 'sz state"
where "Radj x y \<nu> = (RSadj x y (fst \<nu>), RSadj x y (snd \<nu>))" 

lemma SUren: "sterm_sem I (TUrename x y \<theta>) \<nu> = sterm_sem I \<theta> (RSadj x y \<nu>)"
  by (induction \<theta>, auto simp add: RSadj_def)

lemma ren_preserves_dfree:"dfree \<theta> \<Longrightarrow> dfree (TUrename x y \<theta>)"
  by(induction rule: dfree.induct, auto intro: dfree.intros)

lemma TUren_frechet:
assumes good_interp:"is_interp I"
shows "dfree \<theta> \<Longrightarrow> frechet I (TUrename x y \<theta>) \<nu> \<nu>' = frechet I \<theta> (RSadj x y \<nu>) (RSadj x y \<nu>')"
proof (induction rule: dfree.induct)
  (* There's got to be a more elegant proof of this... *)
  case (dfree_Var i)
  then show ?case unfolding RSadj_def apply auto 
    subgoal by (metis vec_lambda_eta)
    subgoal
    proof -
      assume "y \<noteq> x"
      have f1: "\<And>v s. v $ (s::'sz) = v \<bullet> (\<chi> sa. if s = sa then 1 else 0)"
        by (metis basis_vector.simps inner_prod_eq)
      have "(\<chi> s. \<nu>' $ (if s = x then y else if s = y then x else s)) $ y = \<nu>' $ x"
        by simp
      then show "\<nu>' \<bullet> (\<chi> s. if x = s then 1 else 0) = (\<chi> s. \<nu>' $ (if s = x then y else if s = y then x else s)) \<bullet> (\<chi> s. if y = s then 1 else 0)"
        using f1 by force
    qed
    subgoal
    proof -
      have "\<And>v s. v \<bullet> (\<chi> sa. if (s::'sz) = sa then 1 else 0) = v $ s"
        by (metis basis_vector.simps inner_prod_eq)
      then show ?thesis
        by simp
    qed
    subgoal
      sledgehammer
    proof -
      assume a1: "i \<noteq> y"
      assume a2: "i \<noteq> x"
      have "\<And>v s. v \<bullet> (\<chi> sa. if (s::'sz) = sa then 1 else 0) = v $ s"
        by (metis (no_types) basis_vector.simps inner_prod_eq)
      then show ?thesis
        using a2 a1 by simp
    qed
    done 
qed (auto simp add: SUren good_interp is_interp_def)

lemma RSadj_fst:"RSadj x y (fst \<nu>) = fst (Radj x y \<nu>)"
  unfolding RSadj_def Radj_def by auto

lemma RSadj_snd:"RSadj x y (snd \<nu>) = snd (Radj x y \<nu>)"
  unfolding RSadj_def Radj_def by auto

lemma TUren:
assumes good_interp:"is_interp I"
shows "dsafe \<theta> \<Longrightarrow> dterm_sem I (TUrename x y \<theta>) \<nu> = dterm_sem I \<theta> (Radj x y \<nu>)"
proof (induction rule: dsafe.induct)
  case (dsafe_Diff \<theta>)
    assume free:"dfree \<theta>"
    show ?case 
      apply (auto simp add: directional_derivative_def)
      using TUren_frechet[OF good_interp free, of x y "fst \<nu>" "snd \<nu>"]
       by (auto simp add: RSadj_fst RSadj_snd)
qed (auto simp add: Radj_def RSadj_def)

lemma adj_sum:"RSadj x y (\<nu>1 + \<nu>2) = (RSadj x y \<nu>1) + (RSadj x y \<nu>2)"
  unfolding RSadj_def apply auto apply (rule vec_extensionality)
  subgoal for i
    apply (cases "i = x")
    apply (cases "i = y")
    by auto
  done

lemma OUren: "ORadmit ODE \<Longrightarrow> ODE_sem I (OUrename x y ODE) \<nu> = RSadj x y (ODE_sem I ODE (RSadj x y \<nu>))"
proof (induction rule: ORadmit.induct)
  case (ORadmit_Prod ODE1 ODE2)
  then show ?case 
    using adj_sum by auto
next
  case (ORadmit_Sing z \<theta>)
  then show ?case 
    by (rule vec_extensionality | auto simp add: SUren RSadj_def)+   
qed

lemma state_eq: 
  fixes \<nu> \<nu>' :: "'sz state"
  shows "(\<And>i. (fst \<nu>) $ i = (fst \<nu>') $ i) \<Longrightarrow> (\<And>i. (snd \<nu>) $ i = (snd \<nu>') $ i) \<Longrightarrow> \<nu>  = \<nu>'"
  apply (cases "\<nu>", cases "\<nu>'", auto)
  by(rule vec_extensionality, auto)+
  
lemma Radj_repv1:
 fixes x y z ::"'sz" 
 shows "(Radj x y (repv \<nu> y r)) = repv (Radj x y \<nu>) x r"
  apply(rule state_eq)
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
    unfolding Radj_def RSadj_def by auto
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
    unfolding Radj_def RSadj_def by auto
  done

lemma Radj_repv2:
 fixes x y z ::"'sz" 
 shows "(Radj x y (repv \<nu> x r)) = repv (Radj x y \<nu>) y r"
  apply(rule state_eq)
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
    unfolding Radj_def RSadj_def by auto
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
    unfolding Radj_def RSadj_def by auto
  done

lemma Radj_repv3:
 fixes x y z ::"'sz" 
 assumes zx:"z \<noteq> x" and zy:"z \<noteq> y"
 shows "(Radj x y (repv \<nu> z r)) = repv (Radj x y \<nu>) z r"
  apply(rule state_eq)
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
    using zx zy unfolding Radj_def RSadj_def by auto
  subgoal for i
    apply(cases "i = x") apply (cases "i = y") 
    using zx zy unfolding Radj_def RSadj_def by auto
  done

(* i.e. shows Radj x y is a bijection for all x y *)
lemma Radj_eq_iff:"(a = b) = ((Radj x y a) = (Radj x y b))"
  unfolding Radj_def RSadj_def apply auto
  apply (rule state_eq)
  subgoal for i by(cases "i = x", cases "i = y", auto, (smt vec_lambda_beta)+)
  subgoal for i by(cases "i = x", cases "i = y", auto, (smt vec_lambda_beta)+)
  done
    
lemma PUren_FUren:
assumes good_interp:"is_interp I"
shows
  "(PRadmit \<alpha> \<longrightarrow> hpsafe \<alpha> \<longrightarrow> (\<forall> \<nu> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I (PUrename x y \<alpha>) \<longleftrightarrow> (Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I \<alpha>))
  \<and> (FRadmit \<phi> \<longrightarrow> fsafe \<phi> \<longrightarrow> (\<forall> \<nu>. \<nu> \<in> fml_sem I (FUrename x y \<phi>) \<longleftrightarrow> (Radj x y \<nu>) \<in> fml_sem I \<phi>))"
proof(induction rule: PRadmit_FRadmit.induct)
  case (FRadmit_Geq \<theta>1 \<theta>2)
  then show ?case using TUren[OF good_interp] by auto
next
  case (FRadmit_Exists \<phi> z) then have
    FRA:"FRadmit \<phi>"
    and IH:"fsafe \<phi> \<Longrightarrow>  (\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
    by auto
  have "fsafe (Exists z \<phi>) \<Longrightarrow>  (\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>)))"
    apply (cases "z = x")
    subgoal for \<nu>
      proof -
        assume fsafe:"fsafe (Exists z \<phi>)"
        assume zx:"z = x"
        from fsafe have fsafe':"fsafe \<phi>" by auto
        have IH':"(\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
          by (rule IH[OF fsafe'])
        have "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (\<nu> \<in> fml_sem I (Exists y (FUrename x y \<phi>)))" using zx by auto
        moreover have "... = (\<exists>r. (repv \<nu> y r) \<in> fml_sem I (FUrename x y \<phi>))" by auto
        moreover have "... = (\<exists>r. (Radj x y (repv \<nu> y r)) \<in> fml_sem I \<phi>)" using IH' by auto
        moreover have "... = (\<exists>r. (repv (Radj x y \<nu>) x r) \<in> fml_sem I \<phi>)" using Radj_repv1[of x y \<nu>] by auto
        moreover have "... = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))" using zx by auto
        ultimately 
        show "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))"
          by auto
      qed
    apply (cases "z = y")
    subgoal for \<nu>
    proof -
      assume fsafe:"fsafe (Exists z \<phi>)"
      assume zx:"z = y"
      from fsafe have fsafe':"fsafe \<phi>" by auto
      have IH':"(\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
        by (rule IH[OF fsafe'])
      have "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (\<nu> \<in> fml_sem I (Exists x (FUrename x y \<phi>)))" using zx by auto
      moreover have "... = (\<exists>r. (repv \<nu> x r) \<in> fml_sem I (FUrename x y \<phi>))" by auto
      moreover have "... = (\<exists>r. (Radj x y (repv \<nu> x r)) \<in> fml_sem I \<phi>)" using IH' by auto
      moreover have "... = (\<exists>r. (repv (Radj x y \<nu>) y r) \<in> fml_sem I \<phi>)" using Radj_repv2[of x y \<nu>] by auto
      moreover have "... = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))" using zx by auto
      ultimately 
      show "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))"
        by auto
    qed
    subgoal for \<nu>
    proof -
      assume fsafe:"fsafe (Exists z \<phi>)"
      assume zx:"z \<noteq> x" and zy:"z \<noteq> y"
      from fsafe have fsafe':"fsafe \<phi>" by auto
      have IH':"(\<And>\<nu>. (\<nu> \<in> fml_sem I (FUrename x y \<phi>)) = (Radj x y \<nu> \<in> fml_sem I \<phi>))"
        by (rule IH[OF fsafe'])
      have "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (\<nu> \<in> fml_sem I (Exists z (FUrename x y \<phi>)))" using zx zy by auto
      moreover have "... = (\<exists>r. (repv \<nu> z r) \<in> fml_sem I (FUrename x y \<phi>))" by auto
      moreover have "... = (\<exists>r. (Radj x y (repv \<nu> z r)) \<in> fml_sem I \<phi>)" using IH' by auto
      moreover have "... = (\<exists>r. (repv (Radj x y \<nu>) z r) \<in> fml_sem I \<phi>)" using Radj_repv3[of z x y \<nu>, OF zx zy] by auto
      moreover have "... = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))" using zx by auto
      ultimately 
      show "(\<nu> \<in> fml_sem I (FUrename x y (Exists z \<phi>))) = (Radj x y \<nu> \<in> fml_sem I (Exists z \<phi>))"
        by auto
    qed
    done
  then show ?case by auto 
next
  case (PRadmit_Assign z \<theta>)
  have "hpsafe (Assign z \<theta>) \<Longrightarrow>  (\<And>\<nu> \<omega>. ((\<nu>, \<omega>)  \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem I (Assign z \<theta>)))"
    apply (cases "z = x")
    subgoal for \<nu> \<omega>
      proof -
        assume fsafe:"hpsafe (Assign z \<theta>)"
        assume zx:"z = x"
        from fsafe have dsafe:"dsafe \<theta>" by auto
        have IH':"(\<And>\<nu>. dterm_sem I (TUrename x y \<theta>) \<nu> = dterm_sem I \<theta> (Radj x y \<nu>))"
          subgoal for \<nu> using TUren[OF good_interp dsafe , of x y \<nu>] by auto done
        have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((\<nu>, \<omega>) \<in> prog_sem I (Assign y (TUrename x y \<theta>)))"  using zx by auto
        moreover have "... = (\<omega> = repv \<nu> y (dterm_sem I (TUrename x y \<theta>) \<nu>))" by auto
        moreover have "... = (\<omega> = repv \<nu> y (dterm_sem I \<theta> (Radj x y \<nu>)))" using IH' by auto
        moreover have "... = (Radj x y \<omega> = Radj x y (repv \<nu> y (dterm_sem I \<theta> (Radj x y \<nu>))))" using Radj_eq_iff by auto
        moreover have "... = (Radj x y \<omega> = repv (Radj x y \<nu>) x (dterm_sem I \<theta> (Radj x y \<nu>)))" using Radj_repv1 by auto
        moreover have "... = (Radj x y \<omega> = repv (Radj x y \<nu>) z (dterm_sem I \<theta> (Radj x y \<nu>)))" using zx by auto
        moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))" by auto        
        ultimately 
        show "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))"
          by auto
      qed
    apply (cases "z = y")
    subgoal for \<nu> \<omega>
      proof -
        assume fsafe:"hpsafe (Assign z \<theta>)"
        assume zy:"z = y"
        from fsafe have dsafe:"dsafe \<theta>" by auto
        have IH':"(\<And>\<nu>. dterm_sem I (TUrename x y \<theta>) \<nu> = dterm_sem I \<theta> (Radj x y \<nu>))"
          subgoal for \<nu> using TUren[OF good_interp dsafe , of x y \<nu>] by auto done
        have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((\<nu>, \<omega>) \<in> prog_sem I (Assign x (TUrename x y \<theta>)))"  using zy by auto
        moreover have "... = (\<omega> = repv \<nu> x (dterm_sem I (TUrename x y \<theta>) \<nu>))" by auto
        moreover have "... = (\<omega> = repv \<nu> x (dterm_sem I \<theta> (Radj x y \<nu>)))" using IH' by auto
        moreover have "... = (Radj x y \<omega> = Radj x y (repv \<nu> x (dterm_sem I \<theta> (Radj x y \<nu>))))" using Radj_eq_iff by auto
        moreover have "... = (Radj x y \<omega> = repv (Radj x y \<nu>) y (dterm_sem I \<theta> (Radj x y \<nu>)))" using Radj_repv2 by auto
        moreover have "... = (Radj x y \<omega> = repv (Radj x y \<nu>) z (dterm_sem I \<theta> (Radj x y \<nu>)))" using zy by auto
        moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))" by auto        
        ultimately 
        show "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))"
          by auto
      qed
    subgoal for \<nu> \<omega>
      proof -
        assume fsafe:"hpsafe (Assign z \<theta>)"
        assume zx:"z \<noteq> x" and zy:"z \<noteq> y"
        from fsafe have dsafe:"dsafe \<theta>" by auto
        have IH':"(\<And>\<nu>. dterm_sem I (TUrename x y \<theta>) \<nu> = dterm_sem I \<theta> (Radj x y \<nu>))"
          subgoal for \<nu> using TUren[OF good_interp dsafe , of x y \<nu>] by auto done
        have "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((\<nu>, \<omega>) \<in> prog_sem I (Assign z (TUrename x y \<theta>)))"  using zx zy by auto
        moreover have "... = (\<omega> = repv \<nu> z (dterm_sem I (TUrename x y \<theta>) \<nu>))" by auto
        moreover have "... = (\<omega> = repv \<nu> z (dterm_sem I \<theta> (Radj x y \<nu>)))" using IH' by auto
        moreover have "... = (Radj x y \<omega> = Radj x y (repv \<nu> z (dterm_sem I \<theta> (Radj x y \<nu>))))" using Radj_eq_iff by auto
        moreover have "... = (Radj x y \<omega> = repv (Radj x y \<nu>) z (dterm_sem I \<theta> (Radj x y \<nu>)))" using Radj_repv3[OF zx zy] by auto
        moreover have "... = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))" by auto        
        ultimately 
        show "((\<nu>, \<omega>) \<in> prog_sem I (PUrename x y (Assign z \<theta>))) = ((Radj x y \<nu>, Radj x y \<omega>) \<in> prog_sem  I (Assign z \<theta>))"
          by auto
      qed
      done
  then show ?case 
    (* \<omega> = repd \<nu> x (dterm_sem I t \<nu>) *) 
    unfolding Radj_def 
    
    sorry
next
  case (PRadmit_DiffAssign x \<theta>)
  then show ?case sorry
next
  case (PRadmit_Test \<phi>)
  then show ?case unfolding Radj_def 
    apply simp
    apply(rule allI)+
    subgoal for a b aa ba
      apply auto
      apply(rule vec_extensionality)
      subgoal for i
         apply(cases "i = x")
         apply(cases "i = y")
         apply(smt Cart_lambda_cong vec_lambda_eta)
        sorry
      sorry
    done
next
  case (PRadmit_Sequence a b)
  then show ?case sorry
next
  case (PRadmit_Loop a)
  then show ?case sorry
next
  case (FRadmit_Prop p args)
  then show ?case sorry
next
  case (FRadmit_Diamond \<alpha> \<phi>)
  then show ?case sorry
next
  case (PRadmit_EvolveODE ODE \<phi>)
  then show ?case sorry
qed (auto simp add: Radj_def)
  
end end
