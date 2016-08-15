theory "Axioms" 
imports
  Complex_Main HOL
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
  "./Ids"
  "./Lib"
  "./Syntax"
  "./Denotational_Semantics"
begin context ids begin

subsection \<open>Axioms\<close>
text \<open>
  The uniform substitution calculus is based on a finite list of concrete
  axioms, which are defined and proved sound in this section. When axioms apply
  to arbitrary programs or formulas, they mention concrete program or formula
  variables, which are then instantiated by uniform substitution, as opposed
  metavariables.
  
  This section cointains axioms and rules for propositional connectives and programs other than
  ODE's. Differential axioms are handled separately because the proofs are significantly more involved.
  \<close>

definition assign_axiom :: "('sf, 'sc, 'sz) formula"
  where "assign_axiom \<equiv>
    ([[vid1 := ($f fid1 empty)]] (Prop vid1 (singleton (Var vid1))))
      \<leftrightarrow> Prop vid1 (singleton ($f fid1 empty))"

definition loop_iterate_axiom :: "('sf, 'sc, 'sz) formula"
  where "loop_iterate_axiom \<equiv> ([[$\<alpha> vid1**]]Predicational pid1)
    \<leftrightarrow> ((Predicational pid1) && ([[$\<alpha> vid1]][[$\<alpha> vid1**]]Predicational pid1))"

definition test_axiom :: "('sf, 'sc, 'sz) formula"
  where "test_axiom \<equiv>
    ([[?($\<phi> vid2 empty)]]$\<phi> vid1 empty) \<leftrightarrow> (($\<phi> vid2 empty) \<rightarrow> ($\<phi> vid1 empty))"

definition box_axiom :: "('sf, 'sc, 'sz) formula"
  where "box_axiom \<equiv> (\<langle>$\<alpha> vid1\<rangle>Predicational pid1) \<leftrightarrow> !([[$\<alpha> vid1]]!(Predicational pid1))"

definition choice_axiom :: "('sf, 'sc, 'sz) formula"
  where "choice_axiom \<equiv> ([[$\<alpha> vid1 \<union>\<union> $\<alpha> vid2]]Predicational pid1)
    \<leftrightarrow> (([[$\<alpha> vid1]]Predicational pid1) && ([[$\<alpha> vid2]]Predicational pid1))"

definition Kaxiom :: "('sf, 'sc, 'sz) formula"
  where "Kaxiom \<equiv> ([[$\<alpha> vid1]]((Predicational pid1) \<rightarrow> (Predicational pid2)))
    \<rightarrow> ([[$\<alpha> vid1]]Predicational pid1) \<rightarrow> ([[$\<alpha> vid1]]Predicational pid2)"

(* Here is an example of an old version of the induction axiom that was too weak
 * and thus very easy to prove: it used predicates when it should have used predicationals.
 * This serves as a reminder to be careful whether other axioms are also too weak. *)
(* 
definition Ibroken :: "('sf, 'sc, 'sz) formula"
  where "Ibroken \<equiv> ([[$$a]]($P [] \<rightarrow> ([[$$a]]$P []))
    \<rightarrow> ($P [] \<rightarrow> ([[($$a)**]]$P [])))"*)

definition Iaxiom :: "('sf, 'sc, 'sz) formula"
  where "Iaxiom \<equiv> 
  ([[($\<alpha> vid1)**]](Predicational pid1 \<rightarrow> ([[$\<alpha> vid1]]Predicational pid1)))
    \<rightarrow>((Predicational pid1 \<rightarrow> ([[($\<alpha> vid1)**]]Predicational pid1)))"

definition Vaxiom :: "('sf, 'sc, 'sz) formula"
  where "Vaxiom \<equiv> ($\<phi> vid1 empty) \<rightarrow> ([[$\<alpha> vid1]]($\<phi> vid1 empty))"

subsection \<open>Validity/Soundness proofs for axioms and rules\<close>
theorem test_valid: "valid test_axiom"
  by (auto simp add: valid_def test_axiom_def)  

lemma assign_lem1:
"dterm_sem I (if i = vid1 then Var vid1 else (Const 0))
                   (vec_lambda (\<lambda>y. if vid1 = y then Functions I fid1
  (vec_lambda (\<lambda>i. dterm_sem I (empty i) \<nu>)) else  vec_nth (fst \<nu>) y), snd \<nu>)
=
 dterm_sem I (if i = vid1 then $f fid1 empty else (Const 0)) \<nu>
"
 by (cases "i = vid1") (auto simp: proj_sing1)

theorem assign_valid: "valid assign_axiom"
  unfolding  valid_def assign_axiom_def
  by (simp add: assign_lem1) 
  
lemma mem_to_nonempty: "\<omega> \<in> S \<Longrightarrow> (S \<noteq> {})"
  by (auto)

lemma loop_forward: "\<nu> \<in> fml_sem I ([[$\<alpha> id1**]]Predicational pid1)
  \<longrightarrow> \<nu> \<in> fml_sem I (Predicational pid1&&[[$\<alpha> id1]][[$\<alpha> id1**]]Predicational pid1)"
  by (cases \<nu>) (auto intro: converse_rtrancl_into_rtrancl simp add: box_sem)

lemma nat_case: "\<forall>n::nat. (n = 0) \<or> (\<exists>m. n = Suc m)"
  by (rule Nat.nat.nchotomy)

lemma loop_backward:
 "\<nu> \<in> fml_sem I (Predicational pid1 && [[$\<alpha> id1]][[$\<alpha> id1**]]Predicational pid1)
  \<longrightarrow> \<nu> \<in> fml_sem I ([[$\<alpha> id1**]]Predicational pid1)"
  by (auto elim: converse_rtranclE simp add: box_sem)

theorem loop_valid: "valid loop_iterate_axiom"
  apply(simp only: valid_def loop_iterate_axiom_def)
  apply(simp only: iff_sem)
  apply(simp only: HOL.iff_conv_conj_imp)
  apply(rule allI | rule impI)+
  apply(rule conjI)
  apply(rule loop_forward)
  apply(rule loop_backward)
done

theorem box_valid: "valid box_axiom"
  unfolding valid_def box_axiom_def by(auto)

theorem choice_valid: "valid choice_axiom"
  unfolding valid_def choice_axiom_def by (auto)

theorem K_valid: "valid Kaxiom"
  unfolding valid_def Kaxiom_def by (auto)

lemma I_axiom_lemma:
fixes I::"('sf,'sc,'sz) interp" and \<nu>
assumes "is_interp I"
assumes IS:"\<nu> \<in> fml_sem I ([[$\<alpha> vid1**]](Predicational pid1 \<rightarrow>
                          [[$\<alpha> vid1]]Predicational pid1))"
assumes BC:"\<nu> \<in> fml_sem I (Predicational pid1)"
shows "\<nu> \<in> fml_sem I ([[$\<alpha> vid1**]](Predicational pid1))"
proof -
  have IS':"\<And>\<nu>2. (\<nu>, \<nu>2) \<in> (prog_sem I ($\<alpha> vid1))\<^sup>* \<Longrightarrow> \<nu>2 \<in> fml_sem I (Predicational pid1 \<rightarrow> [[$\<alpha> vid1]](Predicational pid1))"
    using IS by (auto simp add: box_sem)
  have res:"\<And>\<nu>3. ((\<nu>, \<nu>3) \<in> (prog_sem I ($\<alpha> vid1))\<^sup>*) \<Longrightarrow> \<nu>3 \<in> fml_sem I (Predicational pid1)"
  proof -
    fix \<nu>3 
    show "((\<nu>, \<nu>3) \<in> (prog_sem I ($\<alpha> vid1))\<^sup>*) \<Longrightarrow> \<nu>3 \<in> fml_sem I (Predicational pid1)"
    apply(induction rule:rtrancl_induct)
    apply(rule BC)
    proof -
      fix y z
      assume vy:"(\<nu>, y) \<in> (prog_sem I ($\<alpha> vid1))\<^sup>*"
      assume yz:"(y, z) \<in> prog_sem I ($\<alpha> vid1)"
      assume yPP:"y \<in> fml_sem I (Predicational pid1)"
      have imp3:"y \<in> fml_sem I (Predicational pid1 \<rightarrow> [[$\<alpha> vid1 ]](Predicational pid1))"
        using IS' vy by (simp)
      have imp4:"y \<in> fml_sem I (Predicational pid1) \<Longrightarrow> y \<in> fml_sem I  ([[$\<alpha> vid1]](Predicational pid1))"
        using imp3 impl_sem by (auto)
      have yaPP:"y \<in> fml_sem I ([[$\<alpha> vid1]]Predicational pid1)" using imp4 yPP by auto
      have zPP:"z \<in> fml_sem I (Predicational pid1)" using yaPP box_sem yz mem_Collect_eq by blast  
      show "
        (\<nu>, y) \<in> (prog_sem I ($\<alpha> vid1))\<^sup>* \<Longrightarrow>
        (y, z) \<in> prog_sem I ($\<alpha> vid1) \<Longrightarrow>
        y \<in> fml_sem I (Predicational pid1) \<Longrightarrow>
        z \<in> fml_sem I (Predicational pid1)" using zPP by simp
    qed
  qed
  show "\<nu> \<in> fml_sem I ([[$\<alpha> vid1**]]Predicational pid1)"
    using res by (simp add: mem_Collect_eq box_sem loop_sem) 
qed

theorem I_valid: "valid Iaxiom" 
  apply(unfold Iaxiom_def valid_def)
  apply(rule impI | rule allI)+
  apply(simp only: impl_sem)
  using I_axiom_lemma by blast

theorem V_valid: "valid Vaxiom"
  apply(simp only: valid_def Vaxiom_def impl_sem box_sem)
  apply(rule allI | rule impI)+
  apply(auto simp add: empty_def)
done

  
definition G_holds :: "('sf, 'sc, 'sz) formula \<Rightarrow> ('sf, 'sc, 'sz) hp \<Rightarrow> bool"
  where "G_holds \<phi> \<alpha> \<equiv> valid \<phi> \<longrightarrow> valid ([[\<alpha>]]\<phi>)"

definition Skolem_holds :: "('sf, 'sc, 'sz) formula \<Rightarrow> 'sz \<Rightarrow> bool"
  where "Skolem_holds \<phi> var \<equiv> valid \<phi> \<longrightarrow> valid (Forall var \<phi>)"

definition MP_holds :: "('sf, 'sc, 'sz) formula \<Rightarrow> ('sf, 'sc, 'sz) formula \<Rightarrow> bool"
  where "MP_holds \<phi> \<psi> \<equiv> valid (\<phi> \<rightarrow> \<psi>) \<longrightarrow> valid \<phi> \<longrightarrow> valid \<psi>"

definition CT_holds :: "'sf \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> bool"
  where "CT_holds g \<theta> \<theta>' \<equiv> valid (Equals \<theta> \<theta>')
    \<longrightarrow> valid (Equals (Function g (singleton \<theta>)) (Function g (singleton \<theta>')))"

definition CQ_holds :: "'sz \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> ('sf, 'sz) trm \<Rightarrow> bool"
  where "CQ_holds p \<theta> \<theta>' \<equiv> valid (Equals \<theta> \<theta>')
    \<longrightarrow> valid ((Prop p (singleton \<theta>)) \<leftrightarrow> (Prop p (singleton \<theta>')))"

definition CE_holds :: "'sc \<Rightarrow> ('sf, 'sc, 'sz) formula \<Rightarrow> ('sf, 'sc, 'sz) formula \<Rightarrow> bool"
  where "CE_holds var \<phi> \<psi> \<equiv> valid (\<phi> \<leftrightarrow> \<psi>)
    \<longrightarrow> valid (InContext var \<phi> \<leftrightarrow> InContext var \<psi>)"

  
subsection \<open>Soundness for rules\<close>
theorem G_sound: "G_holds \<phi> \<alpha>"
  by (simp add: G_holds_def valid_def box_sem)

theorem Skolem_sound: "Skolem_holds \<phi> var"
  by (simp add: Skolem_holds_def valid_def)

theorem MP_sound: "MP_holds \<phi> \<psi>"
  by (auto simp add: MP_holds_def valid_def)

lemma CT_lemma:"\<And>I::('sf::finite, 'sc::finite, 'sz::finite) interp. \<And> a::(real, 'sz) vec. \<And> b::(real, 'sz) vec. \<forall>I::('sf,'sc,'sz) interp. is_interp I \<longrightarrow> (\<forall>a b. dterm_sem I \<theta> (a, b) = dterm_sem I \<theta>' (a, b)) \<Longrightarrow>
             is_interp I \<Longrightarrow>
             Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta> else  (Const 0)) (a, b))) =
             Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta>' else (Const 0)) (a, b)))"
proof -
  fix I :: "('sf::finite, 'sc::finite, 'sz::finite) interp" and a :: "(real, 'sz) vec" and b :: "(real, 'sz) vec"
  assume a1: "is_interp I"
  (* NOTE: example of type annotation sadness here *)
  assume "\<forall>I::('sf,'sc,'sz) interp. is_interp I \<longrightarrow> (\<forall>a b. dterm_sem I \<theta> (a, b) = dterm_sem I \<theta>' (a, b))"
  then have "\<forall>i. dterm_sem I (if i = vid1 then \<theta>' else (Const 0)) (a, b) = dterm_sem I (if i = vid1 then \<theta> else (Const 0)) (a, b)"
    using a1 by presburger
  then show "Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta> else (Const 0)) (a, b)))
           = Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta>' else (Const 0)) (a, b)))"
    by presburger
qed

theorem CT_sound: "CT_holds var \<theta> \<theta>'"
  apply(simp only: CT_holds_def valid_def equals_sem vec_extensionality vec_eq_iff)
  apply(simp)
  apply(rule allI | rule impI)+
  apply(simp add: CT_lemma)
done

(* TODO: I think this lemma actually makes no sense.*)
lemma CQ_lemma:"\<And>I::('sf,'sc,'sz) interp. \<And>\<nu>. \<forall>I::('sf,'sc,'sz) interp. \<forall>\<nu>. is_interp I \<longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu> \<Longrightarrow>
           is_interp I \<Longrightarrow>
           Predicates I (var::'sz) (vec_lambda(\<lambda>i. dterm_sem I (if i = vid1 then \<theta> else  (Const 0)) \<nu>)) =
           Predicates I var (vec_lambda(\<lambda>i. dterm_sem I (if i = vid1 then \<theta>' else (Const 0)) \<nu>))"
proof -
  fix I :: "('sf,'sc,'sz) interp" and \<nu> :: "(real, 'sz) vec \<times> (real, 'sz) vec"
  assume a1: "\<forall>I::('sf,'sc,'sz) interp. \<forall> \<nu>. is_interp I \<longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu>"
  assume a2: "is_interp I"
  obtain ff :: "('sz \<Rightarrow> real) \<Rightarrow> ('sz \<Rightarrow> real) \<Rightarrow> 'sz" where
    f3: "\<forall>f fa. f (ff fa f) \<noteq> fa (ff fa f) \<or> vec_lambda f = vec_lambda fa"
    by (meson Cart_lambda_cong)
  have "dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu> "
    using a2 a1 by blast
  then have "dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else  (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>) = vid1 then \<theta> else (Const 0)) \<nu> \<noteq> dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else  (Const 0)) \<nu>) = vid1 then \<theta>' else (Const 0)) \<nu> \<longrightarrow> dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>) = vid1 then \<theta> else (Const 0)) \<nu> = dterm_sem I (if ff (\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else (Const 0)) \<nu>) (\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>) = vid1 then \<theta>' else (Const 0)) \<nu>"
    by simp
  then have "(vec_lambda(\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>)) = (vec_lambda(\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else  (Const 0)) \<nu>))"
    using f3 by meson
  then show "Predicates I (var::'sz) (vec_lambda(\<lambda>f. dterm_sem I (if f = vid1 then \<theta> else (Const 0)) \<nu>)) = Predicates I var (vec_lambda(\<lambda>f. dterm_sem I (if f = vid1 then \<theta>' else  (Const 0)) \<nu>))"
  (* TODO: Simplify. This subproof used to be a one-line "by presburger" *)
  proof -
    obtain ss :: "('sz \<Rightarrow> real) \<Rightarrow> ('sz \<Rightarrow> real) \<Rightarrow> 'sz" where
      f1: "\<forall>f fa. f (ss fa f) \<noteq> fa (ss fa f) \<or> vec_lambda f = vec_lambda fa"
      by (meson Cart_lambda_cong)
    have "dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = vid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = vid1 then \<theta> else Const 0) \<nu>) = vid1 then \<theta> else Const 0) \<nu> \<noteq> dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = vid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = vid1 then \<theta> else Const 0) \<nu>) = vid1 then \<theta>' else Const 0) \<nu> \<longrightarrow> dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = vid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = vid1 then \<theta> else Const 0) \<nu>) = vid1 then \<theta> else Const 0) \<nu> = dterm_sem I (if ss (\<lambda>s. dterm_sem I (if s = vid1 then \<theta>' else Const 0) \<nu>) (\<lambda>s. dterm_sem I (if s = vid1 then \<theta> else Const 0) \<nu>) = vid1 then \<theta>' else Const 0) \<nu>"
      using \<open>dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu>\<close> by presburger
    then have "(\<chi> s. dterm_sem I (if s = vid1 then \<theta> else Const 0) \<nu>) = (\<chi> s. dterm_sem I (if s = vid1 then \<theta>' else Const 0) \<nu>)"
      using f1 by meson
    then show ?thesis
      by simp
  qed
qed

theorem CQ_sound: "CQ_holds var \<theta> \<theta>'"
  apply(simp only: CQ_holds_def valid_def equals_sem vec_extensionality vec_eq_iff)
  apply(rule allI | rule impI)+
  apply(simp only: iff_sem singleton.simps fml_sem.simps mem_Collect_eq)
  apply(simp only: CQ_lemma)
done

theorem CE_sound: "CE_holds var \<phi> \<psi>"
  apply(simp only: CE_holds_def valid_def iff_sem)
  apply(rule allI | rule impI)+
  apply(simp)
  apply(metis subsetI subset_antisym surj_pair)
done

end end