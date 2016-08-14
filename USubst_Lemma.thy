theory "USubst_Lemma"
imports
  Complex_Main HOL
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
  "../afp/thys/Ordinary_Differential_Equations/ODE_Analysis"
  "./Ids"
  "./Lib"
  "./Syntax"
  "./Denotational_Semantics"
  "./Frechet_Correctness"
  "./Static_Semantics"
  "./Coincidence"
  "./Bound_Effect"
  "./USubst"
begin context ids begin
(* Properties of adjoints *)
lemma adjoint_consequence:" Vagree \<nu> \<omega> (FVS \<sigma>) \<Longrightarrow> adjoint I \<sigma> \<nu> = adjoint I \<sigma> \<omega>"
  sorry

lemma uadmit_sterm_adjoint:"TUadmit \<sigma> \<theta> U \<Longrightarrow> Vagree \<nu> \<omega> U \<Longrightarrow> sterm_sem (adjoint I \<sigma> \<nu>) \<theta> = sterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
  sorry

lemma uadmit_dterm_adjoint:"TUadmit \<sigma> \<theta> U \<Longrightarrow> Vagree \<nu> \<omega> U \<Longrightarrow> dterm_sem (adjoint I \<sigma> \<nu>) \<theta> = dterm_sem (adjoint I \<sigma> \<omega>) \<theta>"
  sorry

lemma uadmit_prog_adjoint:"PUadmit \<sigma> a U \<Longrightarrow> Vagree \<nu> \<omega> U \<Longrightarrow> prog_sem (adjoint I \<sigma> \<nu>) a = prog_sem (adjoint I \<sigma> \<omega>) a"
and   uadmit_fml_sem:"FUadmit \<sigma> \<phi> U \<Longrightarrow> Vagree \<nu> \<omega> U \<Longrightarrow> fml_sem (adjoint I \<sigma> \<nu>) \<phi> = fml_sem (adjoint I \<sigma> \<omega>) \<phi>"
  sorry

lemma nsubst_sterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
shows "dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> sterm_sem I (NTsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induction rule: dfree.induct)
  case (dfree_Fun args f) then
    show "?case" 
      by(cases "f") (auto simp add:  NTadjoint_free)
qed (auto)
(*
lemma sterm_determines_frechet:
assumes good_interp1:"is_interp I"
assumes good_interp2:"is_interp J"
assumes free1:"dfree (\<theta>1::('a::finite, 'c) trm)"
assumes free2:"dfree (\<theta>2::('a::finite, 'c::finite) trm)"
assumes sem:"sterm_sem I \<theta>1 (fst \<nu>) = sterm_sem J \<theta>2 (fst \<nu>)"
shows "frechet I \<theta>1 (fst \<nu>) (snd \<nu>) = frechet J \<theta>2 (fst \<nu>) (snd \<nu>)"
proof -
  (*   Deriv.has_derivative_unique: (?f has_derivative ?F) (at ?x) \<Longrightarrow> (?f has_derivative ?F') (at ?x) \<Longrightarrow> ?F = ?F'*)
  let ?v = "(fst \<nu>)"
  have d1:"(sterm_sem I \<theta>1 has_derivative frechet I \<theta>1 ?v) (at ?v)" 
    sorry(*     by (auto simp add: frechet_correctness good_interp1 free1)*)
  have "(sterm_sem I \<theta>2 has_derivative frechet I \<theta>2 ?v) (at ?v)" 
    sorry (*by (auto simp add: frechet_correctness good_interp2 free2)*)
  hence d2:"(sterm_sem I \<theta>1 has_derivative frechet I \<theta>2 ?v) (at ?v)"   
    using sem by (auto intro: derivative_eq_intros)
  thus "?thesis" using has_derivative_unique d1 by auto
qed
*)

lemma nsubst_frechet:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"
shows "dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> frechet I (NTsubst \<theta> \<sigma>) (fst \<nu>) = frechet (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induct rule: dfree.induct)    
  case (dfree_Fun args f) then
  show "?case" 
     sorry (*by(cases "f") (auto simp add:  NTadjoint_free nsubst_sterm good_interp )*)
qed (auto  simp add: nsubst_sterm)
    
lemma nsubst_dterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"    
shows "NTadmit \<sigma> \<theta> \<Longrightarrow> dsafe \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dterm_sem I (NTsubst \<theta> \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> \<nu>"
proof (induction rule: NTadmit.induct)
  case (NTadmit_Fun \<sigma> args f) 
    thus "?case" by (cases "f") (auto simp add: vec_extensionality  NTadjoint_def)
next
    case (NTadmit_Diff \<sigma> \<theta>) 
    hence admit:"NTadmit \<sigma> \<theta>"
      and admitU:"NTUadmit \<sigma> \<theta> UNIV"
      and IH : "dsafe \<theta> \<Longrightarrow>
            (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dterm_sem I (NTsubst \<theta> \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> \<nu>"
      and safe: "dsafe (Differential \<theta>)" 
      and freeSub:"\<And>i. dfree (\<sigma> i)"
      by auto
    have free:"dfree \<theta>" using safe by auto
    have sem:"sterm_sem I (NTsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (NTadjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
      using nsubst_sterm[OF free freeSub] by auto
    then show "dterm_sem I (NTsubst (Differential \<theta>) \<sigma>) \<nu> = dterm_sem (NTadjoint I \<sigma> \<nu>) (Differential \<theta>) \<nu>"
      by (auto simp add: directional_derivative_def frechet_correctness nsubst_frechet[OF good_interp free freeSub])
qed (auto simp add: NTadmit.cases)

lemma ntsubst_preserves_free:
"dfree \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dfree(NTsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case"
    by (cases "i") (auto intro:dfree.intros)
qed (auto intro: dfree.intros)

lemma ntsubst_free_to_safe:
"dfree \<theta> \<Longrightarrow> (\<And>i. dsafe (\<sigma> i)) \<Longrightarrow> dsafe (NTsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case"
    by (cases "i") (auto intro:dsafe.intros ntsubst_preserves_free)
qed (auto intro: dsafe.intros)

lemma ntsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow> (\<And>i. dfree (\<sigma> i)) \<Longrightarrow> dsafe (NTsubst \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Fun args i) then show "?case"
    by (cases "i") (auto intro:dsafe.intros ntsubst_preserves_free dfree_is_dsafe)
next
  case (dsafe_Diff \<theta>) then show "?case"
    by  (auto intro:dsafe.intros ntsubst_preserves_free)
qed (auto simp add: ntsubst_preserves_free intro: dsafe.intros)

lemma tsubst_preserves_free:
"dfree \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dfree(Tsubst \<theta> \<sigma>)"
proof (induction rule: dfree.induct) 
  case (dfree_Fun args i) then show "?case" 
    by (cases "SFunctions \<sigma> i") (auto intro:dfree.intros ntsubst_preserves_free)
qed (auto intro: dfree.intros)

lemma tsubst_preserves_safe:
"dsafe \<theta> \<Longrightarrow>  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> dsafe(Tsubst \<theta> \<sigma>)"
proof (induction rule: dsafe.induct) 
  case (dsafe_Fun args i) then show "?case" 
    sorry 
    (* by (cases "SFunctions \<sigma> i") (auto intro:dsafe.intros ntsubst_preserves_safe tsubst_preserves_free dfree_is_dsafe)*)
qed (auto intro: dsafe.intros tsubst_preserves_free)

lemma subst_sterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
shows "
  dfree \<theta> \<Longrightarrow>
  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> 
   sterm_sem I (Tsubst \<theta> \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) \<theta> (fst \<nu>)"
proof (induction rule: dfree.induct)
  case (dfree_Fun args f) 
    note frees = dfree_Fun.hyps(1) and sfree = dfree_Fun.prems(1)
    have IH:"(\<And>i. dfree (args i) \<Longrightarrow>
        sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>))" 
      using  dfree_Fun.prems dfree_Fun.IH by auto
    have eqs:"\<And>i. sterm_sem I (Tsubst (args i) \<sigma>) (fst \<nu>) = sterm_sem (adjoint I \<sigma> \<nu>) (args i) (fst \<nu>)"
      by (auto simp add: IH frees)
    show "?case" 
    proof (cases "SFunctions \<sigma> f")
      fix f'
      assume some:"SFunctions \<sigma> f = Some f'" 
      let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
      have subFree:"(\<And>i. dfree (?sub i))" using tsubst_preserves_free[OF frees sfree] by simp
      have IH2:"sterm_sem I (NTsubst f' ?sub) (fst \<nu>) = sterm_sem (NTadjoint I ?sub \<nu>) f' (fst \<nu>)"
        using frees subFree sfree[OF some] by (simp add: nsubst_sterm)
      show "?thesis" 
        using IH frees by (auto simp add: eqs adjoint_free[OF sfree] IH2 NTadjoint_free[OF subFree] some)
    qed (auto simp add: IH adjoint_def vec_extensionality frees)
  qed auto

lemma subst_dterm:
fixes I::"('sf, 'sc, 'sz) interp"
fixes \<nu>::"'sz state"
assumes good_interp:"is_interp I"
shows "
  Tadmit \<sigma> \<theta> \<Longrightarrow>
  dsafe \<theta> \<Longrightarrow>
  (\<And>i f'. SFunctions \<sigma> i = Some f' \<Longrightarrow> dfree f') \<Longrightarrow> 
   dterm_sem I (Tsubst \<theta> \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) \<theta> \<nu>"
proof (induction rule: Tadmit.induct)
  case (Tadmit_Fun \<sigma> args f) 
    note safe = Tadmit_Fun.prems(1) and sfree = Tadmit_Fun.prems(2)
    hence safes:"\<And>i. dsafe (args i)" by auto
    have IH:"(\<And>i. dsafe (args i) \<Longrightarrow>
        dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>)" 
      using  Tadmit_Fun.prems Tadmit_Fun.IH by auto
    have eqs:"\<And>i. dterm_sem I (Tsubst (args i) \<sigma>) \<nu> = dterm_sem (adjoint I \<sigma> \<nu>) (args i) \<nu>"
      by (auto simp add: IH safes)
    show "?case" 
    proof (cases "SFunctions \<sigma> f")
      fix f'
      assume some:"SFunctions \<sigma> f = Some f'" 
      let ?sub = "(\<lambda> i. Tsubst (args i) \<sigma>)"
      have subFree:"(\<And>i. dfree (?sub i))" sorry (*using tsubst_preserves_free[OF safes sfree] by simp*)
      have admit:"\<And>i. NTadmit ?sub f'" sorry
      have safef:"dsafe f'" sorry
      have IH2:"dterm_sem I (NTsubst f' ?sub) \<nu> = dterm_sem (NTadjoint I ?sub \<nu>) f' \<nu>"
        by (simp add: nsubst_dterm[OF good_interp admit safef subFree])
      show "?thesis" 
        using IH safes (*by (auto simp add: eqs adjoint_free[OF sfree] IH2 NTadjoint_free[OF subFree] some good_interp)*)
        sorry
    qed (auto simp add: IH adjoint_def vec_extensionality safes)
next
    case (Tadmit_Diff \<sigma> \<theta>) then show "?case" sorry
  qed auto

end end