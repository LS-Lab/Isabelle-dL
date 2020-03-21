theory "Axioms" 
imports
  Ordinary_Differential_Equations.ODE_Analysis
  "Ids"
  "Lib"
  "Syntax"
  "Denotational_Semantics"
begin
section \<open>Axioms\<close>
text \<open>
  The uniform substitution calculus is based on a finite list of concrete
  axioms, which are defined and proved valid (as in sound) in this section. When axioms apply
  to arbitrary programs or formulas, they mention concrete program or formula
  variables, which are then instantiated by uniform substitution, as opposed
  metavariables.
  
  This section contains axioms and rules for propositional connectives and programs other than
  ODE's. Differential axioms are handled separately because the proofs are significantly more involved.
  \<close>
named_theorems axiom_defs "Axiom definitions"
named_theorems axrule_defs "Axiomatic Rule definitions"


definition AllElimAxiom::"formula"
  where [axiom_defs]:"AllElimAxiom \<equiv> (Forall Ix (Pc Ix)) \<rightarrow> (Pc Ix)"

lemma AllElimAxiom_valid:"valid AllElimAxiom"
proof (unfold AllElimAxiom_def, unfold valid_def, simp, rule allI, rule impI, rule allI, rule allI, rule impI)
  fix I::"interp" and  a b
  assume good_interp:"is_interp I"
  assume all:"\<forall>r. (\<chi> y. if Ix = y then r else fst (a, b) $ y, b) \<in> Contexts I Ix UNIV"
  have eq:"(\<chi> y. if Ix = y then a $ Ix else fst (a, b) $ y, b) = (a,b)"
    by(auto, rule vec_extensionality,auto)
  show "(a, b) \<in> Contexts I Ix UNIV"
    using spec[OF all, of "a $ Ix"] eq by auto
qed

(* [a](p_(||)&q_(||)) <-> [a]p_(||)&[a]q_(||)" *)
definition BoxSplitAxiom::"formula"
  where [axiom_defs]:"BoxSplitAxiom \<equiv> 
([[Pvar Ix]](And (Pc Ix) (Pc pid2)))
\<leftrightarrow>  (And ([[Pvar Ix]](Pc Ix))
         ([[Pvar Ix]](Pc pid2)))
"

definition ImpSelfAxiom::"formula"
  where [axiom_defs]:"ImpSelfAxiom \<equiv> 
Equiv
 ((Prop Ix empty) \<rightarrow>(Prop Ix empty))
 TT"

(* s() = t() -> (ctxF_(s()) <-> ctxF_(t()))
 *)
definition constFcongAxiom::"formula"
  where [axiom_defs]:"constFcongAxiom \<equiv> 
Implies
 (Equals (Function Ix empty) (Function fid2 empty))
 (Equiv 
   (Prop Ix (singleton (Function Ix empty))) 
   (Prop Ix (singleton (Function fid2 empty))))
"

lemma constFcong_valid:"valid constFcongAxiom"
proof (simp add: constFcongAxiom_def valid_def, rule allI, rule impI, rule allI, rule allI, rule impI, unfold empty_def)
  fix I::"interp" and a b
  assume good_interp:"is_interp I"
  assume fn:"Functions I Ix (\<chi> i. dterm_sem I (Const (bword_zero)) (a, b)) = Functions I Iy (\<chi> i. dterm_sem I (Const (bword_zero)) (a, b))" 
  have vec_eq:"(\<chi> i. dterm_sem I (if i = Ix then $f Ix (\<lambda>i. Const (bword_zero)) else Const (bword_zero)) (a, b)) = (\<chi> i. dterm_sem I (if i = Ix then $f Iy (\<lambda>i. Const (bword_zero)) else Const (bword_zero)) (a, b))"
    apply(rule vec_extensionality)
    using fn by (auto simp add: empty_def)
  then show "Predicates I Ix (\<chi> i. dterm_sem I (if i = Ix then $f Ix (\<lambda>i. Const (bword_zero))  else Const (bword_zero)) (a, b)) =
             Predicates I Ix (\<chi> i. dterm_sem I (if i = Ix then $f Iy (\<lambda>i. Const (bword_zero))  else Const (bword_zero)) (a, b))"
    by auto
qed

definition assignAnyAxiom::"formula"
  where [axiom_defs]:"assignAnyAxiom \<equiv>
Equiv
 (Box (AssignAny Ix) (Pc Ix))
 (Forall Ix (Pc Ix))"

lemma assignAny_valid:"valid assignAnyAxiom"
  unfolding assignAnyAxiom_def valid_def Box_def Equiv_def Or_def by auto

definition equalCommuteAxiom::"formula"
  where [axiom_defs]:"equalCommuteAxiom \<equiv>
Equiv
(Equals (f0 Ix) (f0 fid2))
(Equals (f0 fid2) (f0 Ix))
"

lemma equalCommute_valid:"valid equalCommuteAxiom"
  unfolding equalCommuteAxiom_def by(auto simp add: f0_def Equiv_def Or_def empty_def Equals_def valid_def)

definition assignEqAxiom::"formula"
  where [axiom_defs]:"assignEqAxiom \<equiv> 
Equiv 
  ([[(Syntax.Assign Ix (Function Ix empty))::hp]](P Ix))
  (Forall Ix (Implies (Equals (Syntax.Var Ix) (Function Ix empty)) (P Ix)))"

lemma assignEq_valid:"valid assignEqAxiom"
proof (unfold assignEqAxiom_def, unfold valid_def, rule allI, rule allI, rule impI, simp)
  fix I::"interp" and \<nu>
  assume "is_interp I"
  have dir1:"((\<chi> y. if Ix = y then Functions I Ix (\<chi> i. dterm_sem I (empty i) \<nu>) else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P Ix)) \<Longrightarrow>
           (\<forall>r. r = Functions I Ix (\<chi> i. dterm_sem I (empty i) (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>)) \<longrightarrow>
                (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P Ix))"
  proof (auto)
    fix r
    assume f1:"(\<chi> y. if Ix = y then Functions I Ix (\<chi> i. dterm_sem I (empty i) \<nu>) else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P Ix)"
    assume  f:"r = Functions I Ix (\<chi> i. dterm_sem I (empty i) (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>))"
    have eq:"(\<chi> y. if Ix = y then r else fst \<nu> $ y) 
           = (\<chi> y. if Ix = y then Functions I Ix (\<chi> i. dterm_sem I (empty i) \<nu>) else fst \<nu> $ y)"
      apply(rule vec_extensionality)
      using f by (auto simp add: empty_def)
    show "(\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P Ix)"
      using f1 eq by auto
  qed
  have dir2:"(\<forall>r. r = Functions I Ix (\<chi> i. dterm_sem I (empty i) (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>)) \<longrightarrow>
                (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P Ix)) \<Longrightarrow>
    ((\<chi> y. if Ix = y then Functions I Ix (\<chi> i. dterm_sem I (empty i) \<nu>) else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P Ix))"
  proof -
    assume f:"(\<forall>r. r = Functions I Ix (\<chi> i. dterm_sem I (empty i) (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>)) \<longrightarrow>
                (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P Ix))"
    then have ff:"(\<And>r. r = Functions I Ix (\<chi> i. dterm_sem I (empty i) (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>)) \<Longrightarrow>
                (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P Ix))"
      by auto
    show "((\<chi> y. if Ix = y then Functions I Ix (\<chi> i. dterm_sem I (empty i) \<nu>) else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P Ix))"
      apply(rule ff)
      by(auto simp add: empty_def)
    qed
  show 
"((\<chi> y. if Ix = y then Functions I Ix (\<chi> i. dterm_sem I (empty i) \<nu>) else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P Ix)) =
           (\<forall>r. r = Functions I Ix (\<chi> i. dterm_sem I (empty i) (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>)) \<longrightarrow>
                (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P Ix))"
  using dir1 dir2  unfolding Ix_def Ix_def Ix_def by blast
qed

definition allInstAxiom::"formula"
  where [axiom_defs]:"allInstAxiom \<equiv> Implies (Forall Ix (Prop Ix (singleton (Syntax.Var Ix)))) ( Prop Ix(singleton (Function Ix empty)))"

lemma allInst_valid:"valid allInstAxiom"
proof (unfold allInstAxiom_def, unfold valid_def, rule allI, rule allI, rule impI, simp, rule impI)
  fix I::"interp" and \<nu>
  let ?f = "$f Ix empty"
  let ?fs = "dterm_sem I ?f \<nu>"
  assume "is_interp I"
  assume pre:"(\<forall>r. Predicates I Ix
                 (\<chi> i. dterm_sem I (if i = Ix then trm.Var Ix else Const (bword_zero)) (\<chi> y. if Ix = y then r else fst \<nu> $ y, snd \<nu>)))"
  have arg_eq:"(\<chi> i. dterm_sem I (if i = Ix then trm.Var Ix else Const (bword_zero)) (\<chi> y. if Ix = y then ?fs else fst \<nu> $ y, snd \<nu>))
                  = (\<chi> i. dterm_sem I (if i = Ix then ?f else Const (bword_zero)) (fst \<nu> , snd \<nu>))"
    by(rule vec_extensionality,auto)
  show "Predicates I Ix (\<chi> i. dterm_sem I (if i = Ix then ?f else Const (bword_zero)) \<nu>)"
    using spec[OF pre, of ?fs] arg_eq by auto
qed

definition EquivReflexiveAxiom::"formula"
  where [axiom_defs]:"EquivReflexiveAxiom \<equiv> (Prop Ix empty) \<leftrightarrow> (Prop  Ix empty)"

definition assign_axiom :: "formula"
where [axiom_defs]:"assign_axiom \<equiv>
  ([[Ix := ($f Ix empty)]] (Prop Ix (singleton (Syntax.Var Ix))))
    \<leftrightarrow> Prop Ix (singleton ($f Ix empty))"

definition diff_assign_axiom :: "formula"
  where [axiom_defs]:"diff_assign_axiom \<equiv>
\<^cancel>\<open> [x_':=f();]p(x_') <-> p(f())\<close>
  ([[DiffAssign Ix  ($f Ix empty)]] (Prop Ix (singleton (DiffVar Ix))))
    \<leftrightarrow> Prop Ix (singleton ($f Ix empty))"

definition loop_iterate_axiom :: "formula"
where [axiom_defs]:"loop_iterate_axiom \<equiv> ([[$\<alpha> Ix**]]Predicational Ix)
  \<leftrightarrow> ((Predicational Ix) && ([[$\<alpha> Ix]][[$\<alpha> Ix**]]Predicational Ix))"

definition test_axiom :: "formula"
where [axiom_defs]:"test_axiom \<equiv>
  ([[?($\<phi> Ix empty)]]$\<phi> Ix empty) \<leftrightarrow> (($\<phi> Ix empty) \<rightarrow> ($\<phi> Ix empty))"

definition box_axiom :: "formula"
where [axiom_defs]:"box_axiom \<equiv> (\<langle>$\<alpha> Ix\<rangle>Predicational Ix) \<leftrightarrow> !([[$\<alpha> Ix]]!(Predicational Ix))"

definition choice_axiom :: "formula"
where [axiom_defs]:"choice_axiom \<equiv> ([[$\<alpha> Ix \<union>\<union> $\<alpha> vid2]]Predicational Ix)
  \<leftrightarrow> (([[$\<alpha> Ix]]Predicational Ix) && ([[$\<alpha> vid2]]Predicational Ix))"

definition compose_axiom :: "formula"
where [axiom_defs]:"compose_axiom \<equiv> ([[$\<alpha> Ix ;; $\<alpha> vid2]]Predicational Ix) \<leftrightarrow> 
  ([[$\<alpha> Ix]][[ $\<alpha> vid2]]Predicational Ix)"
  
definition Kaxiom :: "formula"
where [axiom_defs]:"Kaxiom \<equiv> ([[$\<alpha> Ix]]((Predicational Ix) \<rightarrow> (Predicational pid2)))
  \<rightarrow> ([[$\<alpha> Ix]]Predicational Ix) \<rightarrow> ([[$\<alpha> Ix]]Predicational pid2)"

(* Here is an example of an old version of the induction axiom that was too weak
 * and thus very easy to prove: it used predicates when it should have used predicationals.
 * This serves as a reminder to be careful whether other axioms are also too weak. *)
(* 
definition Ibroken :: "formula"
  where "Ibroken \<equiv> ([[$$a]]($P [] \<rightarrow> ([[$$a]]$P []))
    \<rightarrow> ($P [] \<rightarrow> ([[($$a)**]]$P [])))"*)

definition Iaxiom :: "formula"
  where [axiom_defs]:"Iaxiom \<equiv> 
(Pc Ix  && ([[Loop(Pvar Ix)]](Pc Ix \<rightarrow> ([[Pvar Ix]] Pc Ix)))) \<rightarrow> ([[Loop(Pvar Ix)]]Pc Ix)"
(*([[($\<alpha> Ix)**]](Predicational Ix \<rightarrow> ([[$\<alpha> Ix]]Predicational Ix)))
  \<rightarrow>((Predicational Ix \<rightarrow> ([[($\<alpha> Ix)**]]Predicational Ix)))*)

definition Vaxiom :: "formula"
where [axiom_defs]:"Vaxiom \<equiv> ($\<phi> Ix empty) \<rightarrow> ([[$\<alpha> Ix]]($\<phi> Ix empty))"

definition TrueImplyAxiom :: "formula"
where [axiom_defs]:"TrueImplyAxiom \<equiv> Equiv (Implies TT (Prop Ix empty)) (Prop Ix empty)"

lemma TrueImply_valid: "valid TrueImplyAxiom"
  by(auto simp add: valid_def TrueImplyAxiom_def)

definition diamondAxiom :: "formula"
  where [axiom_defs]:"diamondAxiom \<equiv> Equiv (Not (Box ($\<alpha> Ix ) (Not (P Ix)))) (Diamond ($\<alpha> Ix) (P Ix))"

lemma diamond_valid: "valid diamondAxiom"
  by(auto simp add: valid_def diamondAxiom_def)

definition diamondModusPonensAxiom :: "formula"
  where [axiom_defs]:"diamondModusPonensAxiom \<equiv> Implies
   (Box ($\<alpha> Ix) (P Ix))
   (Implies 
     (Diamond ($\<alpha> Ix) (P pid2)) 
     (Diamond ($\<alpha> Ix) (And (P Ix) (P pid2))))"

lemma diamondModusPonens_valid:"valid diamondModusPonensAxiom"
  by(auto simp add: diamondModusPonensAxiom_def valid_def)

definition equalReflAxiom :: "formula"
  where [axiom_defs]:"equalReflAxiom \<equiv> 
Equiv
  (Equals (Function Ix empty) (Function Ix empty))
  TT
"

lemma equalRefl_valid:"valid equalReflAxiom"
  by(auto simp add: equalReflAxiom_def valid_def)

definition lessEqualReflAxiom :: "formula"
  where [axiom_defs]:"lessEqualReflAxiom \<equiv> 
Equiv
  (Leq (Function Ix empty) (Function Ix empty))
  TT"

lemma lessEqualRefl_valid:"valid lessEqualReflAxiom"
  by(auto simp add: lessEqualReflAxiom_def valid_def Leq_def)

lemma assign_lem1:
"dterm_sem I (if i = Ix then Syntax.Var Ix else (Const (bword_zero)))
                   (vec_lambda (\<lambda>y. if Ix = y then Functions I Ix
  (vec_lambda (\<lambda>i. dterm_sem I (empty i) \<nu>)) else  vec_nth (fst \<nu>) y), snd \<nu>)
=
 dterm_sem I (if i = Ix then $f Ix empty else (Const (bword_zero))) \<nu>"
  by (cases "i = Ix") (auto simp: proj_sing1)

definition assigndAxiom :: "formula"
  where [axiom_defs]:"assigndAxiom \<equiv> 
Equiv 
  (Diamond (Syntax.Assign Ix (f0 Ix)) (Prop Ix (singleton (Syntax.Var Ix))))
  (Prop Ix (singleton (f0 Ix)))
"

lemma assignd_valid:"valid assigndAxiom"
  by(auto simp add: valid_def assigndAxiom_def assign_lem1 f0_def)

definition testdAxiom :: "formula"
  where [axiom_defs]:"testdAxiom \<equiv> Equiv
  (Diamond (Test (Prop vid2 empty)) (Prop Ix empty))
  (And (Prop vid2 empty) (Prop Ix empty))"

lemma testd_valid:"valid testdAxiom"
  by(auto simp add: valid_def testdAxiom_def)

definition choicedAxiom :: "formula"
  where [axiom_defs]:"choicedAxiom \<equiv>  Equiv
 (Diamond (Choice ($\<alpha> Ix) ($\<alpha> vid2)) (P Ix))
 (Or (Diamond ($\<alpha> Ix) (P Ix))
     (Diamond ($\<alpha> vid2) (P Ix)))"

lemma choiced_valid:"valid choicedAxiom"
  by(auto simp add: valid_def choicedAxiom_def)

definition composedAxiom :: "formula"
  where [axiom_defs]:"composedAxiom \<equiv> Equiv
(Diamond (Sequence ($\<alpha> Ix) ($\<alpha> vid2)) (P Ix))
(Diamond ($\<alpha> Ix) (Diamond ($\<alpha> vid2) (P Ix)))"

lemma composed_valid:"valid composedAxiom"
  by(auto simp add: valid_def composedAxiom_def)

definition randomdAxiom :: "formula"
  where [axiom_defs]:"randomdAxiom \<equiv> Equiv
(Diamond (Syntax.AssignAny Ix) (Prop Ix (singleton (Syntax.Var Ix))))
(Exists Ix (Prop Ix (singleton (Syntax.Var Ix))))
"

lemma randomd_valid:"valid randomdAxiom"
  by(auto simp add: randomdAxiom_def valid_def)

(*  Ix (singleton (f1 Ix Ix))) (Prop Ix (singleton (f1 fid2 Ix)))*)
definition CEaxrule :: "rule"
  where [axrule_defs]:"CEaxrule \<equiv> ([  ([],[Equiv(Pc Ix ) (Pc pid2)])  ],    
([], [Equiv(InContext pid3 (Pc Ix)) (InContext pid3 (Pc pid2))]))"

lemma sound_CEaxrule: "sound CEaxrule"
proof (unfold CEaxrule_def,rule soundI)
  fix I::"interp"
  assume good_interp:"is_interp I"
  assume pres:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [([], [Pc Ix \<leftrightarrow> Pc pid2])] \<Longrightarrow> seq_sem I ([([], [Pc Ix \<leftrightarrow> Pc pid2])] ! i) = UNIV)"
  have pre:"fml_sem I (Pc Ix) = fml_sem I (Pc pid2)"
    using pres[of 0] 
    by(auto simp add: Equiv_def Or_def TT_def FF_def POS_INF_def NEG_INF_def Abs_bword_inverse bword_zero_def bword_one_def)
  show "seq_sem I ([], [InContext pid3 (Pc Ix) \<leftrightarrow> InContext pid3 (Pc pid2)]) = UNIV"
    using pre by(auto simp add: pre)
qed

definition CTaxrule :: "rule"
  where [axrule_defs]:
"CTaxrule \<equiv> ([],([],[]))"

definition CQaxrule :: "rule"
  where [axrule_defs]:"CQaxrule \<equiv> ([   ([],[Equals ($$F Ix) ($$F Iy)])   ],
  ([],[Equiv(Prop Iz (singleton ($$F Ix)))(Prop Iz (singleton ($$F Iy)))]))"

lemma sound_CQaxrule: "sound CQaxrule"
proof (unfold CQaxrule_def,rule soundI)
  fix I::"interp"
  assume good_interp:"is_interp I"
  assume pres:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [([], [Equals ($$F Ix) ($$F Iy)])] \<Longrightarrow> seq_sem I ([([], [Equals ($$F Ix) ($$F Iy)])] ! i) = UNIV)"
  have pre:"fml_sem I (Equals ($$F Ix) ($$F Iy)) = UNIV"
    using pres[of 0]  
    by(auto simp add: Equiv_def Or_def TT_def FF_def POS_INF_def NEG_INF_def Abs_bword_inverse bword_zero_def bword_one_def)
  then have pre2:"dterm_sem I ($$F Ix) = dterm_sem I ($$F Iy)"
    using pres[of 0] apply(auto simp add: Equiv_def Or_def TT_def FF_def pres[of 0])
    apply(rule ext)
    using pre by auto
  have vec_eq:"\<And>a b. (\<chi> i. dterm_sem I (if i = Ix then $$F Ix else Const (bword_zero)) (a, b)) = (\<chi> i. dterm_sem I (if i = Ix then $$F Iy else Const (bword_zero)) (a, b))"
    apply(rule vec_extensionality)
    using pre2 by(auto)
  show "seq_sem I ([], [Equiv(Prop Iz (singleton ($$F Ix)))(Prop Iz (singleton ($$F Iy)))]) = UNIV"
    using pre2 vec_eq by(auto simp add: pre2 vec_eq)
qed

definition Gaxrule :: "rule"
where [axrule_defs]:"Gaxrule \<equiv> ([   ([],[(P Ix)])   ],   ([],[ ([[Pvar Ix]](P Ix)) ]))"

lemma sound_Gaxrule: "sound Gaxrule"
proof (unfold Gaxrule_def,rule soundI)
  fix I::"interp"
  assume good_interp:"is_interp I"
  assume pres:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [([], [P Ix])] \<Longrightarrow> seq_sem I ([([], [P Ix])] ! i) = UNIV)"
  then have pre:"(\<And>\<nu>. \<nu> \<in> fml_sem I (P Ix))" using pres[of 0] 
    by(auto simp add: Equiv_def Or_def TT_def FF_def Implies_def POS_INF_def NEG_INF_def Abs_bword_inverse bword_zero_def bword_one_def)
  show "seq_sem I ([], [([[$\<alpha> Ix]]P Ix)]) = UNIV"
    by(auto simp add: pre)
qed

definition monbrule :: "rule"
where [axrule_defs]:"monbrule \<equiv> ([   ([P Ix],[(P pid2)])   ],   ([([[Pvar Ix]](P Ix))],[ ([[Pvar Ix]](P pid2)) ]))"

lemma sound_monbrule: "sound monbrule"
proof (unfold monbrule_def,rule soundI)
  fix I::"interp"
  assume good_interp:"is_interp I"
  assume pres:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [([P Ix], [P pid2])] \<Longrightarrow> seq_sem I ([([P Ix], [P pid2])] ! i) = UNIV)"
  then have pre:"\<And>\<nu>. \<nu> \<in> fml_sem I (P Ix) \<Longrightarrow> \<nu> \<in> fml_sem I (P pid2)"
    using pres[of 0] 
    by(auto simp add: Equiv_def Or_def TT_def FF_def POS_INF_def NEG_INF_def Abs_bword_inverse Implies_def bword_zero_def bword_one_def)
  then show "seq_sem I ([([[$\<alpha> Ix]]P Ix)], [([[$\<alpha> Ix]]P pid2)]) = UNIV"
    by(auto simp add: FF_def TT_def Implies_def Or_def)
qed

subsection \<open>Validity proofs for axioms\<close>
text \<open>Because an axiom in a uniform substitution calculus is an individual formula, 
  proving the validity of that formula suffices to prove soundness\<close>
theorem test_valid: "valid test_axiom"
  by (auto simp add: valid_def test_axiom_def)  

lemma diff_assign_lem1:
"dterm_sem I (if i = Ix then Syntax.DiffVar Ix else (Const (bword_zero)))
                   (fst \<nu>, vec_lambda (\<lambda>y. if Ix = y then Functions I Ix (vec_lambda (\<lambda>i. dterm_sem I (empty i) \<nu>)) else  vec_nth (snd \<nu>) y))
=
 dterm_sem I (if i = Ix then $f Ix empty else (Const (bword_zero))) \<nu>
"
  by (cases "i = Ix") (auto simp: proj_sing1)

theorem assign_valid: "valid assign_axiom"
  unfolding  valid_def assign_axiom_def
  by (simp add: assign_lem1) 

theorem diff_assign_valid: "valid diff_assign_axiom"
  unfolding  valid_def diff_assign_axiom_def
  by (simp add: diff_assign_lem1) 

lemma mem_to_nonempty: "\<omega> \<in> S \<Longrightarrow> (S \<noteq> {})"
  by (auto)

lemma loop_forward: "\<nu> \<in> fml_sem I ([[$\<alpha> id1**]]Predicational Ix)
  \<longrightarrow> \<nu> \<in> fml_sem I (Predicational Ix&&[[$\<alpha> id1]][[$\<alpha> id1**]]Predicational Ix)"
  by (cases \<nu>) (auto intro: converse_rtrancl_into_rtrancl simp add: box_sem)

lemma loop_backward:
 "\<nu> \<in> fml_sem I (Predicational Ix && [[$\<alpha> id1]][[$\<alpha> id1**]]Predicational Ix)
  \<longrightarrow> \<nu> \<in> fml_sem I ([[$\<alpha> id1**]]Predicational Ix)"
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

theorem compose_valid: "valid compose_axiom"
  unfolding valid_def compose_axiom_def by (auto)
    
theorem K_valid: "valid Kaxiom"
  unfolding valid_def Kaxiom_def by (auto)

lemma I_axiom_lemma:
  fixes I::"interp" and \<nu>
  assumes "is_interp I"
  assumes IS:"\<nu> \<in> fml_sem I ([[$\<alpha> Ix**]](Predicational Ix \<rightarrow>
                            [[$\<alpha> Ix]]Predicational Ix))"
  assumes BC:"\<nu> \<in> fml_sem I (Predicational Ix)"
  shows "\<nu> \<in> fml_sem I ([[$\<alpha> Ix**]](Predicational Ix))"
proof -
  have IS':"\<And>\<nu>2. (\<nu>, \<nu>2) \<in> (prog_sem I ($\<alpha> Ix))\<^sup>* \<Longrightarrow> \<nu>2 \<in> fml_sem I (Predicational Ix \<rightarrow> [[$\<alpha> Ix]](Predicational Ix))"
    using IS by (auto simp add: box_sem)
  have res:"\<And>\<nu>3. ((\<nu>, \<nu>3) \<in> (prog_sem I ($\<alpha> Ix))\<^sup>*) \<Longrightarrow> \<nu>3 \<in> fml_sem I (Predicational Ix)"
  proof -
    fix \<nu>3 
    show "((\<nu>, \<nu>3) \<in> (prog_sem I ($\<alpha> Ix))\<^sup>*) \<Longrightarrow> \<nu>3 \<in> fml_sem I (Predicational Ix)"
      apply(induction rule:rtrancl_induct)
       apply(rule BC)
    proof -
      fix y z
      assume vy:"(\<nu>, y) \<in> (prog_sem I ($\<alpha> Ix))\<^sup>*"
      assume yz:"(y, z) \<in> prog_sem I ($\<alpha> Ix)"
      assume yPP:"y \<in> fml_sem I (Predicational Ix)"
      have imp3:"y \<in> fml_sem I (Predicational Ix \<rightarrow> [[$\<alpha> Ix ]](Predicational Ix))"
        using IS' vy by (simp)
      have imp4:"y \<in> fml_sem I (Predicational Ix) \<Longrightarrow> y \<in> fml_sem I  ([[$\<alpha> Ix]](Predicational Ix))"
        using imp3 impl_sem by (auto)
      have yaPP:"y \<in> fml_sem I ([[$\<alpha> Ix]]Predicational Ix)" using imp4 yPP by auto
      have zPP:"z \<in> fml_sem I (Predicational Ix)" using yaPP box_sem yz mem_Collect_eq by blast  
      show "
        (\<nu>, y) \<in> (prog_sem I ($\<alpha> Ix))\<^sup>* \<Longrightarrow>
        (y, z) \<in> prog_sem I ($\<alpha> Ix) \<Longrightarrow>
        y \<in> fml_sem I (Predicational Ix) \<Longrightarrow>
        z \<in> fml_sem I (Predicational Ix)" using zPP by simp
    qed
  qed
  show "\<nu> \<in> fml_sem I ([[$\<alpha> Ix**]]Predicational Ix)"
    using res by (simp add: mem_Collect_eq box_sem loop_sem) 
qed

theorem I_valid: "valid Iaxiom" 
  apply(unfold Iaxiom_def valid_def)
  apply(rule impI | rule allI)+
  apply(auto simp add: impl_sem)
proof -
  fix I::"interp" and a b c d
  assume good_interp:"is_interp I"
  assume P1:"(a, b) \<in> Contexts I Ix UNIV"
  assume "\<forall>aa ba. ((a, b), aa, ba) \<in> (Programs I Ix)\<^sup>* \<longrightarrow>
               (aa, ba) \<in> Contexts I Ix UNIV \<longrightarrow> (\<forall>a b. ((aa, ba), a, b) \<in> Programs I Ix \<longrightarrow> (a, b) \<in> Contexts I Ix UNIV)"
  then have IS:"\<And> e f g h. ((a, b), (e, f)) \<in> (Programs I Ix)\<^sup>* \<Longrightarrow>
               (e, f) \<in> Contexts I Ix UNIV \<Longrightarrow> ((e, f), (g,h)) \<in> Programs I Ix \<Longrightarrow> (g,h) \<in> Contexts I Ix UNIV"
    by auto
  have res:"\<And>c d. ((a,b), (c,d)) \<in> (Programs I Ix)\<^sup>* \<Longrightarrow> (c,d) \<in> Contexts I Ix UNIV"
  proof -
    fix c d 
    show "(((a,b), (c,d)) \<in> (Programs  I Ix)\<^sup>*) \<Longrightarrow> (c,d) \<in> Contexts I Ix UNIV"
      apply(induction rule:rtrancl_induct)
       apply(rule P1)
    proof -
      fix y z
      assume vy:"((a,b), y) \<in> (Programs I  Ix)\<^sup>*"
      assume yz:"(y, z) \<in> Programs I Ix"
      assume yPP:"y \<in> Contexts I Ix UNIV"
      have almost:"\<And>z.  ((fst y, snd y), z) \<in> Programs I Ix \<Longrightarrow> (fst z,snd z) \<in> Contexts I Ix UNIV"
        apply(rule IS[of "fst y" "snd y"] )
        using vy apply(cases y,auto)
        using yPP by auto
      then have imp3:"y \<in> Contexts I Ix UNIV \<Longrightarrow>  y \<in> fml_sem I ([[$\<alpha> Ix ]](Predicational Ix))"
        by(auto)
      have imp4:"y \<in> fml_sem I (Predicational Ix) \<Longrightarrow> y \<in> fml_sem I  ([[$\<alpha> Ix]](Predicational Ix))"
        using imp3 impl_sem by (auto)
      have yaPP:"y \<in> fml_sem I ([[$\<alpha> Ix]]Predicational Ix)" using imp4 yPP by auto
      have zPP:"z \<in> fml_sem I (Predicational Ix)" using yaPP box_sem yz mem_Collect_eq 
        proof -
        have "(y, z) \<in> prog_sem I ($\<alpha> Ix)"
          by (simp add: yz)
        then show ?thesis
          using box_sem yaPP by blast
        qed
      show "z \<in> Contexts I Ix UNIV" using zPP by simp
    qed
  qed
  then show "((a, b), c, d) \<in> (Programs I Ix)\<^sup>* \<Longrightarrow> (c, d) \<in> Contexts I Ix UNIV" by auto
qed

theorem V_valid: "valid Vaxiom"
  apply(simp only: valid_def Vaxiom_def impl_sem box_sem)
  apply(rule allI | rule impI)+
  apply(auto simp add: empty_def)
done
  
definition G_holds :: "formula \<Rightarrow> hp \<Rightarrow> bool"
where "G_holds \<phi> \<alpha> \<equiv> valid \<phi> \<longrightarrow> valid ([[\<alpha>]]\<phi>)"

definition Skolem_holds :: "formula \<Rightarrow> ident \<Rightarrow> bool"
where "Skolem_holds \<phi> var \<equiv> valid \<phi> \<longrightarrow> valid (Forall var \<phi>)"

definition MP_holds :: "formula \<Rightarrow> formula \<Rightarrow> bool"
where "MP_holds \<phi> \<psi> \<equiv> valid (\<phi> \<rightarrow> \<psi>) \<longrightarrow> valid \<phi> \<longrightarrow> valid \<psi>"

definition CT_holds :: "ident \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool"
where "CT_holds g \<theta> \<theta>' \<equiv> valid (Equals \<theta> \<theta>')
  \<longrightarrow> valid (Equals (Function g (singleton \<theta>)) (Function g (singleton \<theta>')))"

definition CQ_holds :: "ident \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool"
where "CQ_holds p \<theta> \<theta>' \<equiv> valid (Equals \<theta> \<theta>')
  \<longrightarrow> valid ((Prop p (singleton \<theta>)) \<leftrightarrow> (Prop p (singleton \<theta>')))"

definition CE_holds :: "ident \<Rightarrow> formula \<Rightarrow> formula \<Rightarrow> bool"
where "CE_holds var \<phi> \<psi> \<equiv> valid (\<phi> \<leftrightarrow> \<psi>)
  \<longrightarrow> valid (InContext var \<phi> \<leftrightarrow> InContext var \<psi>)"
  
subsection \<open>Soundness proofs for rules\<close>
theorem G_sound: "G_holds \<phi> \<alpha>"
  by (simp add: G_holds_def valid_def box_sem)

theorem Skolem_sound: "Skolem_holds \<phi> var"
  by (simp add: Skolem_holds_def valid_def)

theorem MP_sound: "MP_holds \<phi> \<psi>"
  by (auto simp add: MP_holds_def valid_def)

lemma CT_lemma:"\<And>I::interp. \<And> a::(real, ident) vec. \<And> b::(real, ident) vec. \<forall>I::interp. is_interp I \<longrightarrow> (\<forall>a b. dterm_sem I \<theta> (a, b) = dterm_sem I \<theta>' (a, b)) \<Longrightarrow>
             is_interp I \<Longrightarrow>
             Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = Ix then \<theta> else  (Const (bword_zero))) (a, b))) =
             Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = Ix then \<theta>' else (Const (bword_zero))) (a, b)))"
proof -
  fix I :: "interp" and a :: "(real, ident) vec" and b :: "(real, ident) vec"
  assume a1: "is_interp I"
  assume "\<forall>I::interp. is_interp I \<longrightarrow> (\<forall>a b. dterm_sem I \<theta> (a, b) = dterm_sem I \<theta>' (a, b))"
  then have "\<forall>i. dterm_sem I (if i = Ix then \<theta>' else (Const (bword_zero))) (a, b) = dterm_sem I (if i = Ix then \<theta> else (Const (bword_zero))) (a, b)"
    using a1 by presburger
  then show "Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = Ix then \<theta> else (Const (bword_zero))) (a, b)))
           = Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = Ix then \<theta>' else (Const (bword_zero))) (a, b)))"
    by presburger
qed

theorem CT_sound: "CT_holds var \<theta> \<theta>'"
  apply(simp only: CT_holds_def valid_def equals_sem vec_extensionality vec_eq_iff)
  apply(simp)
  apply(rule allI | rule impI)+
  apply(simp add: CT_lemma)
done

theorem CQ_sound: "CQ_holds var \<theta> \<theta>'"
proof (auto simp only: CQ_holds_def valid_def equals_sem vec_extensionality vec_eq_iff singleton.simps mem_Collect_eq)
  fix I :: "interp" and a b
  assume sem:"\<forall>I::interp. \<forall> \<nu>. is_interp I \<longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu>"
  assume good:"is_interp I"
  have sem_eq:"dterm_sem I \<theta> (a,b) = dterm_sem I \<theta>' (a,b)"
    using sem good by auto
  have feq:"(\<chi> i. dterm_sem I (if i = Ix then \<theta> else Const (bword_zero)) (a, b)) = (\<chi> i. dterm_sem I (if i = Ix then \<theta>' else Const (bword_zero)) (a, b))"  
    apply(rule vec_extensionality)
    using sem_eq by auto
  then show "(a, b) \<in> fml_sem I ($\<phi> var (singleton \<theta>) \<leftrightarrow> $\<phi> var (singleton \<theta>'))"
    by auto
qed

theorem CE_sound: "CE_holds var \<phi> \<psi>"
  apply(simp only: CE_holds_def valid_def iff_sem)
  apply(rule allI | rule impI)+
  apply(simp)
  apply(metis subsetI subset_antisym surj_pair)
done
end
