theory "Axioms" 
imports
  Ordinary_Differential_Equations.ODE_Analysis
  "Ids"
  "Lib"
  "Syntax"
  "Denotational_Semantics"
begin context ids begin

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


definition AllElimAxiom::"('sf,'sc,'sz) formula"
  where [axiom_defs]:"AllElimAxiom \<equiv> (Forall vid1 (Pc pid1)) \<rightarrow> (Pc pid1)"

lemma AllElimAxiom_valid:"valid AllElimAxiom"
proof (unfold AllElimAxiom_def, unfold valid_def, simp, rule allI, rule impI, rule allI, rule allI, rule impI)
  fix I::"('sf,'sc,'sz)interp" and  a b
  assume good_interp:"is_interp I"
  assume all:"\<forall>r. (\<chi> y. if vid1 = y then r else fst (a, b) $ y, b) \<in> Contexts I pid1 UNIV"
  have eq:"(\<chi> y. if vid1 = y then a $ vid1 else fst (a, b) $ y, b) = (a,b)"
    by(auto, rule vec_extensionality,auto)
  show "(a, b) \<in> Contexts I pid1 UNIV"
    using spec[OF all, of "a $ vid1"] eq by auto
qed

(* [a](p_(||)&q_(||)) <-> [a]p_(||)&[a]q_(||)" *)
definition BoxSplitAxiom::"('sf,'sc,'sz) formula"
  where [axiom_defs]:"BoxSplitAxiom \<equiv> 
([[Pvar vid1]](And (Pc pid1) (Pc pid2)))
\<leftrightarrow>  (And ([[Pvar vid1]](Pc pid1))
         ([[Pvar vid1]](Pc pid2)))
"

definition ImpSelfAxiom::"('sf,'sc,'sz) formula"
  where [axiom_defs]:"ImpSelfAxiom \<equiv> 
Equiv
 ((Prop vid1 empty) \<rightarrow>(Prop vid1 empty))
 TT"

(* s() = t() -> (ctxF_(s()) <-> ctxF_(t()))
 *)
definition constFcongAxiom::"('sf,'sc,'sz) formula"
  where [axiom_defs]:"constFcongAxiom \<equiv> 
Implies
 (Equals (Function fid1 empty) (Function fid2 empty))
 (Equiv 
   (Prop vid1 (singleton (Function fid1 empty))) 
   (Prop vid1 (singleton (Function fid2 empty))))
"

lemma constFcong_valid:"valid constFcongAxiom"
proof (simp add: constFcongAxiom_def valid_def, rule allI, rule impI, rule allI, rule allI, rule impI, unfold empty_def)
  fix I::"('sf,'sc,'sz) interp" and a b
  assume good_interp:"is_interp I"
  assume fn:"Functions I fid1 (\<chi> i. dterm_sem I (Const (bword_zero)) (a, b)) = Functions I fid2 (\<chi> i. dterm_sem I (Const (bword_zero)) (a, b))" 
  have vec_eq:"(\<chi> i. dterm_sem I (if i = vid1 then $f fid1 (\<lambda>i. Const (bword_zero)) else Const (bword_zero)) (a, b)) = (\<chi> i. dterm_sem I (if i = vid1 then $f fid2 (\<lambda>i. Const (bword_zero)) else Const (bword_zero)) (a, b))"
    apply(rule vec_extensionality)
    using fn by (auto simp add: empty_def)
  then show "Predicates I vid1 (\<chi> i. dterm_sem I (if i = vid1 then $f fid1 (\<lambda>i. Const (bword_zero))  else Const (bword_zero)) (a, b)) =
             Predicates I vid1 (\<chi> i. dterm_sem I (if i = vid1 then $f fid2 (\<lambda>i. Const (bword_zero))  else Const (bword_zero)) (a, b))"
    by auto
qed

definition assignAnyAxiom::"('sf,'sc,'sz) formula"
  where [axiom_defs]:"assignAnyAxiom \<equiv>
Equiv
 (Box (AssignAny vid1) (Pc pid1))
 (Forall vid1 (Pc pid1))"

lemma assignAny_valid:"valid assignAnyAxiom"
  unfolding assignAnyAxiom_def valid_def Box_def Equiv_def Or_def by auto

definition equalCommuteAxiom::"('sf,'sc,'sz) formula"
  where [axiom_defs]:"equalCommuteAxiom \<equiv>
Equiv
(Equals (f0 fid1) (f0 fid2))
(Equals (f0 fid2) (f0 fid1))
"

lemma equalCommute_valid:"valid equalCommuteAxiom"
  unfolding equalCommuteAxiom_def by(auto simp add: f0_def Equiv_def Or_def empty_def Equals_def valid_def)

definition assignEqAxiom::"('sf,'sc,'sz) formula"
  where [axiom_defs]:"assignEqAxiom \<equiv> 
Equiv 
  ([[Assign vid1 (Function fid1 empty)]](P pid1))
  (Forall vid1 (Implies (Equals (Var vid1) (Function fid1 empty)) (P pid1)))"

lemma assignEq_valid:"valid assignEqAxiom"
proof (unfold assignEqAxiom_def, unfold valid_def, rule allI, rule allI, rule impI, simp)
  fix I::"('sf,'sc,'sz) interp" and \<nu>
  assume "is_interp I"
  have dir1:"((\<chi> y. if vid1 = y then Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) \<nu>) else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P pid1)) \<Longrightarrow>
           (\<forall>r. r = Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>)) \<longrightarrow>
                (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P pid1))"
  proof (auto)
    fix r
    assume f1:"(\<chi> y. if vid1 = y then Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) \<nu>) else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P pid1)"
    assume  f:"r = Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>))"
    have eq:"(\<chi> y. if vid1 = y then r else fst \<nu> $ y) 
           = (\<chi> y. if vid1 = y then Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) \<nu>) else fst \<nu> $ y)"
      apply(rule vec_extensionality)
      using f by (auto simp add: empty_def)
    show "(\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P pid1)"
      using f1 eq by auto
  qed
  have dir2:"(\<forall>r. r = Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>)) \<longrightarrow>
                (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P pid1)) \<Longrightarrow>
    ((\<chi> y. if vid1 = y then Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) \<nu>) else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P pid1))"
  proof -
    assume f:"(\<forall>r. r = Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>)) \<longrightarrow>
                (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P pid1))"
    then have ff:"(\<And>r. r = Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>)) \<Longrightarrow>
                (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P pid1))"
      by auto
    show "((\<chi> y. if vid1 = y then Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) \<nu>) else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P pid1))"
      apply(rule ff)
      by(auto simp add: empty_def)
    qed
  show 
"((\<chi> y. if vid1 = y then Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) \<nu>) else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P pid1)) =
           (\<forall>r. r = Functions I fid1 (\<chi> i. dterm_sem I (local.empty i) (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>)) \<longrightarrow>
                (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>) \<in> fml_sem I (P pid1))"
  using dir1 dir2 by blast
qed

definition allInstAxiom::"('sf,'sc,'sz) formula"
  where [axiom_defs]:"allInstAxiom \<equiv> Implies (Forall vid1 (Prop vid1 (singleton (Var vid1)))) ( Prop vid1(singleton (Function fid1 empty)))"

lemma allInst_valid:"valid allInstAxiom"
proof (unfold allInstAxiom_def, unfold valid_def, rule allI, rule allI, rule impI, simp, rule impI)
  fix I::"('sf,'sc,'sz) interp" and \<nu>
  let ?f = "$f fid1 local.empty"
  let ?fs = "dterm_sem I ?f \<nu>"
  assume "is_interp I"
  assume pre:"(\<forall>r. Predicates I vid1
                 (\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const (bword_zero)) (\<chi> y. if vid1 = y then r else fst \<nu> $ y, snd \<nu>)))"
  have arg_eq:"(\<chi> i. dterm_sem I (if i = vid1 then trm.Var vid1 else Const (bword_zero)) (\<chi> y. if vid1 = y then ?fs else fst \<nu> $ y, snd \<nu>))
                  = (\<chi> i. dterm_sem I (if i = vid1 then ?f else Const (bword_zero)) (fst \<nu> , snd \<nu>))"
    by(rule vec_extensionality,auto)
  show "Predicates I vid1 (\<chi> i. dterm_sem I (if i = vid1 then ?f else Const (bword_zero)) \<nu>)"
    using spec[OF pre, of ?fs] arg_eq by auto
qed

definition EquivReflexiveAxiom::"('sf,'sc,'sz) formula"
  where [axiom_defs]:"EquivReflexiveAxiom \<equiv> (Prop vid1 empty) \<leftrightarrow> (Prop  vid1 empty)"

definition assign_axiom :: "('sf, 'sc, 'sz) formula"
where [axiom_defs]:"assign_axiom \<equiv>
  ([[vid1 := ($f fid1 empty)]] (Prop vid1 (singleton (Var vid1))))
    \<leftrightarrow> Prop vid1 (singleton ($f fid1 empty))"

definition diff_assign_axiom :: "('sf, 'sc, 'sz) formula"
  where [axiom_defs]:"diff_assign_axiom \<equiv>
(* [x_':=f();]p(x_') <-> p(f())*)
  ([[DiffAssign vid1  ($f fid1 empty)]] (Prop vid1 (singleton (DiffVar vid1))))
    \<leftrightarrow> Prop vid1 (singleton ($f fid1 empty))"

definition loop_iterate_axiom :: "('sf, 'sc, 'sz) formula"
where [axiom_defs]:"loop_iterate_axiom \<equiv> ([[$\<alpha> vid1**]]Predicational pid1)
  \<leftrightarrow> ((Predicational pid1) && ([[$\<alpha> vid1]][[$\<alpha> vid1**]]Predicational pid1))"

definition test_axiom :: "('sf, 'sc, 'sz) formula"
where [axiom_defs]:"test_axiom \<equiv>
  ([[?($\<phi> vid2 empty)]]$\<phi> vid1 empty) \<leftrightarrow> (($\<phi> vid2 empty) \<rightarrow> ($\<phi> vid1 empty))"

definition box_axiom :: "('sf, 'sc, 'sz) formula"
where [axiom_defs]:"box_axiom \<equiv> (\<langle>$\<alpha> vid1\<rangle>Predicational pid1) \<leftrightarrow> !([[$\<alpha> vid1]]!(Predicational pid1))"

definition choice_axiom :: "('sf, 'sc, 'sz) formula"
where [axiom_defs]:"choice_axiom \<equiv> ([[$\<alpha> vid1 \<union>\<union> $\<alpha> vid2]]Predicational pid1)
  \<leftrightarrow> (([[$\<alpha> vid1]]Predicational pid1) && ([[$\<alpha> vid2]]Predicational pid1))"

definition compose_axiom :: "('sf, 'sc, 'sz) formula"
where [axiom_defs]:"compose_axiom \<equiv> ([[$\<alpha> vid1 ;; $\<alpha> vid2]]Predicational pid1) \<leftrightarrow> 
  ([[$\<alpha> vid1]][[ $\<alpha> vid2]]Predicational pid1)"
  
definition Kaxiom :: "('sf, 'sc, 'sz) formula"
where [axiom_defs]:"Kaxiom \<equiv> ([[$\<alpha> vid1]]((Predicational pid1) \<rightarrow> (Predicational pid2)))
  \<rightarrow> ([[$\<alpha> vid1]]Predicational pid1) \<rightarrow> ([[$\<alpha> vid1]]Predicational pid2)"

(* Here is an example of an old version of the induction axiom that was too weak
 * and thus very easy to prove: it used predicates when it should have used predicationals.
 * This serves as a reminder to be careful whether other axioms are also too weak. *)
(* 
definition Ibroken :: "('sf, 'sc, 'sz) formula"
  where "Ibroken \<equiv> ([[$$a]]($P [] \<rightarrow> ([[$$a]]$P []))
    \<rightarrow> ($P [] \<rightarrow> ([[($$a)**]]$P [])))"*)

definition Iaxiom :: "('sf, 'sc, 'sz) formula"
  where [axiom_defs]:"Iaxiom \<equiv> 
(Pc pid1  && ([[Loop(Pvar vid1)]](Pc pid1 \<rightarrow> ([[Pvar vid1]] Pc pid1)))) \<rightarrow> ([[Loop(Pvar vid1)]]Pc pid1)"
(*([[($\<alpha> vid1)**]](Predicational pid1 \<rightarrow> ([[$\<alpha> vid1]]Predicational pid1)))
  \<rightarrow>((Predicational pid1 \<rightarrow> ([[($\<alpha> vid1)**]]Predicational pid1)))*)

definition Vaxiom :: "('sf, 'sc, 'sz) formula"
where [axiom_defs]:"Vaxiom \<equiv> ($\<phi> vid1 empty) \<rightarrow> ([[$\<alpha> vid1]]($\<phi> vid1 empty))"

definition TrueImplyAxiom :: "('sf,'sc,'sz) formula"
where [axiom_defs]:"TrueImplyAxiom \<equiv> Equiv (Implies TT (Prop vid1 empty)) (Prop vid1 empty)"

lemma TrueImply_valid: "valid TrueImplyAxiom"
  by(auto simp add: valid_def TrueImplyAxiom_def)

definition diamondAxiom :: "('sf,'sc,'sz) formula"
  where [axiom_defs]:"diamondAxiom \<equiv> Equiv (Not (Box ($\<alpha> vid1 ) (Not (P pid1)))) (Diamond ($\<alpha> vid1) (P pid1))"

lemma diamond_valid: "valid diamondAxiom"
  by(auto simp add: valid_def diamondAxiom_def)

definition diamondModusPonensAxiom :: "('sf,'sc,'sz) formula"
  where [axiom_defs]:"diamondModusPonensAxiom \<equiv> Implies
   (Box ($\<alpha> vid1) (P pid1))
   (Implies 
     (Diamond ($\<alpha> vid1) (P pid2)) 
     (Diamond ($\<alpha> vid1) (And (P pid1) (P pid2))))"

lemma diamondModusPonens_valid:"valid diamondModusPonensAxiom"
  by(auto simp add: diamondModusPonensAxiom_def valid_def)

definition equalReflAxiom :: "('sf,'sc,'sz) formula"
where [axiom_defs]:"equalReflAxiom \<equiv> Equals (Functional fid1) (Functional fid1)"

lemma equalRefl_valid:"valid equalReflAxiom"
  by(auto simp add: equalReflAxiom_def valid_def)

definition lessEqualReflAxiom :: "('sf,'sc,'sz) formula"
where [axiom_defs]:"lessEqualReflAxiom \<equiv> Leq (Functional fid1) (Functional fid1)"

lemma lessEqualRefl_valid:"valid lessEqualReflAxiom"
  by(auto simp add: lessEqualReflAxiom_def valid_def Leq_def)

lemma assign_lem1:
"dterm_sem I (if i = vid1 then Var vid1 else (Const (bword_zero)))
                   (vec_lambda (\<lambda>y. if vid1 = y then Functions I fid1
  (vec_lambda (\<lambda>i. dterm_sem I (empty i) \<nu>)) else  vec_nth (fst \<nu>) y), snd \<nu>)
=
 dterm_sem I (if i = vid1 then $f fid1 empty else (Const (bword_zero))) \<nu>"
  by (cases "i = vid1") (auto simp: proj_sing1)

definition assigndAxiom :: "('sf,'sc,'sz) formula"
  where [axiom_defs]:"assigndAxiom \<equiv> 
Equiv 
  (Diamond (Assign vid1 (f0 fid1)) (Prop vid1 (singleton (Var vid1))))
  (Prop vid1 (singleton (f0 fid1)))
"

lemma assignd_valid:"valid assigndAxiom"
  by(auto simp add: valid_def assigndAxiom_def assign_lem1 f0_def)

definition testdAxiom :: "('sf,'sc,'sz) formula"
  where [axiom_defs]:"testdAxiom \<equiv> Equiv
  (Diamond (Test (Prop vid2 empty)) (Prop vid1 empty))
  (And (Prop vid2 empty) (Prop vid1 empty))"

lemma testd_valid:"valid testdAxiom"
  by(auto simp add: valid_def testdAxiom_def)

definition choicedAxiom :: "('sf,'sc,'sz) formula"
  where [axiom_defs]:"choicedAxiom \<equiv>  Equiv
 (Diamond (Choice ($\<alpha> vid1) ($\<alpha> vid2)) (P pid1))
 (Or (Diamond ($\<alpha> vid1) (P pid1))
     (Diamond ($\<alpha> vid2) (P pid1)))"

lemma choiced_valid:"valid choicedAxiom"
  by(auto simp add: valid_def choicedAxiom_def)

definition composedAxiom :: "('sf,'sc,'sz) formula"
  where [axiom_defs]:"composedAxiom \<equiv> Equiv
(Diamond (Sequence ($\<alpha> vid1) ($\<alpha> vid2)) (P pid1))
(Diamond ($\<alpha> vid1) (Diamond ($\<alpha> vid2) (P pid1)))"

lemma composed_valid:"valid composedAxiom"
  by(auto simp add: valid_def composedAxiom_def)

definition randomdAxiom :: "('sf,'sc,'sz) formula"
  where [axiom_defs]:"randomdAxiom \<equiv> Equiv
(Diamond (AssignAny vid1) (Prop vid1 (singleton (Var vid1))))
(Exists vid1 (Prop vid1 (singleton (Var vid1))))
"

lemma randomd_valid:"valid randomdAxiom"
  by(auto simp add: randomdAxiom_def valid_def)

(*  vid1 (singleton (f1 fid1 vid1))) (Prop vid1 (singleton (f1 fid2 vid1)))*)
definition CEaxrule :: "('sf,'sc,'sz) rule"
  where [axrule_defs]:"CEaxrule \<equiv> ([  ([],[Equiv(Pc pid1 ) (Pc pid2)])  ],    
([], [Equiv(InContext pid3 (Pc pid1)) (InContext pid3 (Pc pid2))]))"

lemma sound_CEaxrule: "sound CEaxrule"
proof (unfold CEaxrule_def,rule soundI)
  fix I::"('sf,'sc,'sz) interp"
  assume good_interp:"is_interp I"
  assume pres:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [([], [Pc pid1 \<leftrightarrow> Pc pid2])] \<Longrightarrow> seq_sem I ([([], [Pc pid1 \<leftrightarrow> Pc pid2])] ! i) = UNIV)"
  have pre:"fml_sem I (Pc pid1) = fml_sem I (Pc pid2)"
    using pres[of 0] 
    by(auto simp add: Equiv_def Or_def TT_def FF_def POS_INF_def NEG_INF_def Abs_bword_inverse bword_zero_def bword_one_def)
  show "seq_sem I ([], [InContext pid3 (Pc pid1) \<leftrightarrow> InContext pid3 (Pc pid2)]) = UNIV"
    using pre by(auto simp add: pre)
qed

definition CTaxrule :: "('sf,'sc,'sz) rule"
  where [axrule_defs]:
"CTaxrule \<equiv> ([],([],[]))"

definition CQaxrule :: "('sf,'sc,'sz) rule"
  where [axrule_defs]:"CQaxrule \<equiv> ([   ([],[Equals ($$F fid1) ($$F fid2)])   ],
  ([],[Equiv(Prop vid3 (singleton ($$F fid1)))(Prop vid3 (singleton ($$F fid2)))]))"

lemma sound_CQaxrule: "sound CQaxrule"
proof (unfold CQaxrule_def,rule soundI)
  fix I::"('sf,'sc,'sz) interp"
  assume good_interp:"is_interp I"
  assume pres:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [([], [Equals ($$F fid1) ($$F fid2)])] \<Longrightarrow> seq_sem I ([([], [Equals ($$F fid1) ($$F fid2)])] ! i) = UNIV)"
  have pre:"fml_sem I (Equals ($$F fid1) ($$F fid2)) = UNIV"
    using pres[of 0]  
    by(auto simp add: Equiv_def Or_def TT_def FF_def POS_INF_def NEG_INF_def Abs_bword_inverse bword_zero_def bword_one_def)
  then have pre2:"dterm_sem I ($$F fid1) = dterm_sem I ($$F fid2)"
    using pres[of 0] apply(auto simp add: Equiv_def Or_def TT_def FF_def pres[of 0])
    apply(rule ext)
    using pre by auto
  have vec_eq:"\<And>a b. (\<chi> i. dterm_sem I (if i = vid1 then $$F fid1 else Const (bword_zero)) (a, b)) = (\<chi> i. dterm_sem I (if i = vid1 then $$F fid2 else Const (bword_zero)) (a, b))"
    apply(rule vec_extensionality)
    using pre2 by(auto)
  show "seq_sem I ([], [Equiv(Prop vid3 (singleton ($$F fid1)))(Prop vid3 (singleton ($$F fid2)))]) = UNIV"
    using pre2 vec_eq by(auto simp add: pre2 vec_eq)
qed

definition Gaxrule :: "('sf,'sc,'sz) rule"
where [axrule_defs]:"Gaxrule \<equiv> ([   ([],[(P pid1)])   ],   ([],[ ([[Pvar vid1]](P pid1)) ]))"

lemma sound_Gaxrule: "sound Gaxrule"
proof (unfold Gaxrule_def,rule soundI)
  fix I::"('sf,'sc,'sz) interp"
  assume good_interp:"is_interp I"
  assume pres:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [([], [P pid1])] \<Longrightarrow> seq_sem I ([([], [P pid1])] ! i) = UNIV)"
  then have pre:"(\<And>\<nu>. \<nu> \<in> fml_sem I (P pid1))" using pres[of 0] 
    by(auto simp add: Equiv_def Or_def TT_def FF_def Implies_def POS_INF_def NEG_INF_def Abs_bword_inverse bword_zero_def bword_one_def)
  show "seq_sem I ([], [([[$\<alpha> vid1]]P pid1)]) = UNIV"
    by(auto simp add: pre)
qed

definition monbrule :: "('sf,'sc,'sz) rule"
where [axrule_defs]:"monbrule \<equiv> ([   ([P pid1],[(P pid2)])   ],   ([([[Pvar vid1]](P pid1))],[ ([[Pvar vid1]](P pid2)) ]))"

lemma sound_monbrule: "sound monbrule"
proof (unfold monbrule_def,rule soundI)
  fix I::"('sf,'sc,'sz) interp"
  assume good_interp:"is_interp I"
  assume pres:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [([P pid1], [P pid2])] \<Longrightarrow> seq_sem I ([([P pid1], [P pid2])] ! i) = UNIV)"
  then have pre:"\<And>\<nu>. \<nu> \<in> fml_sem I (P pid1) \<Longrightarrow> \<nu> \<in> fml_sem I (P pid2)"
    using pres[of 0] 
    by(auto simp add: Equiv_def Or_def TT_def FF_def POS_INF_def NEG_INF_def Abs_bword_inverse Implies_def bword_zero_def bword_one_def)
  then show "seq_sem I ([([[$\<alpha> vid1]]P pid1)], [([[$\<alpha> vid1]]P pid2)]) = UNIV"
    by(auto simp add: FF_def TT_def Implies_def Or_def)
qed

subsection \<open>Validity proofs for axioms\<close>
text \<open>Because an axiom in a uniform substitution calculus is an individual formula, 
  proving the validity of that formula suffices to prove soundness\<close>
theorem test_valid: "valid test_axiom"
  by (auto simp add: valid_def test_axiom_def)  

lemma diff_assign_lem1:
"dterm_sem I (if i = vid1 then DiffVar vid1 else (Const (bword_zero)))
                   (fst \<nu>, vec_lambda (\<lambda>y. if vid1 = y then Functions I fid1 (vec_lambda (\<lambda>i. dterm_sem I (empty i) \<nu>)) else  vec_nth (snd \<nu>) y))
=
 dterm_sem I (if i = vid1 then $f fid1 empty else (Const (bword_zero))) \<nu>
"
  by (cases "i = vid1") (auto simp: proj_sing1)

theorem assign_valid: "valid assign_axiom"
  unfolding  valid_def assign_axiom_def
  by (simp add: assign_lem1) 

theorem diff_assign_valid: "valid diff_assign_axiom"
  unfolding  valid_def diff_assign_axiom_def
  by (simp add: diff_assign_lem1) 

lemma mem_to_nonempty: "\<omega> \<in> S \<Longrightarrow> (S \<noteq> {})"
  by (auto)

lemma loop_forward: "\<nu> \<in> fml_sem I ([[$\<alpha> id1**]]Predicational pid1)
  \<longrightarrow> \<nu> \<in> fml_sem I (Predicational pid1&&[[$\<alpha> id1]][[$\<alpha> id1**]]Predicational pid1)"
  by (cases \<nu>) (auto intro: converse_rtrancl_into_rtrancl simp add: box_sem)

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

theorem compose_valid: "valid compose_axiom"
  unfolding valid_def compose_axiom_def by (auto)
    
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
  apply(auto simp add: impl_sem)
proof -
  fix I::"('sf,'sc,'sz)interp" and a b c d
  assume good_interp:"is_interp I"
  assume P1:"(a, b) \<in> Contexts I pid1 UNIV"
  assume "\<forall>aa ba. ((a, b), aa, ba) \<in> (Programs I vid1)\<^sup>* \<longrightarrow>
               (aa, ba) \<in> Contexts I pid1 UNIV \<longrightarrow> (\<forall>a b. ((aa, ba), a, b) \<in> Programs I vid1 \<longrightarrow> (a, b) \<in> Contexts I pid1 UNIV)"
  then have IS:"\<And> e f g h. ((a, b), (e, f)) \<in> (Programs I vid1)\<^sup>* \<Longrightarrow>
               (e, f) \<in> Contexts I pid1 UNIV \<Longrightarrow> ((e, f), (g,h)) \<in> Programs I vid1 \<Longrightarrow> (g,h) \<in> Contexts I pid1 UNIV"
    by auto
  have res:"\<And>c d. ((a,b), (c,d)) \<in> (Programs I vid1)\<^sup>* \<Longrightarrow> (c,d) \<in> Contexts I pid1 UNIV"
  proof -
    fix c d 
    show "(((a,b), (c,d)) \<in> (Programs  I vid1)\<^sup>*) \<Longrightarrow> (c,d) \<in> Contexts I pid1 UNIV"
      apply(induction rule:rtrancl_induct)
       apply(rule P1)
    proof -
      fix y z
      assume vy:"((a,b), y) \<in> (Programs I  vid1)\<^sup>*"
      assume yz:"(y, z) \<in> Programs I vid1"
      assume yPP:"y \<in> Contexts I pid1 UNIV"
      have almost:"\<And>z.  ((fst y, snd y), z) \<in> Programs I vid1 \<Longrightarrow> (fst z,snd z) \<in> Contexts I pid1 UNIV"
        apply(rule IS[of "fst y" "snd y"] )
        using vy apply(cases y,auto)
        using yPP by auto
      then have imp3:"y \<in> Contexts I pid1 UNIV \<Longrightarrow>  y \<in> fml_sem I ([[$\<alpha> vid1 ]](Predicational pid1))"
        by(auto)
      have imp4:"y \<in> fml_sem I (Predicational pid1) \<Longrightarrow> y \<in> fml_sem I  ([[$\<alpha> vid1]](Predicational pid1))"
        using imp3 impl_sem by (auto)
      have yaPP:"y \<in> fml_sem I ([[$\<alpha> vid1]]Predicational pid1)" using imp4 yPP by auto
      have zPP:"z \<in> fml_sem I (Predicational pid1)" using yaPP box_sem yz mem_Collect_eq 
        proof -
        have "(y, z) \<in> prog_sem I ($\<alpha> vid1)"
          by (simp add: yz)
        then show ?thesis
          using box_sem yaPP by blast
        qed
      show "z \<in> Contexts I pid1 UNIV" using zPP by simp
    qed
  qed
  then show "((a, b), c, d) \<in> (Programs I vid1)\<^sup>* \<Longrightarrow> (c, d) \<in> Contexts I pid1 UNIV" by auto
qed

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
  
subsection \<open>Soundness proofs for rules\<close>
theorem G_sound: "G_holds \<phi> \<alpha>"
  by (simp add: G_holds_def valid_def box_sem)

theorem Skolem_sound: "Skolem_holds \<phi> var"
  by (simp add: Skolem_holds_def valid_def)

theorem MP_sound: "MP_holds \<phi> \<psi>"
  by (auto simp add: MP_holds_def valid_def)

lemma CT_lemma:"\<And>I::('sf::finite, 'sc::finite, 'sz::{finite,linorder}) interp. \<And> a::(real, 'sz) vec. \<And> b::(real, 'sz) vec. \<forall>I::('sf,'sc,'sz) interp. is_interp I \<longrightarrow> (\<forall>a b. dterm_sem I \<theta> (a, b) = dterm_sem I \<theta>' (a, b)) \<Longrightarrow>
             is_interp I \<Longrightarrow>
             Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta> else  (Const (bword_zero))) (a, b))) =
             Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta>' else (Const (bword_zero))) (a, b)))"
proof -
  fix I :: "('sf::finite, 'sc::finite, 'sz::{finite,linorder}) interp" and a :: "(real, 'sz) vec" and b :: "(real, 'sz) vec"
  assume a1: "is_interp I"
  assume "\<forall>I::('sf,'sc,'sz) interp. is_interp I \<longrightarrow> (\<forall>a b. dterm_sem I \<theta> (a, b) = dterm_sem I \<theta>' (a, b))"
  then have "\<forall>i. dterm_sem I (if i = vid1 then \<theta>' else (Const (bword_zero))) (a, b) = dterm_sem I (if i = vid1 then \<theta> else (Const (bword_zero))) (a, b)"
    using a1 by presburger
  then show "Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta> else (Const (bword_zero))) (a, b)))
           = Functions I var (vec_lambda (\<lambda>i. dterm_sem I (if i = vid1 then \<theta>' else (Const (bword_zero))) (a, b)))"
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
  fix I :: "('sf,'sc,'sz) interp" and a b
  assume sem:"\<forall>I::('sf,'sc,'sz) interp. \<forall> \<nu>. is_interp I \<longrightarrow> dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu>"
  assume good:"is_interp I"
  have sem_eq:"dterm_sem I \<theta> (a,b) = dterm_sem I \<theta>' (a,b)"
    using sem good by auto
  have feq:"(\<chi> i. dterm_sem I (if i = vid1 then \<theta> else Const (bword_zero)) (a, b)) = (\<chi> i. dterm_sem I (if i = vid1 then \<theta>' else Const (bword_zero)) (a, b))"  
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
end end
