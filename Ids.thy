theory "Ids"
  imports Complex_Main
   "HOL-Library.Code_Target_Int"
   "Syntax"
begin

(*Differential dynamic logic can be defined for any finite types, given a 
  few elements of those types (so that we can generate axioms). *)
(*locale ids =
  fixes vid1 :: ident
  fixes vid2 :: ident
  fixes vid3 :: ident
  fixes is_vid1 :: "ident \<Rightarrow> bool"
  fixes fid1 :: ident
  fixes fid2 :: ident
  fixes fid3 :: ident
  fixes pid1 :: ident
  fixes pid2 :: ident
  fixes pid3 :: ident
  fixes pid4 :: ident
  assumes vne12:"vid1 \<noteq> vid2"
  assumes vne23:"vid2 \<noteq> vid3"
  assumes vne13:"vid1 \<noteq> vid3"
  assumes fne12:"fid1 \<noteq> fid2"
  assumes fne23:"fid2 \<noteq> fid3"
  assumes fne13:"fid1 \<noteq> fid3"
  assumes pne12:"pid1 \<noteq> pid2"
  assumes pne23:"pid2 \<noteq> pid3"
  assumes pne13:"pid1 \<noteq> pid3"
  assumes pne14:"pid1 \<noteq> pid4"
  assumes pne24:"pid2 \<noteq> pid4"
  assumes pne34:"pid3 \<noteq> pid4"
context ids begin*)
  lemma vne12:"Ix \<noteq> Iy" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto
  lemma vne23:"Iy \<noteq> Iz" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto
  lemma vne13:"Ix \<noteq> Iz" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto
  lemma fne12:"Ix \<noteq> Iy" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto
  lemma fne23:"Iy \<noteq> Iz" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto
  lemma fne13:"Ix \<noteq> Iz" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto
  lemma pne12:"Ix \<noteq> Iy" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto
  lemma pne23:"Iy \<noteq> Iz" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto
  lemma pne13:"Ix \<noteq> Iz" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto
  lemma pne14:"Ix \<noteq> Iw" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto
  lemma pne24:"Iy \<noteq> Iw" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto
  lemma pne34:"Iz \<noteq> Iw" apply (auto simp add: Ix_def Iy_def Iz_def Iw_def)using Ix.abs_eq Ix.rep_eq Iy.abs_eq Iy.rep_eq  Iz.abs_eq Iz.rep_eq Iw.abs_eq Iw.rep_eq by auto

  lemma id_simps:
    "(Ix = Iy) = False" "(Iy = Iz) = False" "(Ix = Iz) = False"
    "(Ix = Iy) = False" "(Iy = Iz) = False" "(Ix = Iz) = False"
    "(Ix = Iy) = False" "(Iy = Iz) = False" "(Ix = Iz) = False" 
    "(Ix = Iw) = False" "(Iy = Iw) = False" "(Iz = Iw) = False"
    "(Iy = Ix) = False" "(Iz = Iy) = False" "(Iz = Ix) = False"
    "(Iy = Ix) = False" "(Iz = Iy) = False" "(Iz = Ix) = False"
    "(Iy = Ix) = False" "(Iz = Iy) = False" "(Iz = Ix) = False" 
    "(Iw = Ix) = False" "(Iw = Iy) = False" "(Iw = Iz) = False"
    using vne12 vne23 vne13 fne12 fne23 fne13 pne12 pne23 pne13 pne14 pne24 pne34 by auto

(* Function applied to one argument *)
definition f1::"ident \<Rightarrow> ident \<Rightarrow> trm"
where "f1 f x = Function f (singleton (Var x))"

(* Function applied to zero arguments (simulates a constant symbol given meaning by the interpretation) *)
definition f0::"ident \<Rightarrow> trm"
where "f0 f = Function f empty"

(* Predicate applied to one argument *)
definition p1::"ident \<Rightarrow> ident \<Rightarrow> formula"
where "p1 p x = Prop p (singleton (Var x))"

(* Predicational *)
definition P::"ident \<Rightarrow> formula"
where "P p = Predicational p"

end
