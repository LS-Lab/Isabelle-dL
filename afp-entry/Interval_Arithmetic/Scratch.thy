theory "Scratch"
  imports 
    Complex_Main
begin

lemma condCase[case_names NonNeg Zero Pos]:
  fixes x::real and P
  shows "x \<ge> 0 \<Longrightarrow> (x = 0 \<Longrightarrow> P) \<Longrightarrow> (x > 0 \<Longrightarrow> P) \<Longrightarrow> P"
  by linarith

lemma square:
  fixes y::real
  assumes sign:"y \<ge> 0"
  shows "abs y = y"
proof (cases rule: condCase[OF sign])
  case 1
  then show ?thesis by auto
next
  case 2
  then show ?thesis by auto
qed

lemma square':
  fixes y::real
  assumes sign:"y \<ge> 0"
  shows "abs y = y"
proof (induct taking: y rule: condCase)
  case Zero
  then show ?thesis by auto
next
  case Pos
  then show ?thesis by auto
qed (auto simp add: sign)

end
