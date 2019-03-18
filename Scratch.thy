theory "Scratch"
imports Main  "./Proof_Checker"
begin
type_synonym arity = Enum.finite_5

(* Code snippet for coset code generation credit to Andreas Lochbihler *) 
lemma set_fold_remove1:
  "distinct ys \<Longrightarrow> set (fold remove1 xs ys) = set ys - set xs"
  by(induction xs arbitrary: ys) auto

lemma coset_enum:
  "List.coset xs = set (fold remove1 xs Enum.enum)"
  by(auto simp add: set_fold_remove1 enum_distinct UNIV_enum[symmetric])

lemma image_coset [code]:
  "f ` List.coset xs = set (map f (fold remove1 xs Enum.enum))"
  by(simp only: coset_enum set_map)

  
datatype myvars =
    i1
  | i2
  | i3
  | i4
  | i5
  | i6
  | i7
  | i8
  | i9
  | i10
  | i11
  | i12
  | i13
  | i14
  | i15
  | i16
  | i17
  | i18
  | i19
  | i20
  | i21
  | i22
  | i23
  | i24
  | i25

| i26
| i27
| i28
| i29
| i30
| i31
| i32
| i33




instantiation myvars :: finite begin
instance proof
  have "UNIV = {i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26,i27,i28,i29,i30,i31,i32,i33}"
    unfolding UNIV_def 
    using myvars.exhaust
    by (blast)
  moreover have "finite {i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26,i27,i28,i29,i30,i31,i32,i33}"
    by(auto)
  ultimately show "finite (UNIV:: myvars set)"
    by auto
qed
end
    

instantiation bword :: equal begin
definition equal_bword :: "bword \<Rightarrow> bword \<Rightarrow> bool"
  where "equal_bword \<equiv> (\<lambda>x y. sint (Rep_bword x) = sint (Rep_bword y))"
instance
  apply(standard)
  by(auto simp add: equal_bword_def Rep_bword_inject)
end

instantiation myvars :: enum begin
definition enum_myvars where   "enum_myvars \<equiv> [i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20,i21,i22,i23,i24,i25, i26,i27,i28,i29,i30,i31,i32,i33]"
definition enum_all_myvars where "enum_all_myvars P \<equiv> list_all P [i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20,i21,i22,i23,i24,i25, i26,i27,i28,i29,i30,i31,i32,i33]"
definition enum_ex_myvars where "enum_ex_myvars P \<equiv> list_ex P [i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20,i21,i22,i23,i24,i25, i26,i27,i28,i29,i30,i31,i32,i33]"
instance sorry
(*  apply(standard)
  subgoal apply auto
    subgoal for x
      by(cases x, auto simp add: enum_myvars_def)
    done
    apply (auto simp add: enum_myvars_def)
  subgoal for P x
    by(cases x, auto simp add: enum_myvars_def enum_all_myvars_def)
  subgoal for P
    by(auto simp add: enum_myvars_def enum_all_myvars_def)
  subgoal for P
    by(auto simp add: enum_myvars_def enum_ex_myvars_def)
  subgoal for P x
    by(cases x, auto simp add: enum_myvars_def enum_ex_myvars_def)
  done*)
end


instantiation myvars :: linorder begin
definition less_eq_myvars where
  "x \<le> y \<equiv> 
  (case (x,y) of 
    (i1, _) \<Rightarrow> True
  | (i2, i1) \<Rightarrow> False
  | (i2, _) \<Rightarrow> True
  | (i3, i2) \<Rightarrow> False
  | (i3, i1) \<Rightarrow> False
  | (i3, _) \<Rightarrow> True
  | (i4, i4) \<Rightarrow> True
  | (i4, i5) \<Rightarrow> True
  | (i4, i6) \<Rightarrow> True
  | (i4, i7) \<Rightarrow> True
  | (i4, i8) \<Rightarrow> True
  | (i4, i9) \<Rightarrow> True
  | (i4, i10) \<Rightarrow> True
  | (i4, i11) \<Rightarrow> True
  | (i4, i12) \<Rightarrow> True
  | (i4, i13) \<Rightarrow> True
  | (i4, i14) \<Rightarrow> True
  | (i4, i15) \<Rightarrow> True
  | (i4, i16) \<Rightarrow> True
  | (i4, i17) \<Rightarrow> True
  | (i4, i18) \<Rightarrow> True
  | (i4, i19) \<Rightarrow> True
  | (i4, i20) \<Rightarrow> True
  | (i4, i21) \<Rightarrow> True
  | (i4, i22) \<Rightarrow> True
  | (i4, i23) \<Rightarrow> True
  | (i4, i24) \<Rightarrow> True
  | (i4, i25) \<Rightarrow> True
  | (i4, i26) \<Rightarrow> True
  | (i4, i27) \<Rightarrow> True
  | (i4, i28) \<Rightarrow> True
  | (i4, i29) \<Rightarrow> True
  | (i4, i30) \<Rightarrow> True
  | (i4, i31) \<Rightarrow> True
  | (i4, i32) \<Rightarrow> True
  | (i4, i33) \<Rightarrow> True
  | (i4, _) \<Rightarrow> False
  | (i5, i12) \<Rightarrow> True
  | (i5, i13) \<Rightarrow> True
  | (i5, i14) \<Rightarrow> True
  | (i5, i15) \<Rightarrow> True
  | (i5, i16) \<Rightarrow> True
  | (i5, i17) \<Rightarrow> True
  | (i5, i18) \<Rightarrow> True
  | (i5, i19) \<Rightarrow> True
  | (i5, i20) \<Rightarrow> True
  | (i5, i21) \<Rightarrow> True
  | (i5, i22) \<Rightarrow> True
  | (i5, i23) \<Rightarrow> True
  | (i5, i24) \<Rightarrow> True
  | (i5, i25) \<Rightarrow> True
  | (i5, i26) \<Rightarrow> True
  | (i5, i27) \<Rightarrow> True
  | (i5, i28) \<Rightarrow> True
  | (i5, i29) \<Rightarrow> True
  | (i5, i30) \<Rightarrow> True
  | (i5, i31) \<Rightarrow> True
  | (i5, i32) \<Rightarrow> True
  | (i5, i33) \<Rightarrow> True
  | (i5, i11) \<Rightarrow> True
  | (i5, i10) \<Rightarrow> True
  | (i5, i9) \<Rightarrow> True
  | (i5, i8) \<Rightarrow> True
  | (i5, i7) \<Rightarrow> True
  | (i5, i6) \<Rightarrow> True
  | (i5, i5) \<Rightarrow> True
  | (i5, _) \<Rightarrow> False
  | (i6, i6) \<Rightarrow> True
  | (i6, i7) \<Rightarrow> True
  | (i6, i8) \<Rightarrow> True
  | (i6, i9) \<Rightarrow> True
  | (i6, i10) \<Rightarrow> True
  | (i6, i11) \<Rightarrow> True
  | (i6, i12) \<Rightarrow> True
  | (i6, i13) \<Rightarrow> True
  | (i6, i14) \<Rightarrow> True
  | (i6, i15) \<Rightarrow> True
  | (i6, i16) \<Rightarrow> True
  | (i6, i17) \<Rightarrow> True
  | (i6, i18) \<Rightarrow> True
  | (i6, i19) \<Rightarrow> True
  | (i6, i20) \<Rightarrow> True
  | (i6, i21) \<Rightarrow> True
  | (i6, i22) \<Rightarrow> True
  | (i6, i23) \<Rightarrow> True
  | (i6, i24) \<Rightarrow> True
  | (i6, i25) \<Rightarrow> True
  | (i6, i26) \<Rightarrow> True
  | (i6, i27) \<Rightarrow> True
  | (i6, i28) \<Rightarrow> True
  | (i6, i29) \<Rightarrow> True
  | (i6, i30) \<Rightarrow> True
  | (i6, i31) \<Rightarrow> True
  | (i6, i32) \<Rightarrow> True
  | (i6, i33) \<Rightarrow> True
  | (i6, _) \<Rightarrow> False
  | (i7, i7) \<Rightarrow> True
  | (i7, i8) \<Rightarrow> True
  | (i7, i9) \<Rightarrow> True
  | (i7, i10) \<Rightarrow> True
  | (i7, i11) \<Rightarrow> True
  | (i7, i12) \<Rightarrow> True
  | (i7, i13) \<Rightarrow> True
  | (i7, i14) \<Rightarrow> True
  | (i7, i15) \<Rightarrow> True
  | (i7, i16) \<Rightarrow> True
  | (i7, i17) \<Rightarrow> True
  | (i7, i18) \<Rightarrow> True
  | (i7, i19) \<Rightarrow> True
  | (i7, i20) \<Rightarrow> True
  | (i7, i21) \<Rightarrow> True
  | (i7, i22) \<Rightarrow> True
  | (i7, i23) \<Rightarrow> True
  | (i7, i24) \<Rightarrow> True
  | (i7, i25) \<Rightarrow> True
  | (i7, i26) \<Rightarrow> True
  | (i7, i27) \<Rightarrow> True
  | (i7, i28) \<Rightarrow> True
  | (i7, i29) \<Rightarrow> True
  | (i7, i30) \<Rightarrow> True
  | (i7, i31) \<Rightarrow> True
  | (i7, i32) \<Rightarrow> True
  | (i7, i33) \<Rightarrow> True
  | (i7, _) \<Rightarrow> False
  | (i8, i8) \<Rightarrow> True
  | (i8, i9) \<Rightarrow> True
  | (i8, i10) \<Rightarrow> True
  | (i8, i11) \<Rightarrow> True
  | (i8, i12) \<Rightarrow> True
  | (i8, i13) \<Rightarrow> True
  | (i8, i14) \<Rightarrow> True
  | (i8, i15) \<Rightarrow> True
  | (i8, i16) \<Rightarrow> True
  | (i8, i17) \<Rightarrow> True
  | (i8, i18) \<Rightarrow> True
  | (i8, i19) \<Rightarrow> True
  | (i8, i20) \<Rightarrow> True
  | (i8, i21) \<Rightarrow> True
  | (i8, i22) \<Rightarrow> True
  | (i8, i23) \<Rightarrow> True
  | (i8, i24) \<Rightarrow> True
  | (i8, i25) \<Rightarrow> True  
  | (i8, i26) \<Rightarrow> True
  | (i8, i27) \<Rightarrow> True
  | (i8, i28) \<Rightarrow> True
  | (i8, i29) \<Rightarrow> True
  | (i8, i30) \<Rightarrow> True
  | (i8, i31) \<Rightarrow> True
  | (i8, i32) \<Rightarrow> True
  | (i8, i33) \<Rightarrow> True


  | (i8, _) \<Rightarrow> False
  | (i9, i12) \<Rightarrow> True
  | (i9, i13) \<Rightarrow> True
  | (i9, i14) \<Rightarrow> True
  | (i9, i15) \<Rightarrow> True
  | (i9, i16) \<Rightarrow> True
  | (i9, i17) \<Rightarrow> True
  | (i9, i18) \<Rightarrow> True
  | (i9, i19) \<Rightarrow> True
  | (i9, i20) \<Rightarrow> True
  | (i9, i21) \<Rightarrow> True
  | (i9, i22) \<Rightarrow> True
  | (i9, i23) \<Rightarrow> True
  | (i9, i24) \<Rightarrow> True
  | (i9, i25) \<Rightarrow> True
  | (i9, i26) \<Rightarrow> True
  | (i9, i27) \<Rightarrow> True
  | (i9, i28) \<Rightarrow> True
  | (i9, i29) \<Rightarrow> True
  | (i9, i30) \<Rightarrow> True
  | (i9, i31) \<Rightarrow> True
  | (i9, i32) \<Rightarrow> True
  | (i9, i33) \<Rightarrow> True

  | (i9, i11) \<Rightarrow> True
  | (i9, i10) \<Rightarrow> True
  | (i9, i9) \<Rightarrow> True
  | (i9, _) \<Rightarrow> False
  | (i10, i12) \<Rightarrow> True
  | (i10, i13) \<Rightarrow> True
  | (i10, i14) \<Rightarrow> True
  | (i10, i15) \<Rightarrow> True
  | (i10, i16) \<Rightarrow> True
  | (i10, i17) \<Rightarrow> True
  | (i10, i18) \<Rightarrow> True
  | (i10, i19) \<Rightarrow> True
  | (i10, i20) \<Rightarrow> True
  | (i10, i21) \<Rightarrow> True
  | (i10, i22) \<Rightarrow> True
  | (i10, i23) \<Rightarrow> True
  | (i10, i24) \<Rightarrow> True
  | (i10, i25) \<Rightarrow> True
  | (i10, i26) \<Rightarrow> True
  | (i10, i27) \<Rightarrow> True
  | (i10, i28) \<Rightarrow> True
  | (i10, i29) \<Rightarrow> True
  | (i10, i30) \<Rightarrow> True
  | (i10, i31) \<Rightarrow> True
  | (i10, i32) \<Rightarrow> True
  | (i10, i33) \<Rightarrow> True

  | (i10, i11) \<Rightarrow> True
  | (i10, i10) \<Rightarrow> True
  | (i10, _) \<Rightarrow> False
  | (i11, i11) \<Rightarrow> True
  | (i11, i12) \<Rightarrow> True
  | (i11, i13) \<Rightarrow> True
  | (i11, i14) \<Rightarrow> True
  | (i11, i15) \<Rightarrow> True
  | (i11, i16) \<Rightarrow> True
  | (i11, i17) \<Rightarrow> True
  | (i11, i18) \<Rightarrow> True
  | (i11, i19) \<Rightarrow> True
  | (i11, i20) \<Rightarrow> True
  | (i11, i21) \<Rightarrow> True
  | (i11, i22) \<Rightarrow> True
  | (i11, i23) \<Rightarrow> True
  | (i11, i24) \<Rightarrow> True
  | (i11, i25) \<Rightarrow> True
  | (i11, i26) \<Rightarrow> True
  | (i11, i27) \<Rightarrow> True
  | (i11, i28) \<Rightarrow> True
  | (i11, i29) \<Rightarrow> True
  | (i11, i30) \<Rightarrow> True
  | (i11, i31) \<Rightarrow> True
  | (i11, i32) \<Rightarrow> True
  | (i11, i33) \<Rightarrow> True

  | (i11, _) \<Rightarrow> False
  | (i12, i12) \<Rightarrow> True
  | (i12, i13) \<Rightarrow> True
  | (i12, i14) \<Rightarrow> True
  | (i12, i15) \<Rightarrow> True
  | (i12, i16) \<Rightarrow> True
  | (i12, i17) \<Rightarrow> True
  | (i12, i18) \<Rightarrow> True
  | (i12, i19) \<Rightarrow> True
  | (i12, i20) \<Rightarrow> True
  | (i12, i21) \<Rightarrow> True
  | (i12, i22) \<Rightarrow> True
  | (i12, i23) \<Rightarrow> True
  | (i12, i24) \<Rightarrow> True
  | (i12, i25) \<Rightarrow> True
  | (i12, i26) \<Rightarrow> True
  | (i12, i27) \<Rightarrow> True
  | (i12, i28) \<Rightarrow> True
  | (i12, i29) \<Rightarrow> True
  | (i12, i30) \<Rightarrow> True
  | (i12, i31) \<Rightarrow> True
  | (i12, i32) \<Rightarrow> True
  | (i12, i33) \<Rightarrow> True

  | (i12, _) \<Rightarrow> False

  | (i13, i13) \<Rightarrow> True
  | (i13, i14) \<Rightarrow> True
  | (i13, i15) \<Rightarrow> True
  | (i13, i16) \<Rightarrow> True
  | (i13, i17) \<Rightarrow> True
  | (i13, i18) \<Rightarrow> True
  | (i13, i19) \<Rightarrow> True
  | (i13, i20) \<Rightarrow> True
  | (i13, i21) \<Rightarrow> True
  | (i13, i22) \<Rightarrow> True
  | (i13, i23) \<Rightarrow> True
  | (i13, i24) \<Rightarrow> True
  | (i13, i25) \<Rightarrow> True
  | (i13, i26) \<Rightarrow> True
  | (i13, i27) \<Rightarrow> True
  | (i13, i28) \<Rightarrow> True
  | (i13, i29) \<Rightarrow> True
  | (i13, i30) \<Rightarrow> True
  | (i13, i31) \<Rightarrow> True
  | (i13, i32) \<Rightarrow> True
  | (i13, i33) \<Rightarrow> True

  | (i13, _) \<Rightarrow> False

  | (i14, i14) \<Rightarrow> True
  | (i14, i15) \<Rightarrow> True
  | (i14, i16) \<Rightarrow> True
  | (i14, i17) \<Rightarrow> True
  | (i14, i18) \<Rightarrow> True
  | (i14, i19) \<Rightarrow> True
  | (i14, i20) \<Rightarrow> True
  | (i14, i21) \<Rightarrow> True
  | (i14, i22) \<Rightarrow> True
  | (i14, i23) \<Rightarrow> True
  | (i14, i24) \<Rightarrow> True
  | (i14, i25) \<Rightarrow> True
  | (i14, i26) \<Rightarrow> True
  | (i14, i27) \<Rightarrow> True
  | (i14, i28) \<Rightarrow> True
  | (i14, i29) \<Rightarrow> True
  | (i14, i30) \<Rightarrow> True
  | (i14, i31) \<Rightarrow> True
  | (i14, i32) \<Rightarrow> True
  | (i14, i33) \<Rightarrow> True

  | (i14, _) \<Rightarrow> False
  | (i15, i15) \<Rightarrow> True
  | (i15, i16) \<Rightarrow> True
  | (i15, i17) \<Rightarrow> True
  | (i15, i18) \<Rightarrow> True
  | (i15, i19) \<Rightarrow> True
  | (i15, i20) \<Rightarrow> True
  | (i15, i21) \<Rightarrow> True
  | (i15, i22) \<Rightarrow> True
  | (i15, i23) \<Rightarrow> True
  | (i15, i24) \<Rightarrow> True
  | (i15, i25) \<Rightarrow> True
  | (i15, i26) \<Rightarrow> True
  | (i15, i27) \<Rightarrow> True
  | (i15, i28) \<Rightarrow> True
  | (i15, i29) \<Rightarrow> True
  | (i15, i30) \<Rightarrow> True
  | (i15, i31) \<Rightarrow> True
  | (i15, i32) \<Rightarrow> True
  | (i15, i33) \<Rightarrow> True

  | (i15, _) \<Rightarrow> False

  | (i16, i16) \<Rightarrow> True
  | (i16, i17) \<Rightarrow> True
  | (i16, i18) \<Rightarrow> True
  | (i16, i19) \<Rightarrow> True
  | (i16, i20) \<Rightarrow> True
  | (i16, i21) \<Rightarrow> True
  | (i16, i22) \<Rightarrow> True
  | (i16, i23) \<Rightarrow> True
  | (i16, i24) \<Rightarrow> True
  | (i16, i25) \<Rightarrow> True
  | (i16, i26) \<Rightarrow> True
  | (i16, i27) \<Rightarrow> True
  | (i16, i28) \<Rightarrow> True
  | (i16, i29) \<Rightarrow> True
  | (i16, i30) \<Rightarrow> True
  | (i16, i31) \<Rightarrow> True
  | (i16, i32) \<Rightarrow> True
  | (i16, i33) \<Rightarrow> True

  | (i16, _) \<Rightarrow> False

  | (i17, i17) \<Rightarrow> True
  | (i17, i18) \<Rightarrow> True
  | (i17, i19) \<Rightarrow> True
  | (i17, i20) \<Rightarrow> True
  | (i17, i21) \<Rightarrow> True
  | (i17, i22) \<Rightarrow> True
  | (i17, i23) \<Rightarrow> True
  | (i17, i24) \<Rightarrow> True
  | (i17, i25) \<Rightarrow> True
  | (i17, i26) \<Rightarrow> True
  | (i17, i27) \<Rightarrow> True
  | (i17, i28) \<Rightarrow> True
  | (i17, i29) \<Rightarrow> True
  | (i17, i30) \<Rightarrow> True
  | (i17, i31) \<Rightarrow> True
  | (i17, i32) \<Rightarrow> True
  | (i17, i33) \<Rightarrow> True

  | (i17, _) \<Rightarrow> False

  | (i18, i18) \<Rightarrow> True
  | (i18, i19) \<Rightarrow> True
  | (i18, i20) \<Rightarrow> True
  | (i18, i21) \<Rightarrow> True
  | (i18, i22) \<Rightarrow> True
  | (i18, i23) \<Rightarrow> True
  | (i18, i24) \<Rightarrow> True
  | (i18, i25) \<Rightarrow> True
  | (i18, i26) \<Rightarrow> True
  | (i18, i27) \<Rightarrow> True
  | (i18, i28) \<Rightarrow> True
  | (i18, i29) \<Rightarrow> True
  | (i18, i30) \<Rightarrow> True
  | (i18, i31) \<Rightarrow> True
  | (i18, i32) \<Rightarrow> True
  | (i18, i33) \<Rightarrow> True

  | (i18, _) \<Rightarrow> False

  | (i19, i19) \<Rightarrow> True
  | (i19, i20) \<Rightarrow> True
  | (i19, i21) \<Rightarrow> True
  | (i19, i22) \<Rightarrow> True
  | (i19, i23) \<Rightarrow> True
  | (i19, i24) \<Rightarrow> True
  | (i19, i25) \<Rightarrow> True
  | (i19, i26) \<Rightarrow> True
  | (i19, i27) \<Rightarrow> True
  | (i19, i28) \<Rightarrow> True
  | (i19, i29) \<Rightarrow> True
  | (i19, i30) \<Rightarrow> True
  | (i19, i31) \<Rightarrow> True
  | (i19, i32) \<Rightarrow> True
  | (i19, i33) \<Rightarrow> True

  | (i19, _) \<Rightarrow> False

  | (i20, i20) \<Rightarrow> True
  | (i20, i21) \<Rightarrow> True
  | (i20, i22) \<Rightarrow> True
  | (i20, i23) \<Rightarrow> True
  | (i20, i24) \<Rightarrow> True
  | (i20, i25) \<Rightarrow> True
  | (i20, i26) \<Rightarrow> True
  | (i20, i27) \<Rightarrow> True
  | (i20, i28) \<Rightarrow> True
  | (i20, i29) \<Rightarrow> True
  | (i20, i30) \<Rightarrow> True
  | (i20, i31) \<Rightarrow> True
  | (i20, i32) \<Rightarrow> True
  | (i20, i33) \<Rightarrow> True

  | (i20, _) \<Rightarrow> False

  | (i21, i21) \<Rightarrow> True
  | (i21, i22) \<Rightarrow> True
  | (i21, i23) \<Rightarrow> True
  | (i21, i24) \<Rightarrow> True
  | (i21, i25) \<Rightarrow> True
  | (i21, i26) \<Rightarrow> True
  | (i21, i27) \<Rightarrow> True
  | (i21, i28) \<Rightarrow> True
  | (i21, i29) \<Rightarrow> True
  | (i21, i30) \<Rightarrow> True
  | (i21, i31) \<Rightarrow> True
  | (i21, i32) \<Rightarrow> True
  | (i21, i33) \<Rightarrow> True

  | (i21, _) \<Rightarrow> False

  | (i22, i22) \<Rightarrow> True
  | (i22, i23) \<Rightarrow> True
  | (i22, i24) \<Rightarrow> True
  | (i22, i25) \<Rightarrow> True
  | (i22, i26) \<Rightarrow> True
  | (i22, i27) \<Rightarrow> True
  | (i22, i28) \<Rightarrow> True
  | (i22, i29) \<Rightarrow> True
  | (i22, i30) \<Rightarrow> True
  | (i22, i31) \<Rightarrow> True
  | (i22, i32) \<Rightarrow> True
  | (i22, i33) \<Rightarrow> True

  | (i22, _) \<Rightarrow> False

  | (i23, i23) \<Rightarrow> True
  | (i23, i24) \<Rightarrow> True
  | (i23, i25) \<Rightarrow> True
  | (i23, i26) \<Rightarrow> True
  | (i23, i27) \<Rightarrow> True
  | (i23, i28) \<Rightarrow> True
  | (i23, i29) \<Rightarrow> True
  | (i23, i30) \<Rightarrow> True
  | (i23, i31) \<Rightarrow> True
  | (i23, i32) \<Rightarrow> True
  | (i23, i33) \<Rightarrow> True

  | (i23, _) \<Rightarrow> False

  | (i24, i24) \<Rightarrow> True
  | (i24, i25) \<Rightarrow> True
  | (i24, i26) \<Rightarrow> True
  | (i24, i27) \<Rightarrow> True
  | (i24, i28) \<Rightarrow> True
  | (i24, i29) \<Rightarrow> True
  | (i24, i30) \<Rightarrow> True
  | (i24, i31) \<Rightarrow> True
  | (i24, i32) \<Rightarrow> True
  | (i24, i33) \<Rightarrow> True

  | (i24, _) \<Rightarrow> False

  | (i25, i25) \<Rightarrow> True
  | (i25, i26) \<Rightarrow> True
  | (i25, i27) \<Rightarrow> True
  | (i25, i28) \<Rightarrow> True
  | (i25, i29) \<Rightarrow> True
  | (i25, i30) \<Rightarrow> True
  | (i25, i31) \<Rightarrow> True
  | (i25, i32) \<Rightarrow> True
  | (i25, i33) \<Rightarrow> True
  | (i25, _) \<Rightarrow> False

  | (i26, i26) \<Rightarrow> True
  | (i26, i27) \<Rightarrow> True
  | (i26, i28) \<Rightarrow> True
  | (i26, i29) \<Rightarrow> True
  | (i26, i30) \<Rightarrow> True
  | (i26, i31) \<Rightarrow> True
  | (i26, i32) \<Rightarrow> True
  | (i26, i33) \<Rightarrow> True
  | (i26, _) \<Rightarrow> False

  | (i27, i27) \<Rightarrow> True
  | (i27, i28) \<Rightarrow> True
  | (i27, i29) \<Rightarrow> True
  | (i27, i30) \<Rightarrow> True
  | (i27, i31) \<Rightarrow> True
  | (i27, i32) \<Rightarrow> True
  | (i27, i33) \<Rightarrow> True
  | (i27, _) \<Rightarrow> False

  | (i28, i28) \<Rightarrow> True
  | (i28, i29) \<Rightarrow> True
  | (i28, i30) \<Rightarrow> True
  | (i28, i31) \<Rightarrow> True
  | (i28, i32) \<Rightarrow> True
  | (i28, i33) \<Rightarrow> True
  | (i28, _) \<Rightarrow> False

  | (i29, i29) \<Rightarrow> True
  | (i29, i30) \<Rightarrow> True
  | (i29, i31) \<Rightarrow> True
  | (i29, i32) \<Rightarrow> True
  | (i29, i33) \<Rightarrow> True
  | (i29, _) \<Rightarrow> False

  | (i30, i30) \<Rightarrow> True
  | (i30, i31) \<Rightarrow> True
  | (i30, i32) \<Rightarrow> True
  | (i30, i33) \<Rightarrow> True
  | (i30, _) \<Rightarrow> False

  | (i31, i31) \<Rightarrow> True
  | (i31, i32) \<Rightarrow> True
  | (i31, i33) \<Rightarrow> True
  | (i31, _) \<Rightarrow> False

  | (i32, i32) \<Rightarrow> True
  | (i32, i33) \<Rightarrow> True
  | (i32, _) \<Rightarrow> False

  | (i33, i33) \<Rightarrow> True
  | (i33, _) \<Rightarrow> False
)
"

definition less_myvars where
  "x < y \<equiv> 
  (case (x,y) of 
    (i1, i1) \<Rightarrow> False 
  | (i1, _) \<Rightarrow> True
  | (i2, i1) \<Rightarrow> False
  | (i2, i2) \<Rightarrow> False
  | (i2, _) \<Rightarrow> True
  | (i3, i3) \<Rightarrow> False
  | (i3, i2) \<Rightarrow> False
  | (i3, i1) \<Rightarrow> False
  | (i3, _) \<Rightarrow> True
  | (i4, i4) \<Rightarrow> False
  | (i4, i3) \<Rightarrow> False
  | (i4, i2) \<Rightarrow> False
  | (i4, i1) \<Rightarrow> False
  | (i4, _) \<Rightarrow> True
  | (i5, i5) \<Rightarrow> False
  | (i5, i4) \<Rightarrow> False
  | (i5, i3) \<Rightarrow> False
  | (i5, i2) \<Rightarrow> False
  | (i5, i1) \<Rightarrow> False
  | (i5, _) \<Rightarrow> True
  | (i6, i6) \<Rightarrow> False
  | (i6, i5) \<Rightarrow> False
  | (i6, i4) \<Rightarrow> False
  | (i6, i3) \<Rightarrow> False
  | (i6, i2) \<Rightarrow> False
  | (i6, i1) \<Rightarrow> False
  | (i6, _) \<Rightarrow> True
  | (i7, i7) \<Rightarrow> False
  | (i7, i6) \<Rightarrow> False
  | (i7, i5) \<Rightarrow> False
  | (i7, i4) \<Rightarrow> False
  | (i7, i3) \<Rightarrow> False
  | (i7, i2) \<Rightarrow> False
  | (i7, i1) \<Rightarrow> False
  | (i7, _) \<Rightarrow> True
  | (i8, i8) \<Rightarrow> False
  | (i8, i7) \<Rightarrow> False
  | (i8, i6) \<Rightarrow> False
  | (i8, i5) \<Rightarrow> False
  | (i8, i4) \<Rightarrow> False
  | (i8, i3) \<Rightarrow> False
  | (i8, i2) \<Rightarrow> False
  | (i8, i1) \<Rightarrow> False
  | (i8, _) \<Rightarrow> True
  | (i9, i9) \<Rightarrow> False
  | (i9, i8) \<Rightarrow> False
  | (i9, i7) \<Rightarrow> False
  | (i9, i6) \<Rightarrow> False
  | (i9, i5) \<Rightarrow> False
  | (i9, i4) \<Rightarrow> False
  | (i9, i3) \<Rightarrow> False
  | (i9, i2) \<Rightarrow> False
  | (i9, i1) \<Rightarrow> False
  | (i9, _) \<Rightarrow> True
  | (i10, i10) \<Rightarrow> False
  | (i10, i9) \<Rightarrow> False
  | (i10, i8) \<Rightarrow> False
  | (i10, i7) \<Rightarrow> False
  | (i10, i6) \<Rightarrow> False
  | (i10, i5) \<Rightarrow> False
  | (i10, i4) \<Rightarrow> False
  | (i10, i3) \<Rightarrow> False
  | (i10, i2) \<Rightarrow> False
  | (i10, i1) \<Rightarrow> False
  | (i10, _) \<Rightarrow> True
  | (i11, i11) \<Rightarrow> False
  | (i11, i10) \<Rightarrow> False
  | (i11, i9) \<Rightarrow> False
  | (i11, i8) \<Rightarrow> False
  | (i11, i7) \<Rightarrow> False
  | (i11, i6) \<Rightarrow> False
  | (i11, i5) \<Rightarrow> False
  | (i11, i4) \<Rightarrow> False
  | (i11, i3) \<Rightarrow> False
  | (i11, i2) \<Rightarrow> False
  | (i11, i1) \<Rightarrow> False
  | (i11, _) \<Rightarrow> True

  | (i12, i12) \<Rightarrow> False
  | (i12, i11) \<Rightarrow> False
  | (i12, i10) \<Rightarrow> False
  | (i12, i9) \<Rightarrow> False
  | (i12, i8) \<Rightarrow> False
  | (i12, i7) \<Rightarrow> False
  | (i12, i6) \<Rightarrow> False
  | (i12, i5) \<Rightarrow> False
  | (i12, i4) \<Rightarrow> False
  | (i12, i3) \<Rightarrow> False
  | (i12, i2) \<Rightarrow> False
  | (i12, i1) \<Rightarrow> False
  | (i12, _) \<Rightarrow> True

  | (i13, i13) \<Rightarrow> False
  | (i13, i12) \<Rightarrow> False
  | (i13, i11) \<Rightarrow> False
  | (i13, i10) \<Rightarrow> False
  | (i13, i9) \<Rightarrow> False
  | (i13, i8) \<Rightarrow> False
  | (i13, i7) \<Rightarrow> False
  | (i13, i6) \<Rightarrow> False
  | (i13, i5) \<Rightarrow> False
  | (i13, i4) \<Rightarrow> False
  | (i13, i3) \<Rightarrow> False
  | (i13, i2) \<Rightarrow> False
  | (i13, i1) \<Rightarrow> False
  | (i13, _) \<Rightarrow> True

  | (i14, i14) \<Rightarrow> False
  | (i14, i13) \<Rightarrow> False
  | (i14, i12) \<Rightarrow> False
  | (i14, i11) \<Rightarrow> False
  | (i14, i10) \<Rightarrow> False
  | (i14, i9) \<Rightarrow> False
  | (i14, i8) \<Rightarrow> False
  | (i14, i7) \<Rightarrow> False
  | (i14, i6) \<Rightarrow> False
  | (i14, i5) \<Rightarrow> False
  | (i14, i4) \<Rightarrow> False
  | (i14, i3) \<Rightarrow> False
  | (i14, i2) \<Rightarrow> False
  | (i14, i1) \<Rightarrow> False
  | (i14, _) \<Rightarrow> True

  | (i15, i15) \<Rightarrow> False
  | (i15, i14) \<Rightarrow> False
  | (i15, i13) \<Rightarrow> False
  | (i15, i12) \<Rightarrow> False
  | (i15, i11) \<Rightarrow> False
  | (i15, i10) \<Rightarrow> False
  | (i15, i9) \<Rightarrow> False
  | (i15, i8) \<Rightarrow> False
  | (i15, i7) \<Rightarrow> False
  | (i15, i6) \<Rightarrow> False
  | (i15, i5) \<Rightarrow> False
  | (i15, i4) \<Rightarrow> False
  | (i15, i3) \<Rightarrow> False
  | (i15, i2) \<Rightarrow> False
  | (i15, i1) \<Rightarrow> False
  | (i15, _) \<Rightarrow> True

  | (i16, i16) \<Rightarrow> False
  | (i16, i15) \<Rightarrow> False
  | (i16, i14) \<Rightarrow> False
  | (i16, i13) \<Rightarrow> False
  | (i16, i12) \<Rightarrow> False
  | (i16, i11) \<Rightarrow> False
  | (i16, i10) \<Rightarrow> False
  | (i16, i9) \<Rightarrow> False
  | (i16, i8) \<Rightarrow> False
  | (i16, i7) \<Rightarrow> False
  | (i16, i6) \<Rightarrow> False
  | (i16, i5) \<Rightarrow> False
  | (i16, i4) \<Rightarrow> False
  | (i16, i3) \<Rightarrow> False
  | (i16, i2) \<Rightarrow> False
  | (i16, i1) \<Rightarrow> False
  | (i16, _) \<Rightarrow> True

  | (i17, i17) \<Rightarrow> False
  | (i17, i16) \<Rightarrow> False
  | (i17, i15) \<Rightarrow> False
  | (i17, i14) \<Rightarrow> False
  | (i17, i13) \<Rightarrow> False
  | (i17, i12) \<Rightarrow> False
  | (i17, i11) \<Rightarrow> False
  | (i17, i10) \<Rightarrow> False
  | (i17, i9) \<Rightarrow> False
  | (i17, i8) \<Rightarrow> False
  | (i17, i7) \<Rightarrow> False
  | (i17, i6) \<Rightarrow> False
  | (i17, i5) \<Rightarrow> False
  | (i17, i4) \<Rightarrow> False
  | (i17, i3) \<Rightarrow> False
  | (i17, i2) \<Rightarrow> False
  | (i17, i1) \<Rightarrow> False
  | (i17, _) \<Rightarrow> True

  | (i18, i18) \<Rightarrow> False
  | (i18, i17) \<Rightarrow> False
  | (i18, i16) \<Rightarrow> False
  | (i18, i15) \<Rightarrow> False
  | (i18, i14) \<Rightarrow> False
  | (i18, i13) \<Rightarrow> False
  | (i18, i12) \<Rightarrow> False
  | (i18, i11) \<Rightarrow> False
  | (i18, i10) \<Rightarrow> False
  | (i18, i9) \<Rightarrow> False
  | (i18, i8) \<Rightarrow> False
  | (i18, i7) \<Rightarrow> False
  | (i18, i6) \<Rightarrow> False
  | (i18, i5) \<Rightarrow> False
  | (i18, i4) \<Rightarrow> False
  | (i18, i3) \<Rightarrow> False
  | (i18, i2) \<Rightarrow> False
  | (i18, i1) \<Rightarrow> False
  | (i18, _) \<Rightarrow> True

  | (i19, i19) \<Rightarrow> False
  | (i19, i18) \<Rightarrow> False
  | (i19, i17) \<Rightarrow> False
  | (i19, i16) \<Rightarrow> False
  | (i19, i15) \<Rightarrow> False
  | (i19, i14) \<Rightarrow> False
  | (i19, i13) \<Rightarrow> False
  | (i19, i12) \<Rightarrow> False
  | (i19, i11) \<Rightarrow> False
  | (i19, i10) \<Rightarrow> False
  | (i19, i9) \<Rightarrow> False
  | (i19, i8) \<Rightarrow> False
  | (i19, i7) \<Rightarrow> False
  | (i19, i6) \<Rightarrow> False
  | (i19, i5) \<Rightarrow> False
  | (i19, i4) \<Rightarrow> False
  | (i19, i3) \<Rightarrow> False
  | (i19, i2) \<Rightarrow> False
  | (i19, i1) \<Rightarrow> False
  | (i19, _) \<Rightarrow> True

  | (i20, i20) \<Rightarrow> False
  | (i20, i19) \<Rightarrow> False
  | (i20, i18) \<Rightarrow> False
  | (i20, i17) \<Rightarrow> False
  | (i20, i16) \<Rightarrow> False
  | (i20, i15) \<Rightarrow> False
  | (i20, i14) \<Rightarrow> False
  | (i20, i13) \<Rightarrow> False
  | (i20, i12) \<Rightarrow> False
  | (i20, i11) \<Rightarrow> False
  | (i20, i10) \<Rightarrow> False
  | (i20, i9) \<Rightarrow> False
  | (i20, i8) \<Rightarrow> False
  | (i20, i7) \<Rightarrow> False
  | (i20, i6) \<Rightarrow> False
  | (i20, i5) \<Rightarrow> False
  | (i20, i4) \<Rightarrow> False
  | (i20, i3) \<Rightarrow> False
  | (i20, i2) \<Rightarrow> False
  | (i20, i1) \<Rightarrow> False
  | (i20, _) \<Rightarrow> True

  | (i21, i21) \<Rightarrow> False
  | (i21, i20) \<Rightarrow> False
  | (i21, i19) \<Rightarrow> False
  | (i21, i18) \<Rightarrow> False
  | (i21, i17) \<Rightarrow> False
  | (i21, i16) \<Rightarrow> False
  | (i21, i15) \<Rightarrow> False
  | (i21, i14) \<Rightarrow> False
  | (i21, i13) \<Rightarrow> False
  | (i21, i12) \<Rightarrow> False
  | (i21, i11) \<Rightarrow> False
  | (i21, i10) \<Rightarrow> False
  | (i21, i9) \<Rightarrow> False
  | (i21, i8) \<Rightarrow> False
  | (i21, i7) \<Rightarrow> False
  | (i21, i6) \<Rightarrow> False
  | (i21, i5) \<Rightarrow> False
  | (i21, i4) \<Rightarrow> False
  | (i21, i3) \<Rightarrow> False
  | (i21, i2) \<Rightarrow> False
  | (i21, i1) \<Rightarrow> False
  | (i21, _) \<Rightarrow> True

  | (i22, i22) \<Rightarrow> False
  | (i22, i21) \<Rightarrow> False
  | (i22, i20) \<Rightarrow> False
  | (i22, i19) \<Rightarrow> False
  | (i22, i18) \<Rightarrow> False
  | (i22, i17) \<Rightarrow> False
  | (i22, i16) \<Rightarrow> False
  | (i22, i15) \<Rightarrow> False
  | (i22, i14) \<Rightarrow> False
  | (i22, i13) \<Rightarrow> False
  | (i22, i12) \<Rightarrow> False
  | (i22, i11) \<Rightarrow> False
  | (i22, i10) \<Rightarrow> False
  | (i22, i9) \<Rightarrow> False
  | (i22, i8) \<Rightarrow> False
  | (i22, i7) \<Rightarrow> False
  | (i22, i6) \<Rightarrow> False
  | (i22, i5) \<Rightarrow> False
  | (i22, i4) \<Rightarrow> False
  | (i22, i3) \<Rightarrow> False
  | (i22, i2) \<Rightarrow> False
  | (i22, i1) \<Rightarrow> False
  | (i22, _) \<Rightarrow> True

  | (i23, i33) \<Rightarrow> True
  | (i23, i32) \<Rightarrow> True
  | (i23, i31) \<Rightarrow> True
  | (i23, i30) \<Rightarrow> True
  | (i23, i29) \<Rightarrow> True
  | (i23, i28) \<Rightarrow> True
  | (i23, i27) \<Rightarrow> True
  | (i23, i26) \<Rightarrow> True
  | (i23, i25) \<Rightarrow> True
  | (i23, i24) \<Rightarrow> True
  | (i23, _) \<Rightarrow> False

  | (i24, i33) \<Rightarrow> True
  | (i24, i32) \<Rightarrow> True
  | (i24, i31) \<Rightarrow> True
  | (i24, i30) \<Rightarrow> True
  | (i24, i29) \<Rightarrow> True
  | (i24, i28) \<Rightarrow> True
  | (i24, i27) \<Rightarrow> True
  | (i24, i26) \<Rightarrow> True
  | (i24, i25) \<Rightarrow> True
  | (i24, _) \<Rightarrow> False

  | (i25, i33) \<Rightarrow> True
  | (i25, i32) \<Rightarrow> True
  | (i25, i31) \<Rightarrow> True
  | (i25, i30) \<Rightarrow> True
  | (i25, i29) \<Rightarrow> True
  | (i25, i28) \<Rightarrow> True
  | (i25, i27) \<Rightarrow> True
  | (i25, i26) \<Rightarrow> True
  | (i25, _) \<Rightarrow> False

  | (i26, i33) \<Rightarrow> True
  | (i26, i32) \<Rightarrow> True
  | (i26, i31) \<Rightarrow> True
  | (i26, i30) \<Rightarrow> True
  | (i26, i29) \<Rightarrow> True
  | (i26, i28) \<Rightarrow> True
  | (i26, i27) \<Rightarrow> True
  | (i26, _) \<Rightarrow> False

  | (i27, i33) \<Rightarrow> True
  | (i27, i32) \<Rightarrow> True
  | (i27, i31) \<Rightarrow> True
  | (i27, i30) \<Rightarrow> True
  | (i27, i29) \<Rightarrow> True
  | (i27, i28) \<Rightarrow> True
  | (i27, _) \<Rightarrow> False

  | (i28, i33) \<Rightarrow> True
  | (i28, i32) \<Rightarrow> True
  | (i28, i31) \<Rightarrow> True
  | (i28, i30) \<Rightarrow> True
  | (i28, i29) \<Rightarrow> True
  | (i28, _) \<Rightarrow> False

  | (i29, i33) \<Rightarrow> True
  | (i29, i32) \<Rightarrow> True
  | (i29, i31) \<Rightarrow> True
  | (i29, i30) \<Rightarrow> True
  | (i29, _) \<Rightarrow> False

  | (i30, i33) \<Rightarrow> True
  | (i30, i32) \<Rightarrow> True
  | (i30, i31) \<Rightarrow> True
  | (i30, _) \<Rightarrow> False

  | (i31, i33) \<Rightarrow> True
  | (i31, i32) \<Rightarrow> True
  | (i31, _) \<Rightarrow> False

  | (i32, i33) \<Rightarrow> True
  | (i32, _) \<Rightarrow> False

  | (i33, _) \<Rightarrow> False
)
"

instance
  apply(standard)
  subgoal for x y   
    apply(cases x) 
      by((cases y, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+

  subgoal for x  by(cases x,auto simp add: less_eq_myvars_def)     

  subgoal for x y z   
    apply(cases x)
    subgoal by((cases y,(cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+)+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    subgoal apply(cases y) by((cases z, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    done
  subgoal for x y    apply(cases x)
      by((cases y, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
  subgoal for x y    apply(cases x)
      by((cases y, (auto simp add: less_myvars_def less_eq_myvars_def myvars.exhaust)))+
    done
end
 
  


definition max_str:"MAX_STR = 20"
typedef ident = "{s::string. size s \<le> MAX_STR}"
  morphisms Rep_ident Abs_ident
  apply(auto)
  apply(rule exI[where x=Nil])
  by(auto simp add: max_str)

(*definition trunc :: "string \<Rightarrow> string"
  where "trunc s \<equiv>  (if size s > MAX_STR then '''' else  s)"
lift_definition ident_of_str :: "string \<Rightarrow> ident" is trunc
  done

definition trunc :: "string \<Rightarrow> string"
  where "trunc s \<equiv>  (if size s > MAX_STR then '''' else  s)"
definition ident_of_str :: "string \<Rightarrow> ident"
 where "ident_of_str s \<equiv> Abs_ident (if size s > MAX_STR then '''' else  s)"
lift_definition ident_enum_ex::"(ident \<Rightarrow> bool) \<Rightarrow> bool" is string_enum_ex
  done
*)


(*definition ident_of_str :: "string \<Rightarrow> ident"
 where [code]:"ident_of_str s \<equiv> Abs_ident s"(*Abs_ident (if size s > MAX_STR then '''' else  s)*)
*)
definition cr_ident::"string \<Rightarrow> ident \<Rightarrow> bool"
  where "cr_ident x y \<equiv> Abs_ident x = y"

lemma Quotient_ident:
  "Quotient (\<lambda> x y. x = y \<and> size x \<le> MAX_STR) Abs_ident Rep_ident cr_ident"
  sorry

lemma reflp_ident: "reflp (\<lambda>x y. x = y \<and> size x \<le> MAX_STR)"
  sorry

setup_lifting  Quotient_ident reflp_ident

instantiation ident :: finite begin
instance proof 
  have any:"\<forall>i::nat. card {s::string. size s \<le> i} > 0"
    apply(auto)
    subgoal for i
  proof (induct i)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    assume IH:"card {s::string. size s \<le> k} > 0"
    have "card {s::string. size s \<le> Suc k} = card (UNIV:: char set) * card {s::string. size s \<le> Suc k}"
      sorry
    then show ?case sorry
  qed
  done        
  then have any:"\<forall>i::nat. finite {s::string. size s \<le> i}"
    using card_ge_0_finite by blast
  then show "finite (UNIV:: ident set)"
    by (metis Abs_ident_cases ex_new_if_finite finite_imageI image_eqI)
qed
end

instantiation char :: linorder begin
definition less_eq_char where
[code]:"less_eq_char x  y \<equiv> int_of_char x \<le> int_of_char y"
definition less_char where
[code]:"less_char x y \<equiv> int_of_char x < int_of_char y"
instance
  by(standard, auto simp add: less_char_def less_eq_char_def int_of_char_def)+
end

instantiation ident :: linorder begin
fun lleq :: "char list \<Rightarrow> char list \<Rightarrow> bool"
  where 
  [code]:"lleq Nil Nil = True"
| [code]:"lleq Nil _ = True"
| [code]:"lleq _ Nil = False"
| [code]:"lleq (x # xs)(y # ys) = 
   (if x = y then lleq xs ys else x < y)"

lift_definition less_eq_ident::"ident \<Rightarrow> ident \<Rightarrow> bool" is lleq sorry

(*fun less_eq_ident :: "ident \<Rightarrow> ident \<Rightarrow> bool"
  where [code]:"less_eq_ident X Y = lleq (Rep_ident X) (Rep_ident Y)"*)
instance
  apply(standard, auto simp add: )
        prefer 4
  subgoal for x
    apply(induction "Rep_ident x")
(*    subgoal by auto*)
(*    subgoal for y ys*)
      sorry
    sorry
(*    done
  sorry*)
end

lift_definition ident_empty::ident is "''''" done
lift_definition ident_cons::"char \<Rightarrow> ident \<Rightarrow> ident" is "(#)" sorry


fun ident_upto :: "nat \<Rightarrow> ident list"
  where 
  "ident_upto n = 
(if n = 0 then
  ident_empty # Nil
else if n > 0 then
 (let k = n - 1 in
   let r = ident_upto k in
    let ab =  String.enum_char_inst.enum_char in
    concat (map (\<lambda> c. map (\<lambda>s. ident_cons c  s) r) ab))
else Nil)"

lift_definition x::ident is "''x''::string"  
  done
lift_definition y::ident is "''y''::string"
  done
lift_definition z::ident is "''z''::string"
  done
lift_definition w::ident is "''w''::string"
  done

(*lift_definition (code_dt) ident_upto::"nat \<Rightarrow> ident list" is "str_upto::nat \<Rightarrow> string list"*)
code_thms ident_upto
print_theorems

(*definition vals_inner_def[code]:"vals_inner \<equiv> str_upto MAX_STR"*)
definition vals_def[code]:"vals \<equiv> ident_upto MAX_STR"
export_code vals in Scala


definition ident_enum :: "ident list" 
  where "ident_enum = vals"
definition ident_enum_all :: "(ident \<Rightarrow> bool) \<Rightarrow> bool"
  where "ident_enum_all = (\<lambda> f. list_all f vals)"
definition ident_enum_ex :: "(ident \<Rightarrow> bool) \<Rightarrow> bool"
  where "ident_enum_ex = (\<lambda> f. list_ex f vals)"
(*
lift_definition ident_enum::"ident list" is string_enum
  done
lift_definition ident_enum_all::"(ident \<Rightarrow> bool) \<Rightarrow> bool" is string_enum_all
  done
lift_definition ident_enum_ex::"(ident \<Rightarrow> bool) \<Rightarrow> bool" is string_enum_ex
  done
*)
instantiation ident :: enum begin
definition enum_ident 
  where enum_ident_def[code]:"enum_ident \<equiv> ident_enum"
definition enum_all_ident
  where enum_all_ident[code]:"enum_all_ident \<equiv> ident_enum_all"
definition enum_ex_ident
  where enum_ex_ident[code]:"enum_ex_ident \<equiv> ident_enum_ex"
instance 
  apply(standard)
     apply(auto)
  sorry
end
export_code ident_enum_ex in Scala
(*export_code enum_ident_inst.enum_all_ident in Scala*)
instantiation ident :: equal begin
definition equal_ident :: "ident \<Rightarrow> ident \<Rightarrow> bool"
  where [code]:"equal_ident X Y = (X \<le> Y \<and> Y \<le> X)"
instance
  sorry
end


inductive is_i1::"ident \<Rightarrow> bool"
  where i1_is_i1:"is_i1 x"
(*
definition x::myvars where "x = i1"
definition y::myvars where "y = i2"
definition z::myvars where "z = i3"
definition w::myvars where "w = i4"

inductive is_i1::"myvars \<Rightarrow> bool"
  where i1_is_i1:"is_i1 i1"*)

global_interpretation ddl:ids x y z "is_i1" x y z x y z w
  defines ddl_pt_result = "ddl.pt_result"
  and ddl_rule_result = "ddl.rule_result"
  and ddl_start_proof = "ddl.start_proof"
  and ddl_RightRule_result = "ddl.RightRule_result"
  and ddl_LeftRule_result = "ddl.LeftRule_result"
  and ddl_merge_rules = "ddl.merge_rules"
  and ddl_get_axrule = "ddl.get_axrule"
  and ddl_pro = "ddl.pro"
  and ddl_fnc = "ddl.fnc"
  and ddl_Radmit = "ddl.Radmit"
  and ddl_Sadmit = "ddl.Sadmit"
  and ddl_Rsubst = "ddl.Rsubst"
  and ddl_Ssubst = "ddl.Ssubst"
  and ddl_TUrename = "ddl.TUrename"
  and ddl_PUrename = "ddl.PUrename"
  and ddl_swap = "ddl.swap"
  and ddl_SUrename = "ddl.SUrename"
  and ddl_SBrename = "ddl.SBrename"
  and ddl_FUrename = "ddl.FUrename"
  and ddl_OUrename = "ddl.OUrename"
  and ddl_FBrename = "ddl.FBrename"
  and ddl_is_singleton = "ddl.is_singleton"
  and ddl_sing_at = "ddl.sing_at"
  and ddl_ssafe = "ddl.ssafe"

  and ddl_singleton = "ddl.singleton"
  and ddl_get_axiom = "ddl.get_axiom"
  and ddl_p1 = "ddl.p1"
  and ddl_f1 = "ddl.f1"
  and ddl_P = "ddl.P"  

  and ddl_diff_times_axiom = "ddl.diff_times_axiom"
  and ddl_diff_const_axiom = "ddl.diff_const_axiom"
  and ddl_diff_plus_axiom = "ddl.diff_plus_axiom"
  and ddl_DIGeqaxiom = ddl.DIGeqaxiom
  and ddl_DIGraxiom =  ddl.DIGraxiom
  and ddl_DWaxiom =  ddl.DWaxiom
  and ddl_DSaxiom =  ddl.DSaxiom
  and ddl_DGaxiom =  ddl.DGaxiom
  and ddl_DEaxiom =  ddl.DEaxiom
  and ddl_DCaxiom =  ddl.DCaxiom
  and ddl_loop_iterate_axiom =  ddl.loop_iterate_axiom
  and ddl_diff_assign_axiom =  ddl.diff_assign_axiom
  and ddl_choice_axiom =   ddl.choice_axiom
  and ddl_assign_axiom =   ddl.assign_axiom
  and ddl_test_axiom =   ddl.test_axiom
  and ddl_box_axiom =   ddl.box_axiom
  and ddl_Vaxiom =   ddl.Vaxiom
  and ddl_Kaxiom =  ddl.Kaxiom
  and ddl_Iaxiom =  ddl.Iaxiom
  and ddl_CTaxrule = ddl.CTaxrule
  and ddl_CQaxrule = ddl.CQaxrule
  and ddl_CEaxrule = ddl.CEaxrule 
  and ddl_Gaxrule = ddl.Gaxrule
  and ddl_state_fun = ddl.state_fun
  and ddl_constFcongAxiom = ddl.constFcongAxiom
  and ddl_DiffLinearAxiom = ddl.DiffLinearAxiom
  and ddl_compose_axiom = ddl.compose_axiom
  and ddl_assignEqAxiom = ddl.assignEqAxiom
  and ddl_BoxSplitAxiom = ddl.BoxSplitAxiom
  and ddl_allInstAxiom = ddl.allInstAxiom
  and ddl_ImpSelfAxiom = ddl.ImpSelfAxiom
  and ddl_AllElimAxiom = ddl.AllElimAxiom
  and ddl_dMinusAxiom = ddl.dMinusAxiom
  and ddl_diamondModusPonensAxiom = ddl.diamondModusPonensAxiom
  and ddl_lessEqualReflAxiom = ddl.lessEqualReflAxiom
  and ddl_equalReflAxiom = ddl.equalReflAxiom
  and ddl_TrueImplyAxiom = ddl.TrueImplyAxiom
  and ddl_composedAxiom = ddl.composedAxiom
  and ddl_randomdAxiom = ddl.randomdAxiom
  and ddl_diamondAxiom = ddl.diamondAxiom
  and ddl_choicedAxiom = ddl.choicedAxiom
  and ddl_assigndAxiom = ddl.assigndAxiom
  and ddl_testdAxiom = ddl.testdAxiom

  and ddl_f0 = ddl.f0

  and ddl_diff_var_axiom = "ddl.diff_var_axiom"
  and ddl_EquivReflexiveAxiom = "ddl.EquivReflexiveAxiom"
  and ddl_DiffEffectSysAxiom = "ddl.DiffEffectSysAxiom"
  and ddl_monbrule = "ddl.monbrule"
 and ddl_join = "ddl.join"
 and ddl_vid_to_string = "ddl.vid_to_string"
 and  ddl_oid_to_string = "ddl.oid_to_string"
 and ddl_cid_to_string = "ddl.cid_to_string"
 and ddl_ppid_to_string = "ddl.ppid_to_string"
 and ddl_hpid_to_string = "ddl.hpid_to_string"
 and ddl_fid_to_string = "ddl.fid_to_string"
and ddl_trm_to_string = "ddl.trm_to_string"
and ddl_ode_to_string = "ddl.ode_to_string"
and ddl_fml_to_string = "ddl.fml_to_string"
 and ddl_hp_to_string = "ddl.hp_to_string"
and ddl_seq_to_string = "ddl.seq_to_string"
and ddl_rule_to_string = "ddl.rule_to_string"
and ddl_Oadmit = "ddl.Oadmit"
and ddl_Fadmit = "ddl.Fadmit"
and ddl_TRadmit = "ddl.TRadmit"
and ddl_FRadmit = "ddl.FRadmit"
and ddl_assignAnyAxiom = "ddl.assignAnyAxiom"
and ddl_equalCommuteAxiom = "ddl.equalCommuteAxiom"
and ddl_Rsafe = "ddl.Rsafe"
  apply(standard, auto simp add: x_def y_def z_def w_def is_i1.intros)
  sorry


    
declare 
ddl.pt_result.simps[code_pred_simp]  
ddl.rule_result.simps[code_pred_simp] 
ddl.start_proof.simps[code_pred_simp] 
singleton_def[code_pred_simp]
ddl.get_axiom.simps[code_pred_simp]
ddl.p1_def[code_pred_simp]
ddl.f1_def[code_pred_simp]
ddl.P_def[code_pred_simp]  
singleton_def[code_pred_simp]
Syntax.hpsafe_fsafe.intros[code_pred_intro]
Syntax.osafe.intros[code_pred_intro]
Syntax.dsafe.intros[code_pred_intro]
Syntax.dfree.intros[code_pred_intro]
ddl.Oadmit.intros[code_pred_intro]
ddl.Padmit_Fadmit.intros[code_pred_intro]
ddl.TRadmit.intros[code_pred_intro]
ddl.PRadmit_FRadmit.intros[code_pred_intro]

Syntax.hpsafe_fsafe.intros[code_pred_intro]
Syntax.osafe.intros[code_pred_intro]
Syntax.dsafe.intros[code_pred_intro]
Syntax.dfree.intros[code_pred_intro]


declare 
(*ddl.is_singleton.intros[code_pred_intro]
ddl.sing_at.intros[code_pred_intro]*)
is_i1.intros[code_pred_intro]


code_pred (modes: i \<Rightarrow> bool as is1_i) "is_i1"
by (rule is_i1.cases)

(*code_pred (modes: i \<Rightarrow> i  \<Rightarrow> i \<Rightarrow> bool as sing_at_i) "ddl_sing_at"
  by(rule ddl.sing_at.cases)

code_pred (modes: o \<Rightarrow> i \<Rightarrow> bool as is_singleton_i) "ddl_is_singleton"
  by(rule ddl.is_singleton.cases)*)

code_pred "Syntax.dfree"  using Syntax.dfree.cases by metis
code_pred "Syntax.osafe"  using Syntax.osafe.cases by metis
code_pred "Syntax.fsafe"  
  apply(rule Syntax.fsafe.cases[of xa thesis]) 
           apply blast+
  apply(rule hpsafe.cases)
           apply blast+
  apply(rule dsafe.cases)
         apply blast+
  done


code_pred "ddl_TRadmit" apply(rule ddl.TRadmit.cases) by(auto)
code_pred  (modes: i \<Rightarrow>  bool as fradmit_i) "ddl_FRadmit"
   apply(rule ddl.FRadmit.cases)
         apply(auto)
  apply(rule ddl.PRadmit.cases)
          apply(auto)
  done


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as oadmit_i) "ddl_Oadmit"
  apply(rule ddl.Oadmit.cases)
      apply(auto)
  done

code_pred (modes: i \<Rightarrow> i \<Rightarrow>  bool as fadmit_i) "ddl_Fadmit"
  apply(rule ddl.Fadmit.cases)
            apply(auto)
  apply(rule ddl.Padmit.cases)
  by(auto)
    
(*

definition ssafe ::"('sf, 'sc, 'sz) subst \<Rightarrow> bool"
where "ssafe \<sigma> \<equiv>
  (\<forall> i. case SFunctions \<sigma> i  of Some f' \<Rightarrow> dfree f' | None \<Rightarrow> True) \<and> 
  (\<forall> f. case SPredicates \<sigma> f of Some f' \<Rightarrow> fsafe f' | None \<Rightarrow> True) \<and>
  (\<forall> F. case SFunls \<sigma> F of Some f' \<Rightarrow> dsafe f' | None \<Rightarrow> True) \<and>
  (\<forall> f. case SPrograms \<sigma> f   of Some f' \<Rightarrow> hpsafe f'| None \<Rightarrow> True) \<and>
  (\<forall> f sp. case SODEs \<sigma> f sp  of Some f' \<Rightarrow> osafe f' | None \<Rightarrow> True) \<and>
  (\<forall> f x. case SODEs \<sigma> f (Some x)  of Some f' \<Rightarrow> Inl x \<notin> BVO f' | None \<Rightarrow> True) \<and>
  (\<forall> C. case SContexts \<sigma> C   of Some C' \<Rightarrow> fsafe C' | None \<Rightarrow> True)"
*)

(*lemma [code abstype]: "Abs_ident (Rep_ident a) = a" 
  sorry*)
(*lemma [code]:"ident_of_str (s) \<equiv> Abs_ident (if size ( s) > MAX_STR then '''' else  ( s))"
  sorry*)

(*
definition string_enum :: "string list" 
  where "string_enum = vals_inner"
definition string_enum_all :: "(string \<Rightarrow> bool) \<Rightarrow> bool"
  where "string_enum_all = (\<lambda> f. list_all f vals_inner)"
definition string_enum_ex :: "(string \<Rightarrow> bool) \<Rightarrow> bool"
  where "string_enum_ex = (\<lambda> f. list_ex f vals_inner)"

lift_definition ident_enum::"ident list" is string_enum
  done
lift_definition ident_enum_all::"(ident \<Rightarrow> bool) \<Rightarrow> bool" is string_enum_all
  done
lift_definition ident_enum_ex::"(ident \<Rightarrow> bool) \<Rightarrow> bool" is string_enum_ex
  done
*)
(*lemma [code]: "enum_ident_inst.enum_all_ident = ident_enum_all"
  sorry*)

export_code "ident_upto" in Scala

export_code "ddl_ssafe" in Scala
export_code "ddl_start_proof" in Scala
  code_pred (modes: i \<Rightarrow> i \<Rightarrow> bool as fadmit_i) "ddl.Fadmit" 
  done

export_code "ddl_pt_result" in Scala


export_code ddl_rule_to_string in Scala

(* 
subsection \<open>Implementation of Polynomial Mappings as Association Lists\<close>

lift_definition Pm_fmap::"('a, 'b::zero) fmap \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b" is lookup0
  by (rule finite_lookup_default)

lemmas [simp] = Pm_fmap.rep_eq

code_datatype Pm_fmap

lemma PM_clearjunk0_cong:
  "Pm_fmap (clearjunk0 xs) = Pm_fmap xs"
  by (metis Pm_fmap.rep_eq lookup0_clearjunk0 poly_mapping_eqI)

*)

(*definition "blerh =  (\<chi> i::3. ((5)::real))"
export_code blerh in Scala*)

end