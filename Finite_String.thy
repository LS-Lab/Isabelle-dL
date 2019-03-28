theory "Finite_String"
  imports 
    Main 
    "HOL-Library.Code_Target_Int"
begin

definition max_str:"MAX_STR = 20"
typedef ident = "{s::string. size s \<le> MAX_STR}"
  morphisms Rep_ident Abs_ident
  apply(auto)
  apply(rule exI[where x=Nil])
  by(auto simp add: max_str)

setup_lifting  Finite_String.ident.type_definition_ident 

lemma cardiB:
  fixes C:: "char set" and S::"string set"
  assumes C:"card C \<ge> 1" and S:"card S \<ge> 0"
  shows "card C * card S \<ge> card S"
  using C S by auto

fun cons :: "('a * 'a list) \<Rightarrow> 'a list" 
  where "cons (x,y) = x # y"
instantiation ident :: finite begin
instance proof 
  have any:"\<forall>i::nat. card {s::string. length s \<le> i} > 0"
    apply(auto)
    subgoal for i
  proof (induct i)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    assume IH:"card {s::string. length s \<le> k} > 0"
    let ?c = "(UNIV::char set)"
    let ?ih = "{s::string. length s \<le> k}"
    let ?prod = "(?c \<times> ?ih)"
    let ?b = "(cons ` ?prod)"
    let ?A = "{s::string. length s \<le> Suc k}"
    let ?B = "insert [] ?b"

    have IHfin:"finite ?ih" using IH card_ge_0_finite by blast
    have finChar:"finite ?c" using card_ge_0_finite finite_code by blast
    have finiteProd:"finite ?prod"
      using Groups_Big.card_cartesian_product IHfin finChar by auto
    have cardCons:"card ?b = card ?prod"
      apply(rule Finite_Set.card_image)
      by(auto simp add: inj_on_def) 
    have finiteCons:"finite ?b" using cardCons finiteProd card_ge_0_finite by blast
    have finiteB:"finite ?B" using finite_insert finiteCons by auto
    have lr:"\<And>x. x \<in> ?A \<Longrightarrow> x \<in> ?B" subgoal for x
        apply(auto) apply(cases x) apply auto 
        by (metis UNIV_I cons.simps image_eqI mem_Collect_eq mem_Sigma_iff) done
    have rl:"\<And>x. x \<in> ?B \<Longrightarrow> x \<in> ?A" subgoal for x
        by(auto) done
    have isCons:"?A = ?B"
      using lr rl by auto
  show ?case
      using finiteB isCons IH by (simp add: card_insert)
  qed
  done 
    note finMax = card_ge_0_finite[OF spec[OF any, of MAX_STR]]
    have finWow:"finite {x | x y . x = Abs_ident y \<and> y \<in> {s. length s \<le> MAX_STR} }"
      using Abs_ident_cases finMax by auto
    have univEq:"(UNIV::ident set) = {x | x y . x = Abs_ident y \<and> y \<in> {s. length s \<le> MAX_STR} }"
      using Abs_ident_cases  
      by (metis (mono_tags, lifting) Collect_cong UNIV_I top_empty_eq top_set_def)
    then have "finite (UNIV :: ident set)" using univEq finWow by auto
  then show "finite (UNIV::ident set)" by auto
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
  "lleq Nil Nil = True"
| "lleq Nil _ = True"
| "lleq _ Nil = False"
| "lleq (x # xs)(y # ys) = 
   (if x = y then lleq xs ys else x < y)"

lift_definition less_eq_ident::"ident \<Rightarrow> ident \<Rightarrow> bool" is lleq done

(*fun less_eq_ident :: "ident \<Rightarrow> ident \<Rightarrow> bool"
  where [code]:"less_eq_ident X Y = lleq (Rep_ident X) (Rep_ident Y)"*)
instance
  apply(standard, auto simp add:)
        prefer 4
  subgoal for x
    apply(induction "Rep_ident x")
(*    subgoal by auto*)
(*    subgoal for y ys*)
      sorry
    sorry
end

fun string_expose::"string \<Rightarrow> (unit + (char * string))"
  where "string_expose Nil = Inl ()"
  | "string_expose (c#cs) = Inr(c,cs)"

fun string_cons::"char \<Rightarrow> string \<Rightarrow> string"
  where "string_cons c s = (if length s \<ge> MAX_STR then s else c # s)" 

lift_definition ident_empty::ident is "''''" by(auto simp add: max_str)
lift_definition ident_cons::"char \<Rightarrow> ident \<Rightarrow> ident" is "string_cons" by auto
lift_definition ident_expose::"ident \<Rightarrow> (unit + (char*ident))" is string_expose 
  by (smt dual_order.trans le_add_same_cancel1 lessI less_imp_le list.size(4) pred_prod_inject pred_sum.simps string_expose.elims top1I)
(*  apply(auto)
  by (smt ge_eq_refl order_refl prod.rel_eq prod.rel_mono reflp_ge_eq reflp_ident sum.rel_eq sum.rel_mono)*)


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

lift_definition Ix::ident is "''$x''::string"   apply(auto simp add: max_str)
  done
lift_definition Iy::ident is "''$y''::string"apply(auto simp add: max_str)
  done
lift_definition Iz::ident is "''$z''::string"apply(auto simp add: max_str)
  done
lift_definition Iw::ident is "''$w''::string"apply(auto simp add: max_str)
  done

definition [simp]:"fid1 =  Ix"
definition [simp]:"pid1 =  Ix"
definition [simp]:"vid1 =  Ix"

definition [simp]:"fid2 =  Iy"
definition [simp]:"pid2 =  Iy"
definition [simp]:"vid2 =  Iy"

definition [simp]:"fid3 =  Iz"
definition [simp]:"pid3 =  Iz"
definition [simp]:"vid3 =  Iz"

definition [simp]:"fid4 =  Iw"
definition [simp]:"pid4 =  Iw"
definition [simp]:"vid4 =  Iw"

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
  apply(standard)
  by(auto simp add: equal_ident_def)
end


definition "FSENTINEL = ''.''"
definition "CSENTINEL = ''_''"
definition "SSENTINEL = ''$''"
definition "FSENT = hd FSENTINEL"
definition "CSENT = hd CSENTINEL"
definition "SSENT = hd SSENTINEL"

fun args_to_id::"ident \<Rightarrow> (ident + ident) option"
  where "args_to_id z = 
      (case (ident_expose z) of 
       Inl _ \<Rightarrow> None
     | Inr (x,xs) \<Rightarrow> (if x = FSENT then Some (Inr xs) else if x = SSENT then Some (Inl xs) else None))"

(*fun arg_to_id::"ident \<Rightarrow> (ident + unit) option"
  where "arg_to_id  z = 
      (case (ident_expose z) of 
       Inl _ \<Rightarrow> None
     | Inr (x,xs) \<Rightarrow> (if x = CSENT then Some (Inr ()) else if x = SSENT then Some (Inl xs) else None))"
*)
fun debase :: "ident \<Rightarrow> ident"
  where "debase f = ident_cons FSENT f"
fun Debase :: "ident \<Rightarrow> ident"
  where "Debase f = ident_cons SSENT f"
fun rebase :: "ident \<Rightarrow> ident"
  where "rebase f = (case ident_expose f of Inl () \<Rightarrow> f | Inr (c,cs) \<Rightarrow> cs)"
fun is_base :: "ident \<Rightarrow> bool"
  where "is_base f = (case (ident_expose f) of Inl () \<Rightarrow> True | Inr(c,cs) \<Rightarrow> c \<noteq> FSENT)"
fun nonbase :: "ident \<Rightarrow> bool"
  where "nonbase f = (case (ident_expose f) of Inl () \<Rightarrow> False | Inr(c,cs) \<Rightarrow> c = FSENT \<or> c = SSENT)"

lift_definition ilength::"ident \<Rightarrow> nat" is length done


lemma nonbase_nonemp:"(nonbase x) \<Longrightarrow> x \<noteq> ident_empty" 
  apply(auto simp add: FSENT_def SSENT_def ident_empty_def)
  by (metis (mono_tags, lifting) id_apply ident_empty.rep_eq ident_empty_def ident_expose_def map_fun_apply map_sum.simps(1) old.sum.simps(5) old.unit.case string_expose.simps(1))

lemma nonbase_debase:
  assumes spacious:"MAX_STR > ilength a"
  shows "nonbase (debase a)"
  using spacious 
  by(auto simp add: ident_cons_def Rep_ident_inverse ilength_def ident_expose_def Abs_ident_inverse) 

lemma nonbase_some:
  assumes nb:"nonbase x"
  obtains inj where "args_to_id x = Some inj"
  using nb apply auto
  apply(cases "ident_expose x")
  apply (simp add: case_unit_Unity)+
  by fastforce

lemma arg_lengthR:
  assumes ai:"args_to_id x = Some(Inr y)"
  shows "ilength y + 1 = ilength x"
  using ai apply(auto)
  apply(cases "ident_expose x")
   apply(auto)
  subgoal for a b
    apply(cases "a = FSENT")
     apply(auto simp add: ilength_def ident_expose_def)
     apply(cases "string_expose (Rep_ident x)")
      apply(auto)
    apply (metis (no_types, lifting) Inl_Inr_False Inr_inject Rep_ident eq_onp_same_args ilength.abs_eq ilength.rep_eq impossible_Cons le_cases le_trans length_Suc_conv mem_Collect_eq snd_conv string_expose.elims)
    apply(cases "a = SSENT")
    by(auto simp add: ilength_def ident_expose_def)
  done

lemma arg_lengthL:
  assumes ai:"args_to_id x = Some(Inl y)"
  shows "ilength y + 1 = ilength x"
  using ai apply(auto)
  apply(cases "ident_expose x")
   apply(auto)
  subgoal for a b
    apply(cases "a = FSENT")
     apply(auto simp add: ilength_def ident_expose_def)
     apply(cases "string_expose (Rep_ident x)")
      apply(auto)
    apply(cases "a = SSENT")
    apply(auto simp add: FSENT_def SSENT_def FSENTINEL_def SSENTINEL_def)
    using Inl_Inr_False Inl_inject Rep_ident eq_onp_same_args ilength.abs_eq ilength.rep_eq impossible_Cons le_cases le_trans length_Suc_conv mem_Collect_eq snd_conv string_expose.elims
    by (metis Inr_inject)
  done
lemma arg_debaseL:
  assumes spacious:"MAX_STR > ilength a"
  assumes ai:"args_to_id x = Some (Inl a)"
  shows "x = Debase a"
proof -
  show ?thesis
  proof (cases "ident_expose x")
    case (Inl c) then have xc:" ident_expose x = Inl c" by auto
    then show ?thesis  apply (auto)
    proof (cases "ident_expose a")
      case (Inl d)
      then show "x = ident_cons SSENT a"
        apply(auto simp add: ident_expose_def ident_cons_def)
        using Inl_Inr_False Rep_ident_inverse ident_empty.abs_eq map_sum.simps(2) nonbase_nonemp 
              string_expose.elims ilength.rep_eq spacious apply auto
        using ai xc by auto
    next
      case (Inr e) then have xe:" ident_expose a = Inr e" by auto
      have contra:"ident_expose x = Inl () \<Longrightarrow> False"
         unfolding nonbase.simps
        using case_unit_Unity ai by auto
      from xe show "x = ident_cons SSENT a" 
        using xc apply(auto)
        using contra by auto
    qed
  next
    case (Inr b)
    then obtain c cs where cs:"ident_expose x = Inr(c,cs)"
      apply auto
      unfolding ident_expose_def
      using old.prod.exhaust by blast
    have hd:"c = SSENT"
      using ai apply(simp)
      using cs apply(simp)
      apply(cases "c = FSENT") apply(auto)
      apply(cases "c = SSENT") by auto 
    then show ?thesis
    proof (cases "ident_expose (debase a)")
      case (Inl e) then have xe:" ident_expose (debase a) = Inl e" by auto
       note nbb = nonbase_debase[of a, OF spacious]
      have contra:"\<And>x. ident_expose (debase a) = Inl x \<Longrightarrow> False"
        using nbb unfolding nonbase.simps
        by (simp add: case_unit_Unity)
      show "?thesis" 
        using contra[OF xe] by auto
    next
      case (Inr e) then have xe:" ident_expose (debase a) = Inr e" by auto
      then obtain d ds where ds:"ident_expose (debase a) = Inr(d,ds)"
        apply auto
        using old.prod.exhaust by blast
      from spacious
      have fact:"MAX_STR > length (Rep_ident a)"
        unfolding ilength_def by auto
      have ied:"ident_expose (debase a) = Inr (FSENT, cs)"
        using cs fact ai
        apply(auto simp add:  ident_expose_def ident_cons_def Rep_ident_inverse[of a] Abs_ident_inverse fact)
        using fact apply linarith+
        apply(cases "c = SSENT")
        using hd  by (auto simp add: hd FSENT_def SSENT_def FSENTINEL_def SSENTINEL_def)
        have cd:"cs = ds" 
          using ied cs ds by auto
      have "Rep_ident x = SSENT # Rep_ident ds"
        using cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs)
        unfolding ident_expose_def ident_cons_def
        using cs ds
        apply(auto simp add: ident_expose_def ident_cons_def Rep_ident_inverse)
        apply(cases "MAX_STR \<le> length (Rep_ident a)")
        using fact cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs )
        apply(cases "string_expose (Rep_ident x)")
        using cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs )
          apply(cases "Rep_ident x")
         apply(auto simp add: hd)
        subgoal for bb
        using Rep_ident_inverse[of ds] Abs_ident_inverse[of bb]  cd fact apply auto
        by (metis Rep_ident impossible_Cons le_cases le_trans mem_Collect_eq)
      done
      then show "x = Debase a"
        using cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs)
        unfolding ident_expose_def ident_cons_def
        using cs ds
        apply(auto simp add: ident_expose_def ident_cons_def Rep_ident_inverse)
        subgoal using fact by auto
        using cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs )
        apply(cases "string_expose (Rep_ident x)")
        using cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs )
          apply(cases "Rep_ident x")
         apply(auto)
        using Rep_ident_inverse Abs_ident_inverse ds ied
        by metis
    qed
  qed
qed

lemma arg_debaseR:
  assumes spacious:"MAX_STR > ilength a"
  assumes ai:"args_to_id x = Some (Inr a)"
  shows "x = debase a"
proof -
  show ?thesis
  proof (cases "ident_expose x")
    case (Inl c) then have xc:" ident_expose x = Inl c" by auto
    then show ?thesis  apply (auto)
    proof (cases "ident_expose a")
      case (Inl d)
      then show "x = ident_cons FSENT a"
        apply(auto simp add: ident_expose_def ident_cons_def)
        using Inl_Inr_False Rep_ident_inverse ident_empty.abs_eq map_sum.simps(2) nonbase_nonemp 
              string_expose.elims ilength.rep_eq spacious apply auto
        using ai xc by auto
    next
      case (Inr e) then have xe:" ident_expose a = Inr e" by auto
      have contra:"ident_expose x = Inl () \<Longrightarrow> False"
         unfolding nonbase.simps
        using case_unit_Unity ai by auto
      from xe show "x = ident_cons FSENT a" 
        using xc apply(auto)
        using contra by auto
    qed
  next
    case (Inr b)
    then obtain c cs where cs:"ident_expose x = Inr(c,cs)"
      apply auto
      unfolding ident_expose_def
      using old.prod.exhaust by blast
    have hd:"c = FSENT"
      using ai apply(simp)
      using cs apply(simp)
      apply(cases "c = FSENT") apply(auto)
      apply(cases "c = SSENT") by(auto)
    then show ?thesis
    proof (cases "ident_expose (debase a)")
      case (Inl e) then have xe:" ident_expose (debase a) = Inl e" by auto
       note nbb = nonbase_debase[of a, OF spacious]
      have contra:"\<And>x. ident_expose (debase a) = Inl x \<Longrightarrow> False"
        using nbb unfolding nonbase.simps
        by (simp add: case_unit_Unity)
      show "?thesis" 
        using contra[OF xe] by auto
    next
      case (Inr e) then have xe:" ident_expose (debase a) = Inr e" by auto
      then obtain d ds where ds:"ident_expose (debase a) = Inr(d,ds)"
        apply auto
        using old.prod.exhaust by blast
      from spacious
      have fact:"MAX_STR > length (Rep_ident a)"
        unfolding ilength_def by auto
      have ied:"ident_expose (debase a) = Inr (FSENT, cs)"
        using cs  fact ai
        apply(auto simp add:  ident_expose_def ident_cons_def Rep_ident_inverse[of a] Abs_ident_inverse fact)
       using fact apply linarith+
       by (simp add: hd)
        have cd:"cs = ds" 
          using ied cs ds by auto
      have "Rep_ident x = FSENT # Rep_ident ds"
        using cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs)
        unfolding ident_expose_def ident_cons_def
        using cs ds
        apply(auto simp add: ident_expose_def ident_cons_def Rep_ident_inverse)
        apply(cases "MAX_STR \<le> length (Rep_ident a)")
        using fact cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs )
        apply(cases "string_expose (Rep_ident x)")
        using cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs )
          apply(cases "Rep_ident x")
         apply(auto simp add: hd)
        subgoal for bb
        using Rep_ident_inverse[of ds] Abs_ident_inverse[of bb]  cd fact apply auto
        by (metis Rep_ident impossible_Cons le_cases le_trans mem_Collect_eq)
      done
      then show "x = debase a"
        using cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs)
        unfolding ident_expose_def ident_cons_def
        using cs ds
        apply(auto simp add: ident_expose_def ident_cons_def Rep_ident_inverse)
        subgoal using fact by auto
        using cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs )
        apply(cases "string_expose (Rep_ident x)")
        using cs apply(auto simp add: Rep_ident_inverse Abs_ident_inverse cs )
          apply(cases "Rep_ident x")
         apply(auto)
        using Rep_ident_inverse Abs_ident_inverse
        by metis
    qed
  qed
qed

end