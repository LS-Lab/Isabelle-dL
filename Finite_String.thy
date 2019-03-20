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
  "lleq Nil Nil = True"
| "lleq Nil _ = True"
| "lleq _ Nil = False"
| "lleq (x # xs)(y # ys) = 
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

fun string_expose::"string \<Rightarrow> (unit + (char * string))"
  where "string_expose Nil = Inl ()"
  | "string_expose (c#cs) = Inr(c,cs)"

lift_definition ident_empty::ident is "''''" done
lift_definition ident_cons::"char \<Rightarrow> ident \<Rightarrow> ident" is "(#)" sorry
lift_definition ident_expose::"ident \<Rightarrow> (unit + (char*ident))" is string_expose sorry


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

lift_definition Ix::ident is "''x''::string"  
  done
lift_definition Iy::ident is "''y''::string"
  done
lift_definition Iz::ident is "''z''::string"
  done
lift_definition Iw::ident is "''w''::string"
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


definition "FSENTINEL = ''.''"
definition "CSENTINEL = ''_''"
definition "FSENT = hd FSENTINEL"
definition "CSENT = hd CSENTINEL"

fun args_to_id::"ident \<Rightarrow> (ident + ident)"
  where "args_to_id  z = 
      (case (ident_expose z) of 
       Inl () \<Rightarrow> Inl ident_empty
     | Inr (x,xs) \<Rightarrow> (if x#Nil = FSENTINEL then Inr xs else Inl (ident_cons x xs)))"

fun arg_to_id::"ident \<Rightarrow> (ident + unit)"
  where "arg_to_id  z = 
      (case (ident_expose z) of 
       Inl () \<Rightarrow> Inl ident_empty
     | Inr (x,xs) \<Rightarrow> (if x#Nil = CSENTINEL then Inr () else Inl (ident_cons x xs)))"

fun debase :: "ident \<Rightarrow> ident"
  where "debase f = ident_cons FSENT f"
fun rebase :: "ident \<Rightarrow> ident"
  where "rebase f = (case ident_expose f of Inl () \<Rightarrow> f | Inr (c,cs) \<Rightarrow> cs)"
fun is_base :: "ident \<Rightarrow> bool"
  where "is_base f = (case (ident_expose f) of Inl () \<Rightarrow> True | Inr(c,cs) \<Rightarrow> c \<noteq> FSENT)"


end