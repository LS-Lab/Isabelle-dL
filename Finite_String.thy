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

lift_definition ilength::"ident \<Rightarrow> nat" is length done

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

fun less :: "char list \<Rightarrow> char list \<Rightarrow> bool"
  where 
  "less Nil Nil = False"
| "less Nil _ = True"
| "less _ Nil = False"
| "less (x # xs)(y # ys) = 
   (if x = y then less xs ys else x < y)"

lift_definition less_ident::"ident \<Rightarrow> ident \<Rightarrow> bool" is less done

lemma lists_induct:"\<And>P. (P [] []) \<Longrightarrow> (\<And>x xs. P (x#xs) []) \<Longrightarrow> (\<And>x xs. P [] (x#xs)) \<Longrightarrow> (\<And>L1 L2 x1 x2. P L1 L2 \<Longrightarrow> P (x1 # L1) (x2 # L2)) \<Longrightarrow> P A B"
  using  List.list_induct2' by metis

lemma ax1:"\<And>x y. (less x y) = (lleq x y \<and> \<not> lleq y  x)"
  subgoal for x y
    apply(induction rule: lists_induct)
    by(auto) done
lemma ax2:"\<And>x. lleq x x"
  subgoal for x 
    apply(induction x)
    by(auto) done
lemma ax3:"\<And>x y z. lleq x  y \<Longrightarrow> lleq y z \<Longrightarrow> lleq x  z"
  subgoal for x y z
    apply(induction arbitrary: z rule: lists_induct )
       apply(auto)
    subgoal for x xs z
      apply(induction y)
      using lleq.elims(2) lleq.simps(2) by blast+
    subgoal for L1 L2 x1 x2 z
      apply(cases "x2 = x1")
      apply(auto simp add: less_trans list.discI list.inject lleq.elims(2) lleq.elims(3) order.asym)
      using less_trans list.discI list.inject lleq.elims(2) lleq.elims(3) order.asym
      apply smt+
      done
    done
  done
lemma ax4:"\<And>x y. lleq x y \<Longrightarrow> lleq y x \<Longrightarrow> x = y"
  subgoal for x y
    apply(induction rule: lists_induct)
       apply(auto) 
    subgoal for L1 L2 x1 x2
      apply(cases "x1 = x2") by auto
    subgoal for L1 L2 x1 x2
      apply(cases "x1 = x2") by auto
    done done
lemma ax5:"\<And>x y. lleq x y \<or> lleq y x"
  subgoal for x y
    apply(induction rule: lists_induct)
    by(auto) done

lemma ax6:"\<And>x y. lleq x y \<Longrightarrow> lleq y x \<Longrightarrow> x = y"
  subgoal for x y
    apply(induction rule: lists_induct)
       apply(auto)
    subgoal for L1 L2 x1 x2
      apply(cases "x1 = x2") by auto
    subgoal for L1 L2 x1 x2
      apply(cases "x1 = x2") by auto
    done
  done

instance
  apply(standard)
  unfolding less_eq_ident_def less_ident_def
      apply (auto simp add: ax1 ax2 ax3 ax4 ax5 ax6)
  using ax6 less_eq_ident_def less_ident_def Rep_ident_inject by blast
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
  "ident_upto 0 = [ident_empty]"
| "ident_upto (Suc k) = 
 (let r = ident_upto k in
  let ab =  (enum_class.enum::char list) in
  ident_empty # concat (map (\<lambda> c. map (\<lambda>s. ident_cons c  s) r) ab))"

lemma mem_appL:"List.member L1 x \<Longrightarrow> List.member (L1 @ L2) x"
  apply(induction L1 arbitrary: L2)
  by(auto simp add: member_rec)

lemma mem_appR:"List.member L2 x \<Longrightarrow> List.member (L1 @ L2) x"
  apply(induction L1 arbitrary: L2)
  by(auto simp add: member_rec)

lemma mem_app_or:"List.member (L1 @ L2) x = List.member L1 x \<or> List.member L2 x"
  unfolding member_def by auto

lemma ident_nil:"\<And>n. List.member (ident_upto n) ident_empty"
  subgoal for n
    apply(induction n)
    using ident_empty_def 
    by(auto simp add: member_rec Let_def)
  done

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

lemma length_induct:
  fixes P
  assumes len:"length L \<le> MAX_STR"
  assumes BC:"P [] 0"
  assumes IS:"(\<And>k x xs.  P xs k \<Longrightarrow> P ((x # xs)) (Suc k))"
  shows  "P L (length L)"
  proof -
    have main:"\<And>k.  length L = k \<Longrightarrow> k \<le> MAX_STR \<Longrightarrow> P L (length L)" subgoal for k
        apply(induction L arbitrary: k)
        subgoal for k using BC unfolding ident_empty_def by auto
        subgoal for a L k
        proof -
          assume IH:"(\<And>k. length L = k \<Longrightarrow> k \<le> MAX_STR \<Longrightarrow> P L (length L))"
          assume l:"length (a # L) = k"
          assume str:"k \<le> MAX_STR"
          have yLen:"length L < MAX_STR" using l str by auto
          have it:"P (L) (length L)" 
            using IH[of k] l str  IH less_imp_le yLen by blast
          show  "P  (a # L) (length (a # L))"
            using IS[OF it, of a] by (auto)
        qed
        done
      done
    show ?thesis
      apply(rule main)
      using BC IS len by auto
  qed

lemma ilength_induct:
  fixes P
  assumes BC:"P ident_empty 0"
  assumes IS:"(\<And>k x xs.  P xs k \<Longrightarrow> P (Abs_ident (x # Rep_ident xs)) (Suc k))"
  shows  "P L (ilength L)"
  apply(cases L)
  apply(unfold ilength_def)
  apply(auto simp add: Abs_ident_inverse)
  subgoal for y
  proof -
    assume a1:"L = Abs_ident y"
    assume a2:" length y \<le> MAX_STR "
    have main:"\<And>k. L = Abs_ident y \<Longrightarrow> length y = k \<Longrightarrow> k \<le> MAX_STR \<Longrightarrow> P (Abs_ident y) (length y)" subgoal for k
        apply(induction y arbitrary: k L)
        subgoal for k using BC unfolding ident_empty_def by auto
        subgoal for a y k L
        proof -
          assume IH:"(\<And>k L. L = Abs_ident y \<Longrightarrow> length y = k \<Longrightarrow> k \<le> MAX_STR \<Longrightarrow> P (Abs_ident y) (length y))"
          assume L:"L = Abs_ident (a # y)"
          assume l:"length (a # y) = k"
          assume str:"k \<le> MAX_STR"
          have yLen:"length y < MAX_STR" using l str by auto
          have it:"P (Abs_ident y) (length y)" 
            using IH[of "Abs_ident y" "k-1", OF refl] using L l str by auto
          show  "P (Abs_ident (a # y)) (length (a # y))"
            using IS[OF it, of a] apply (auto simp add: ident_cons_def Abs_ident_inverse)
            apply(cases "MAX_STR \<le> length (Rep_ident (Abs_ident y))")
            using yLen by(auto simp add: l yLen Abs_ident_inverse)
        qed
        done
      done
    show ?thesis
      apply(rule main)
      using BC IS a1 a2 by auto
  qed
  done

lemma enum_chars:"set (enum_class.enum::char list)= UNIV"
  using   Enum.enum_class.enum_UNIV by auto

lemma member_concat:
  shows "(\<exists> LL. List.member L LL \<and> List.member LL x) \<Longrightarrow> List.member (concat L) x"
  apply(induction L)
  by(auto simp add: member_def)

lemma ident_length:
  fixes L::string
  assumes len:"length L \<le> k"
  assumes Len:"length L \<le> MAX_STR"
  shows "List.member (ident_upto k) (Abs_ident L)"
proof - 
  have BC:"\<forall>j\<ge>0. 0 \<le> MAX_STR \<longrightarrow> length [] = 0 \<longrightarrow> List.member (ident_upto j) (Abs_ident [])" 
    apply(auto) subgoal for j apply(cases j) by (auto simp add: ident_empty_def member_rec) done
  have IS:"(\<And>k x xs.
      \<forall>j\<ge>k. k \<le> MAX_STR \<longrightarrow> length xs = k \<longrightarrow> List.member (ident_upto j) (Abs_ident xs) \<Longrightarrow>
      \<forall>j\<ge>Suc k. Suc k \<le> MAX_STR \<longrightarrow> length (x # xs) = Suc k \<longrightarrow> List.member (ident_upto j) (Abs_ident (x # xs)))"
    subgoal for k x xs
    proof -
      assume "\<forall>j\<ge>k. k \<le> MAX_STR \<longrightarrow> length xs = k \<longrightarrow> List.member (ident_upto j) (Abs_ident xs)"
      then have IH:"\<And>j. j\<ge> k \<Longrightarrow> k \<le> MAX_STR \<Longrightarrow> length xs = k \<Longrightarrow> List.member (ident_upto j) (Abs_ident xs)" by auto
      show ?thesis
        apply(auto)
        subgoal for j
        proof -
          assume kj:"Suc (length xs) \<le> j"
          assume sucMax:"Suc (length xs) \<le> MAX_STR"
          assume ilen:" k = length xs"
          obtain jj where jj[simp]:"j = Suc jj" using kj Suc_le_D by auto
          then have kMax:"k < MAX_STR" using jj kj Suc_le_D ilen
            by (simp add: less_eq_Suc_le sucMax)
           have res:"List.member (ident_upto (jj)) (Abs_ident xs)"
            using IH[of "jj"] kj jj ilen  Suc_leD sucMax by blast
          have neq:"Abs_ident [] \<noteq> Abs_ident (x # xs)"
            using Abs_ident_inverse ident_empty.abs_eq ident_empty.rep_eq len length_Cons list.distinct(1) mem_Collect_eq
            by (metis ilen sucMax)
          have univ:" set enum_class.enum  = (UNIV::char set)" using enum_chars by auto
          have "List.member (ident_upto j) (Abs_ident (x # xs))"
             apply(auto simp add: member_rec(2) ident_empty_def)
            using len  sucMax  apply(auto simp add: member_rec ident_empty_def ident_cons_def  Abs_ident_inverse Rep_ident_inverse neq)
          proof -
            let ?witLL = "map (map_fun Rep_ident Abs_ident (string_cons x)) (ident_upto jj)"
            have ex:"\<exists> LL. (List.member (map (\<lambda>c. map (map_fun Rep_ident Abs_ident (string_cons c)) (ident_upto jj)) enum_class.enum) LL) \<and> List.member LL (Abs_ident (x # xs))"
              apply(rule exI[where x="?witLL"])
              apply(auto simp add: member_def univ )
              using res kMax IH Abs_ident_inverse antisym ilen image_iff  less_le map_fun_apply mem_Collect_eq member_def string_cons.simps univ
              by smt
            show "List.member (concat (map (\<lambda>c. map (map_fun Rep_ident Abs_ident (string_cons c)) (ident_upto jj)) enum_class.enum))
     (Abs_ident (x # xs))"
              using member_concat[OF ex] by auto
          qed
          then show "List.member (ident_upto j) (Abs_ident (x # xs))"  by auto
        qed
        done
    qed
    done
  have impl:"length L \<le> k \<Longrightarrow> List.member (ident_upto k) (Abs_ident L)"
    using length_induct[where P = "(\<lambda> L k. \<forall> j \<ge> k. k \<le> MAX_STR \<longrightarrow> length L = k \<longrightarrow> List.member (ident_upto j) (Abs_ident L))", OF Len BC IS] 
    using len Len by auto
  show ?thesis
    using impl len by auto
qed

lemma concat_mem:"List.member (concat LL) x = (\<exists>L. List.member LL L \<and> List.member L x)"
  by(auto simp add: member_def)

lemma ident_upto_length:
  shows "List.member (ident_upto n) L \<Longrightarrow> ilength L \<le> n"
  apply(induction n arbitrary: L)
   apply(auto simp add: ident_empty_def Let_def ilength_def ident_cons_def Rep_ident_inverse Abs_ident_inverse member_rec)
proof -
  fix n L
  assume len:"(\<And>L. List.member (ident_upto n) L \<Longrightarrow> length (Rep_ident L) \<le> n)"
  assume mem:"List.member (concat (map (\<lambda>c. map (map_fun Rep_ident Abs_ident (string_cons c)) (ident_upto n)) enum_class.enum)) L"
  have L:"List.member (ident_upto n) L \<Longrightarrow> length (Rep_ident L) \<le> Suc n" using len[of L] by auto
  have R:"List.member (concat (map (\<lambda>c. map (map_fun Rep_ident Abs_ident (string_cons c)) (ident_upto n)) enum_class.enum)) L
         \<Longrightarrow> length (Rep_ident L) \<le> Suc n" 
  proof -
    assume a:"List.member (concat (map (\<lambda>c. map (map_fun Rep_ident Abs_ident (string_cons c)) (ident_upto n)) enum_class.enum)) L"
    obtain LL where conc:"List.member (map (\<lambda>c. map (map_fun Rep_ident Abs_ident (string_cons c)) (ident_upto n)) enum_class.enum) LL"
      and concmem:"List.member LL L"
      using concat_mem a by metis

    obtain c cs where c:"L = ident_cons c cs" and cs:"List.member (ident_upto n) cs"
      using a conc unfolding member_def apply(auto)
      subgoal for c d cs
        apply(cases "MAX_STR \<le> length (Rep_ident cs)")
         apply(auto simp add: Rep_ident_inverse)
        by (metis (full_types) Rep_ident_inverse ident_cons.rep_eq string_cons.simps)+ done
    then have "ilength (ident_cons c cs) \<le> (Suc n)"
      using len[of cs] unfolding ilength_def ident_cons_def apply (auto simp add: Rep_ident_inverse)
      using c ident_cons.rep_eq by force
    then show ?thesis
      using c ilength.rep_eq by auto
  qed
  show "length (Rep_ident L) \<le> Suc n"
    using L R  mem by blast
qed

lemma distinct_upto:
  shows "i \<le> MAX_STR \<Longrightarrow> distinct (ident_upto i)"
proof (induction i)
  case 0
  then show ?case by(auto)
next
  case (Suc j) then
  have jLen:"Suc j \<le> MAX_STR"
    and IH:"distinct (ident_upto j)" by auto
  have distinct_char:"distinct (enum_class.enum:: char list)" 
    apply(unfold enum_char_unfold)
    apply(unfold distinct_map)
    by auto
  show ?case 
    apply(auto simp add: Let_def)
    subgoal for x xa
      using jLen apply(auto simp add: ident_empty_def ident_cons_def)
      by (smt Rep_ident_inverse Suc_leD eq_onp_same_args ident_empty.rep_eq ilength.abs_eq le_zero_eq length_0_conv length_Cons not_less_eq_eq)
     apply(rule distinct_concat)
    subgoal apply(auto simp add: distinct_map)
       apply(rule distinct_char)
      apply(rule subset_inj_on[where B=UNIV])
       apply(rule injI)
       apply(auto simp add: ident_cons_def) subgoal for x y
        by (smt Abs_ident_inverse Iz.rsp Pair_inject Suc_leD antisym eq_onp_same_args ident_empty.rep_eq ident_nil impossible_Cons length_Cons mem_Collect_eq member_def string_expose.simps(2) sum.inject(2))
      done
    subgoal for ys
      apply(auto simp add: ident_cons_def)
    proof -
      fix c :: char
       assume c:"c \<in> set enum_class.enum"
       assume ys:"ys = map (map_fun Rep_ident Abs_ident (string_cons c)) (ident_upto j)"
       show "distinct (map (map_fun Rep_ident Abs_ident (string_cons c)) (ident_upto j))"
         unfolding distinct_map apply(rule conjI)
          apply(rule IH)
         apply(rule inj_onI)
         apply(auto)
         subgoal for x y
           using ident_upto_length[of j x] ident_upto_length[of j y]
            unfolding List.member_def
            using jLen  unfolding ilength_def apply auto
            by (metis (mono_tags, hide_lams) Rep_ident_inverse ident_cons.rep_eq le_trans list.inject not_less_eq_eq string_cons.simps)
          done
      qed
    subgoal for ys zs
      apply(auto)
         subgoal for  c ca xa xb xc
         apply(auto simp add: ident_cons_def)
          using ident_upto_length[of j] jLen 
          by (smt Rep_ident_inverse ident_cons.rep_eq ilength.rep_eq le_trans list.inject member_def not_less_eq_eq string_cons.simps)
        done
      done
qed

instantiation ident :: enum begin
definition enum_ident 
  where enum_ident_def[code]:"enum_ident \<equiv> ident_enum"
definition enum_all_ident
  where enum_all_ident[code]:"enum_all_ident \<equiv> ident_enum_all"
definition enum_ex_ident
  where enum_ex_ident[code]:"enum_ex_ident \<equiv> ident_enum_ex"
lemma enum_ALL:"(UNIV::ident set) = set enum_class.enum"
  subgoal
    apply(auto simp add:enum_ident_def ident_enum_def)
    subgoal for x
      apply(unfold vals_def)
      apply(rule Abs_ident_cases[where x=x])
      subgoal for y
        using ident_nil[of MAX_STR]  List.member_def[of "ident_upto MAX_STR" x] ident_empty_def ident_length
        using Rep_ident ilength.rep_eq mem_Collect_eq by auto
      done
    done done

lemma vals_ALL:"set (vals::ident list) = UNIV"
  using enum_ALL vals_def Rep_ident ident_length ilength.rep_eq member_def 
  by (metis (mono_tags) Rep_ident_inverse UNIV_eq_I mem_Collect_eq)

lemma setA:
  assumes set:"\<And>y. y \<in> set L \<Longrightarrow> P y"
  shows "list_all P L"
  using set  by (simp add: list.pred_set)

lemma setE:
  assumes set:" y \<in> set L"
  assumes P:"P y"
  shows "list_ex P L"
  using set P  list_ex_iff by auto

instance 
  apply(standard)
  apply(rule enum_ALL)
  subgoal
    apply (auto simp add: ident_enum_def vals_def enum_ident_def)
    by (auto simp add: distinct_upto)
  subgoal for P
    apply(auto)
    unfolding enum_all_ident ident_enum_all_def enum_ALL vals_ALL
    using setA apply (simp add: list_all_iff vals_ALL)
    by (simp add: setA)
  subgoal for P
    apply(auto)
    unfolding enum_ex_ident ident_enum_ex_def enum_ALL vals_ALL
    using setE apply (simp add: list_ex_iff vals_ALL)
    by (simp add: setE vals_ALL)
  done
end
export_code ident_enum_ex in Scala
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