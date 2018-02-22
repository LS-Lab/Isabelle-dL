theory "Codegen_Example"
  imports Complex_Main
begin
  locale Foo =
  fixes x::"'type_param::finite"
  fixes y::"'type_param::finite"

context Foo begin
fun test1 :: "int \<Rightarrow> int" where
  "test1 n = n"

fun test2 :: "'a \<Rightarrow> 'a" where
  "test2 n = n"

fun test3 :: "int \<Rightarrow> 'type_param \<Rightarrow> int" where 
  "test3 n _= n"  
end
 
interpretation bb: Foo Enum.finite_2.a\<^sub>1 Enum.finite_2.a\<^sub>2
done

lemmas[code] = Foo.test1.simps Foo.test2.simps Foo.test3.simps
  
(* Works *)
export_code "bb.test1" in SML
export_code "bb.test2" in SML
  
(* Does Not Work*)
export_code "Foo.test3" in SML

end