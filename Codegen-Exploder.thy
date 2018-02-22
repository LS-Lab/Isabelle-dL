theory Codegen_Exploder
  imports "~~/HOL/HOL"
begin 
fun swap :: "Enum.finite_2 \<Rightarrow> Enum.finite_2"
  where "swap a\<^sub>1 = a\<^sub>2"

export_code ddl_proof_ok_PPiii in Scala

end