theory Codegen_Exploder
  imports "Main"
begin 

definition explode :: "bool set"
  where "explode  = Not ` UNIV"

export_code explode in SML  

end