section \<open>(No) Notation for HOL Constants\<close>
theory Notation_HOL
  imports
    Complex_Main
    "HOL-Library.FuncSet"
begin

bundle funcset_notation begin
notation funcset (infixr "\<rightarrow>" 60)
end
bundle no_funcset_notation begin
no_notation funcset (infixr "\<rightarrow>" 60)
end

bundle list_notation begin
notation nth (infixl "!" 100) 
end
bundle no_list_notation begin
no_notation nth (infixl "!" 100) 
end

end