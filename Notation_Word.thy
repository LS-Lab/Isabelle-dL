section \<open>(No) Notation for Word\<close>
theory Notation_Word
imports
  Word_Lib.Word_Lib
  Word_Lib.Word_Lemmas
begin

bundle word_notation begin
notation wordNOT ("~~ _" [70] 71)
notation wordAND (infixr "&&" 64)
notation wordOR (infixr "||"  59)
notation wordXOR (infixr "xor" 59)
end

bundle no_word_notation begin
no_notation wordNOT ("~~ _" [70] 71)
no_notation wordAND (infixr "&&" 64)
no_notation wordOR (infixr "||"  59)
no_notation wordXOR (infixr "xor" 59)
end

unbundle no_word_notation

end