module SIMPLIFICATION-SYNTAX

  imports INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Int ::= expensive(Int) [function, no-evaluators]
  syntax Int ::= operation(Int, Int) [function]

endmodule

module SIMPLIFICATION

  imports INT
  imports BOOL
  imports SIMPLIFICATION-SYNTAX

  rule [simp-i] : _ <Int expensive(I:Int) => true requires I >Int  0 [simplification]
  rule [simp-0] : 0 <Int expensive(I:Int) => true requires I >=Int 0 [simplification]


endmodule
