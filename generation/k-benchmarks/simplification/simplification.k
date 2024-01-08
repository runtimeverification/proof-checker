module SIMPLIFICATION-SYNTAX

  imports INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Int ::= expensive(Int) [function, no-evaluators]
  syntax Bool ::= operation(Int, Int) [function]

endmodule

module SIMPLIFICATION

  imports INT
  imports BOOL
  imports SIMPLIFICATION-SYNTAX

  rule operation(I1, I2) => I1 <Int expensive(I2)

  rule [simp-i] : _ <Int expensive(I:Int) => true requires I >Int  0 [simplification]
  rule [simp-0] : 0 <Int expensive(I:Int) => true requires I >=Int 0 [simplification]


endmodule
