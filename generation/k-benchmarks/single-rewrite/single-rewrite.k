module SINGLE-REWRITE-SYNTAX

  syntax Term ::= A() | B()

endmodule

module SINGLE-REWRITE

  imports SINGLE-REWRITE-SYNTAX

  rule A() => B()

endmodule
