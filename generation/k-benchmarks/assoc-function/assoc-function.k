module ASSOC-FUNCTION-SYNTAX

  syntax Foo ::= "a" | "b" | "c" | "d"
  syntax Foo ::= Foo "+left"  Foo [function, left]
               | Foo "+right" Foo [function, right]

endmodule

module ASSOC-FUNCTION
  imports ASSOC-FUNCTION-SYNTAX

  rule [left]  : _:Foo +left  _:Foo => a
  rule [right] : _:Foo +right _:Foo => b

endmodule
