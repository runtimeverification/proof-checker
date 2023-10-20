module DOUBLE-REWRITE-SYNTAX

  syntax Foo ::= FooA() | FooB() | FooC()

endmodule

module DOUBLE-REWRITE

  imports DOUBLE-REWRITE-SYNTAX

  rule FooA() => FooB()
  rule FooB() => FooC()

endmodule
