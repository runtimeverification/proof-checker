module REWRITE-SYNTAX

  syntax Foo ::= FooA() | FooB() | FooC()

endmodule

module REWRITE

  imports REWRITE-SYNTAX

  rule FooA() => FooB()
  rule FooB() => FooC()

endmodule
