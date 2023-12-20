module CONDITIONAL-FUNCTION-SYNTAX

  imports INT-SYNTAX

  syntax Foo ::= foo(Int)
               | bar(Foo)

  syntax Int ::= factorial(Int) [function]

endmodule

module CONDITIONAL-FUNCTION

  imports INT
  imports CONDITIONAL-FUNCTION-SYNTAX

  rule bar(foo(X:Int)) => foo(factorial(X))

  rule factorial(X:Int) => X *Int factorial(X -Int 1)
      requires X >=Int 1

  rule factorial(0) => 1

endmodule
