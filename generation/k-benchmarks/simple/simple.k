module SIMPLE

  imports DOMAINS

  syntax Expr ::= f(Int) [function] | g(Int) [function] | Int

  configuration <p> $PGM:Expr </p>

  rule [r1]: <p>0</p> => <p>g(0)</p>
  rule [f1]: f(0) => 0
  rule [f2]: g(0) => 1 *Int 2

endmodule
