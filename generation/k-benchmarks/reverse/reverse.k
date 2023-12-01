module REVERSE
  imports INT

  syntax Tree ::= Int | node(Tree, Tree)
  syntax Tree ::= reverse(Tree) [function, total]

  rule [base-case]: reverse(I:Int) => I
  rule [rec-case]:  reverse(node(T1, T2)) => node(reverse(T2), reverse(T1))

  syntax KItem ::= "#init"
  syntax KItem ::= "#next"

  rule [init]: <k> #init => #next </k>
  rule [next]: <k> #next => reverse(node(1, 2)) </k>
endmodule
