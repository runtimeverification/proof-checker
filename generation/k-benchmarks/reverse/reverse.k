module REVERSE-SYNTAX

  syntax Tree ::= "a" | "b" | "c" | node(Tree, Tree)
  syntax Tree ::= reverse(Tree) [function, total]

endmodule

module REVERSE

  imports REVERSE-SYNTAX

  rule [base-case-a] : reverse(a) => a
  rule [base-case-b] : reverse(b) => b
  rule [base-case-b] : reverse(c) => c

  rule [rec-case] : reverse(node(T1, T2)) => node(reverse(T2), reverse(T1))

endmodule
