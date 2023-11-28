module TREE-SYNTAX

    imports INT-SYNTAX

    syntax Tree ::= Int | node(Tree, Tree)
    syntax Tree ::= reverse(Tree) [function, total]
    syntax KItem ::= "#Init"
    syntax KItem ::= "#next"

endmodule

module TREE

    imports INT
    imports TREE-SYNTAX

    rule [base-case]: reverse(I:Int) => I
    rule [rec-case]:  reverse(node(T1, T2)) => node(reverse(T2), reverse(T1))
    rule [init]: <k> #Init => #next </k>
    rule [next]: <k> #next => reverse(node(1, 2)) </k>

endmodule