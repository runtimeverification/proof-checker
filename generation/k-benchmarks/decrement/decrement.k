module TRIVIAL-SYNTAX

    syntax Nat ::= "0" | s(Nat)

endmodule

module TRIVIAL

    imports TRIVIAL-SYNTAX

    rule [decrement] : s(N:Nat) => N

endmodule