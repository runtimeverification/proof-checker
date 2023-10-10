module PEANO-SYNTAX

    syntax Nat ::= "0"
                 | s(Nat)

    syntax Exp ::= Nat
    syntax Exp ::= s(Exp)        [strict]
    syntax Exp ::= add(Exp, Exp) [seqstrict]
    syntax Exp ::= mul(Exp, Exp) [seqstrict]

endmodule

module PEANO

    imports PEANO-SYNTAX

    syntax KResult ::= Nat

    rule add(0, M:Nat) => M
    rule add(s(N:Nat), M:Nat) => s(add(N, M))

    rule mul(0, _:Nat) => 0
    rule mul(s(N:Nat), M:Nat) => add(M, mul(N, M))

endmodule