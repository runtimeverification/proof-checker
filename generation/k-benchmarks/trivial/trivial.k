module TRIVIAL-SYNTAX

    syntax Foo ::= "a" | "b"
    syntax Bar ::= f(Foo) | g(Foo)

endmodule

module TRIVIAL

    imports TRIVIAL-SYNTAX

    rule f(F:Foo) => g(F)
    rule g(F:Foo) => F

endmodule