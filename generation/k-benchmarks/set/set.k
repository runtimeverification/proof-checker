module SET-FUN-SYNTAX
  imports STRING-SYNTAX
  imports SET-SYNTSX

  syntax Key ::= String

  syntax Bool ::= #hasKey( Key, Set ) [function]
endmodule

module SET-FUN

  imports STRING
  imports SET
  imports SET-FUN-SYNTAX

  rule [has-key]: #hasKey(X:Key, S:Set) => X in S

endmodule
