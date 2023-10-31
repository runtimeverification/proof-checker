module INTERNAL-DOMAIN-SYNTAX
  // Domain constructors
  syntax IBool ::= "true" | "false"
  syntax Nat ::= "0" | s(Nat)

  // Functions (as constructors)
  syntax NatExp ::= Nat
                  | s(NatExp)            [strict]
                  | NatExp "+Nat" NatExp [seqstrict]
                  | NatExp "-Nat" NatExp [seqstrict]

  syntax IBoolExp ::= IBool
                    | NatExp ">Nat" NatExp [strict]

  // Aditional syntactic sugar for the transfer example
  syntax NatExp ::= "12345" | "10" | "100" | "200" | "1"

endmodule

module INTERNAL-DOMAIN
  imports INTERNAL-DOMAIN-SYNTAX

  // Nat plus
  rule 0 +Nat M:Nat => M
  rule s(N:Nat) +Nat M:Nat => s(N +Nat M)

  // Nat monus
  rule 0 -Nat _:Nat => 0
  rule s(N:Nat) -Nat 0 => s(N)
  rule s(N:Nat) -Nat s(M:Nat) => N -Nat M

  // Nat greater than
  rule 0 >Nat _:Nat => false
  rule s(_:Nat) >Nat 0 => true
  rule s(N:Nat) >Nat s(M:Nat) => N >Nat M
endmodule

module IMP5-REWRITE-SYNTAX
  imports INTERNAL-DOMAIN-SYNTAX

  syntax Id2 ::= "x1" | "x2" | "x3" | "x4" | "x5" | "ret"
  syntax AExp  ::= NatExp | Id2
                 | "(" AExp ")"               [bracket]
                 > AExp "+" AExp              [left, seqstrict]
                 | AExp "-" AExp              [left, seqstrict]
  syntax BExp  ::= IBoolExp
                 | AExp ">" AExp              [seqstrict]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id2 "=" AExp ";"           [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= Stmt

endmodule

module IMP5-REWRITE
  imports IMP5-REWRITE-SYNTAX
  imports INTERNAL-DOMAIN

  syntax KResult ::= Nat | IBool

  syntax Vars5 ::= Nat "," Nat "," Nat "," Nat "," Nat "," Nat

  configuration <T>
                  <k color="green"> $PGM:Pgm </k>
                  <s color="red"> (0 , 0 , 0 , 0 , 0 , 0):Vars5 </s>
                </T>

  rule <k> x1 => I ...</k> <s> I , _ , _ , _ , _ , _ </s>
  rule <k> x2 => I ...</k> <s> _ , I , _ , _ , _ , _ </s>
  rule <k> x3 => I ...</k> <s> _ , _ , I , _ , _ , _ </s>
  rule <k> x4 => I ...</k> <s> _ , _ , _ , I , _ , _ </s>
  rule <k> x5 => I ...</k> <s> _ , _ , _ , _ , I , _ </s>
  rule <k> ret => I ...</k> <s> _ , _ , _ , _ , _ , I </s>

  rule I1 + I2 => I1 +Nat I2
  rule I1 - I2 => I1 -Nat I2

  rule I1 > I2 => I1 >Nat I2

  rule {} => .
  rule {S} => S

  rule <k> x1 = I:Nat; => . ...</k> <s> ( _ => I ) , _ , _ , _ , _ , _ </s>
  rule <k> x2 = I:Nat; => . ...</k> <s> _ , ( _ => I ) , _ , _ , _ , _ </s>
  rule <k> x3 = I:Nat; => . ...</k> <s> _ , _ , ( _ => I ) , _ , _ , _ </s>
  rule <k> x4 = I:Nat; => . ...</k> <s> _ , _ , _ , ( _ => I ) , _  , _ </s>
  rule <k> x5 = I:Nat; => . ...</k> <s> _ , _ , _ , _ , ( _ => I ) , _ </s>
  rule <k> ret = I:Nat; => . ...</k> <s> _ , _ , _ , _ , _ , ( _ => I ) </s>

  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule if (true)  S else _ => S
  rule if (false) _ else S => S

  rule while (B) S => if (B) {S while (B) S} else {}

  // For the transfer example:
  // Values are arbitrary, but they preserve the original flow of control of the transfer example
  rule 12345 => 0 // 0
  rule 10 => s(0) // 1
  rule 100 => s(s(s(s(s(s(s(s(s(s(0))))))))))  // 10
  rule 200 => s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(0)))))))))))))))))))) // 20
  rule 1 => s(0) // 1
endmodule
