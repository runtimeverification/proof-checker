module INTERNAL-DOMAIN-SYNTAX
  // Domain constructors
  syntax IBool ::= "true" | "false"
  syntax IInt ::= "12345" | "10" | "100" | "200" | "1" | "90" | "210" | "0"

endmodule

module INTERNAL-DOMAIN
  imports INTERNAL-DOMAIN-SYNTAX

endmodule

module IMP5-RW-LITERAL-SYNTAX
  imports INTERNAL-DOMAIN-SYNTAX

  syntax Id2 ::= "x1" | "x2" | "x3" | "x4" | "x5" | "ret"
  syntax AExp  ::= IInt | Id2
                 | "(" AExp ")"               [bracket]
                 > AExp "+" AExp              [left, seqstrict]
                 | AExp "-" AExp              [left, seqstrict]
  syntax BExp  ::= IBool
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

module IMP5-RW-LITERAL
  imports IMP5-RW-LITERAL-SYNTAX
  imports INTERNAL-DOMAIN

  syntax KResult ::= IInt | IBool

  configuration <T>
                  <k color="green"> $PGM:Pgm </k>
                  <x1  color="red"> 0:IInt </x1>
                  <x2  color="red"> 0:IInt </x2>
                  <x3  color="red"> 0:IInt </x3>
                  <x4  color="red"> 0:IInt </x4>
                  <x5  color="red"> 0:IInt </x5>
                  <ret color="red"> 0:IInt </ret>
                </T>

  rule <k> x1  => I ...</k> <x1>  I </x1>
  rule <k> x2  => I ...</k> <x2>  I </x2>
  rule <k> x3  => I ...</k> <x3>  I </x3>
  rule <k> x4  => I ...</k> <x4>  I </x4>
  rule <k> x5  => I ...</k> <x5>  I </x5>
  rule <k> ret => I ...</k> <ret> I </ret>

  rule {} => .
  rule {S} => S

  rule <k> x1  = I:IInt; => . ...</k> <x1>  ( _ => I ) </x1>
  rule <k> x2  = I:IInt; => . ...</k> <x2>  ( _ => I ) </x2>
  rule <k> x3  = I:IInt; => . ...</k> <x3>  ( _ => I ) </x3>
  rule <k> x4  = I:IInt; => . ...</k> <x4>  ( _ => I ) </x4>
  rule <k> x5  = I:IInt; => . ...</k> <x5>  ( _ => I ) </x5>
  rule <k> ret = I:IInt; => . ...</k> <ret> ( _ => I ) </ret>

  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule if (true)  S else _ => S
  rule if (false) _ else S => S

  rule while (B) S => if (B) {S while (B) S} else {}

  // For the transfer example:
  rule 200 + 10 => 210
  rule 100 - 10 => 90
  rule 10 > 100 => false

endmodule
