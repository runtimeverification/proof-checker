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
                 > AExp "+" AExp
                 | AExp "-" AExp
  syntax BExp  ::= IBool
                 | AExp ">" AExp
  syntax Block ::= "{" "}"
                 | "{" StmtList "}"
  syntax Stmt  ::= Block
                 | Id2 "=" AExp ";"
                 | "if" "(" BExp ")"
                   Block "else" Block
                 | "while" "(" BExp ")" Block
  syntax StmtList ::= Stmt | Stmt StmtList
  syntax Pgm ::= StmtList

endmodule

module IMP5-RW-LITERAL
  imports IMP5-RW-LITERAL-SYNTAX
  imports INTERNAL-DOMAIN

  configuration <T>
                  <k color="green"> $PGM:Pgm </k>
                  <x1  color="red"> 0:IInt </x1>
                  <x2  color="red"> 0:IInt </x2>
                  <x3  color="red"> 0:IInt </x3>
                  <x4  color="red"> 0:IInt </x4>
                  <x5  color="red"> 0:IInt </x5>
                  <ret color="red"> 0:IInt </ret>
                </T>

  // for manually defining heating/cooling rules
  syntax AExp ::= "#hole"
  syntax BExp ::= "#hole"

  // Identifiers
  rule <k> x1  => I ...</k> <x1>  I </x1>
  rule <k> x2  => I ...</k> <x2>  I </x2>
  rule <k> x3  => I ...</k> <x3>  I </x3>
  rule <k> x4  => I ...</k> <x4>  I </x4>
  rule <k> x5  => I ...</k> <x5>  I </x5>
  rule <k> ret => I ...</k> <ret> I </ret>

  // + [seqstrict]
  rule <k> A1:AExp + A2:AExp => A1 ~> #hole + A2 ... </k>
  rule <k> (A1:IInt ~> #hole + A2) => A2 ~> A1 ~> #hole + #hole  ... </k>
  rule <k> (10 ~> 200 ~> #hole + #hole) => 210 ... </k> // the transfer example: 200 + 10

  // - [seqstrict]
  rule <k> A1:AExp - A2:AExp => A1 ~> #hole - A2 ... </k>
  rule <k> (A1:IInt ~> #hole - A2) => A2 ~> A1 ~> #hole - #hole  ... </k>
  rule <k> (10 ~> 100 ~> #hole - #hole) => 90 ... </k> // the transfer example: 100 - 10

  // > [seqstrict]
  rule <k> A1:AExp > A2:AExp => A1 ~> #hole > A2 ... </k>
  rule <k> (A1:IInt ~> #hole > A2) => A2 ~> A1 ~> #hole > #hole  ... </k>
  rule <k> (100 ~> 10 ~> #hole > #hole) => false ... </k> // the transfer example: 10 > 100

  // assignment [strict(2)]
  rule <k> X:Id2 = A:AExp; => A ~> X = #hole; ... </k>
  rule <k> (I:IInt ~> x1  = #hole;) => . ...</k> <x1>  _ => I </x1>
  rule <k> (I:IInt ~> x2  = #hole;) => . ...</k> <x2>  _ => I </x2>
  rule <k> (I:IInt ~> x3  = #hole;) => . ...</k> <x3>  _ => I </x3>
  rule <k> (I:IInt ~> x4  = #hole;) => . ...</k> <x4>  _ => I </x4>
  rule <k> (I:IInt ~> x5  = #hole;) => . ...</k> <x5>  _ => I </x5>
  rule <k> (I:IInt ~> ret = #hole;) => . ...</k> <ret> _ => I </ret>

  // conditional [strict(1)]
  rule <k> if (B:BExp) S1 else S2 => B ~> if (#hole) S1 else S2 ...</k>
  rule <k> (true  ~> if (#hole)  S else _) => S ... </k>
  rule <k> (false ~> if (#hole)  _ else S) => S ... </k>

  // while loops
  rule while (B) S => if (B) {S while (B) S} else {}

  // blocks
  rule {} => .
  rule {S} => S

  // Statements
  rule S1:Stmt S2:Stmt => S1 ~> S2

endmodule
