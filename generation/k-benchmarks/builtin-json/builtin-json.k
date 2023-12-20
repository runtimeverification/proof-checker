requires "json.md"

module BUILTIN-JSON-SYNTAX
  imports STRING-SYNTAX
  imports JSON-SYNTAX

  syntax JSON ::= id(JSON) [function]

endmodule

module BUILTIN-JSON

  imports STRING
  imports JSON
  imports BUILTIN-JSON-SYNTAX

  rule [id-rule] : id(J:JSON) => String2JSON(JSON2String(J))

endmodule
