module BUILTIN-IO-SYNTAX

endmodule

module BUILTIN-IO

  imports INT
  imports STRING
  imports K-IO
  imports BUILTIN-IO-SYNTAX

  syntax KItem ::= readFromFile(String)
                 | open(IOInt)
                 | buffer(IOString)
                 | closing(K)

  configuration
    <k> readFromFile($PGM:String) </k> // file IO operation, or output upon completion or error
    <fd> -1 </fd>                      // file descriptor, or -1 for uninitialized, or < -1 for error
    <buffer> "" </buffer>              // internal read buffer

  // Open the input file for reading
  rule <k> readFromFile(FILE) => open(#open(FILE)) </k>

  // successfully opened the file, begin reading
  rule <k> open(FD:Int) => buffer(#read(FD, 500)) </k>
       <fd> _ => FD </fd>

  // error openning file for reading, report an error
  rule <k> open(E:IOError) => E </k>
       <fd> _ => -2 </fd>

  // a chunk of file was read successfully, close the file
  rule <k> buffer(S:String) => closing(#close(FD)) </k>
       <fd> FD </fd>
       <buffer> IN => IN +String S </buffer>

  // error while reading from file, report the error
  rule <k> buffer(E:IOError) => E </k>
       <fd> _ => -3 </fd>

  // successfully closed the file, return the read buffer
  rule <k> closing(.K) => IN </k>
       <fd> _ => -1 </fd>
       <buffer> IN => "" </buffer>

  // error closing the file, report the error
  rule <k> closing(E:IOError) => E </k>
       <fd> _ => -4 </fd>
endmodule

