module sysStringDisplay(Empty);
  Reg#(Bool) done <- mkReg(False);
  Reg#(Bit#(120)) str_as_num <- mkReg('h48656c6c6f20576f726c64);
   
  rule display (!done);
    $display("str_as_num in hex     = %h", str_as_num);
    $display("str_as_num in decimal = %d", str_as_num);
    $display("str_as_num in binary  = %b", str_as_num);
    $display("str_as_num as string  = %s", str_as_num);
    $display("string literal in hex     = %h", "Hello World");
    $display("string literal in decimal = %d", "Hello World");
    $display("string literal in binary  = %b", "Hello World");
    $display("string literal as string  = %s", "Hello World"); 
    done <= True;
  endrule: display
 
  rule quit (done);
    $finish(0);
  endrule: quit

endmodule: sysStringDisplay
