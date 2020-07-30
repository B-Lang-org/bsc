Bit#(8) zeroes = 0;
Bit#(8) ones   = -1;

(* synthesize *)
module sysNegInvOpts();

  Reg#(Bit#(8)) z <- mkReg(zeroes);
  Reg#(Bit#(8)) o <- mkReg(ones);

  Reg#(Bool) b <- mkReg(True);

  Bit#(8) zbo = b ? z : o;

  rule test(b);
    if(-{o,o} == 1) 
       $display("Negate concat: PASS");
    else
       $display("Negate concat: FAIL");
    if(~{z,o} == {ones,zeroes})
       $display("Invert concat: PASS");
    else
       $display("Invert concat: FAIL");
    if(-(-{o,z}) == {ones, zeroes})
       $display("Double negate concat: PASS");
    else 
       $display("Double negate concat: FAIL");
    if(~{~{z,o}} == {zeroes, ones})
       $display("Double invert concat: PASS");
    else
       $display("Double invert concat: FAIL");

    if(-zbo == -zeroes)
       $display("Negate if 1: PASS");
    else
       $display("Negate if 1: FAIL");
    if(~zbo == ~zeroes)
       $display("Invert if 1: PASS");
    else
       $display("Invert if 1: FAIL");
    
    b <= !b;
  endrule

  rule test2(!b);
    if(-zbo == -ones)
       $display("Negate if 2: PASS");
    else
       $display("Negate if 2: FAIL");
    if(~zbo == ~ones)
       $display("Invert if 2: PASS");
    else
       $display("Invert if 2: FAIL");
    $finish(0);
  endrule
 
endmodule
   
  