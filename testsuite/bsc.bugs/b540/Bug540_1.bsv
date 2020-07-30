module sysBug540_1(Empty);

  Reg#(Bit#(2)) r();
  mkReg#(0) the_r(r);

  Reg#(Bit#(1)) a();
  mkReg#(0) the_a(a);

  Reg#(Bit#(1)) b();
  mkReg#(1) the_b(b);

  Reg#(Bit#(1)) c();
  mkReg#(0) the_c(c);
  
  Reg#(Bool) done();
  mkReg#(False) the_done(done);

  rule test (True);
   Bit#(2) d = 3;
   case({a,b})
    2'b00 : d = {~c,c};
    2'b11 : d = {c,~c};
   endcase
   r <= d;
  endrule: test

  rule dump (True);
    $display("r: %0d", r);
    if(done)
      $finish(0);
    else
      done <= True;
  endrule

endmodule
