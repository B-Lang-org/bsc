package RegTime;

module sysRegTime(Empty);

  Reg#(Bit#(64)) regtime();
  mkRegU the_regtime(regtime);

  Reg#(Bool) done();
  mkReg#(False) the_done(done);

  rule start
   (!(done)); Bit#(64) wiretime <- $time();
                regtime <= wiretime;
                $display("Wiretime: %h", wiretime);
                done <= True;
  endrule: start

  rule done_rule
   (done); $display("Regtime: %h", regtime); $finish(0);
  endrule: done_rule

endmodule: sysRegTime              

endpackage
