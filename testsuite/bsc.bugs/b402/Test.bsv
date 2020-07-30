import Design::*;

module sysTest(Empty);

  Design_IFC swap();
  mkDesign the_swap(swap);

  Reg#(Bit#(2)) indata();
  mkReg#(0) the_indata(indata);

  Reg#(Bit#(1)) sel();
  mkReg#(0) the_sel(sel);

  rule inc
   (True);
      indata <= indata + 1;
      if (indata == 2'b11)
        sel <= sel + 1;
  endrule: inc

  rule test
   (True); $display("indata: %b sel: %b out: %b",indata,sel,swap.out(indata,sel));
  endrule: test

  rule finish
   (indata == 2'b11 && sel == 1'b1); $finish(0);
  endrule: finish

endmodule: sysTest
