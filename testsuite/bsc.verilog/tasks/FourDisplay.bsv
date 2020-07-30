export sysFourDisplay;

module sysFourDisplay(Empty);
  Reg#(Bit#(16)) r();
  mkReg#(0) the_r(r);
  Reg#(Bit#(3)) counter();
  mkReg#(0) the_counter(counter);

  rule start
   (counter == 0); r <= 5;
  endrule: start
  rule t1
   (counter == 1); r <= r + 1;
  endrule: t1
  rule t2
   (counter == 2); r <= zeroExtend(counter);
  endrule: t2
  rule t3
   (counter == 3); r <= 19;
  endrule: t3
  rule t4 
   (counter == 4); $finish(0);
  endrule: t4
  rule count
    (True()); counter <= counter + 1; 
  endrule: count
  rule display
    (True()); $display("counter: %0d\nr: %0d\n", counter, r);
  endrule: display
endmodule: sysFourDisplay
