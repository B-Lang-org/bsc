// test that predicates are evaluated in urgency order
// even when execution is in a different order

module sysRWireUrgency2(Empty);

  Reg#(Bit#(23)) r();
  mkReg#(0) the_r(r);
  Reg#(Bit#(23)) s();
  mkReg#(0) the_s(s);
  Reg#(Bit#(23)) t();
  mkReg#(0) the_t(t);
  
  RWire#(Bool) rw();
  mkRWire the_rw(rw);
  
  RWire#(Bit#(0)) rw2();
  mkRWire the_rw2(rw2);

  (* descending_urgency = "c,a" *)
  rule a (True); // first and least urgent - should not fire
    $display("Rule a r: %0d s: %0d", r, s);
    t <= t + 2;
    rw2.wset(?);
  endrule

  // will happen after a because it writes r
  rule b (True);
    $display("Rule b");
    rw.wset(True);
    r <= 5;
  endrule

  // happens last and conflicts with a
  rule c (rw.wget() != Invalid); // reads the RWire
    $display("Rule c s: %0d", s);
    t <= t + 1;
  endrule
  
  // happens after a and before e, 
  // but should not fire because a
  // didn't fire
  rule d (rw2.wget() != Invalid);
    $display("SHOULDN'T FIRE"); 
    $display("Rule d s: %0d", s);
  endrule

  // happens after c and d to exit
  rule e (True);
    s <= 17;
    $finish(0);
  endrule

endmodule


     
