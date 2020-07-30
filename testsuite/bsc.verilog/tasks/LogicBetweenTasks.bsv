(* synthesize *)
module sysLogicBetweenTasks ();
   Reg#(Bit#(32)) state <- mkReg(0);

   Reg#(Bit#(32)) rg <- mkReg('1);
   RWire#(Bit#(32)) rw <- mkRWire;

/*
   // this function could be used to make the calls to $stime
   // match in Verilog and Bluesim
   function ActionValue#(Bit#(32)) my_time ();
      actionvalue
	 let r <- $stime();
	 // correct for Verilog's negedge
	 if (genVerilog)
	    return (r + 5);
	 else
	    return (r);
      endactionvalue
   endfunction
*/

   rule r1 (state == 0);
      let v1 <- $stime();
      $display("v1 = %b", v1);
      let x1 = ~v1 & rg;
      $display("x1 = %b", x1);
      $display();

      // test logic that needs an always block (here, case statement)
      let v2 <- $stime();
      $display("v2 = %b", v2);
      Bit#(32) x2;
      case (rg)
	 1: x2 = v2 << 1;
	 2: x2 = v2 << 3;
	 '1: x2 = v2 << 2;
	 default: x2 = v2;
      endcase
      let x3 = x2 + 1;
      let x4 = ~x3;
      $display("x2 = %b", x2);
      $display("x4 = %b", x4);
      $display();

      state <= state + 1;
   endrule

   // test several rules muxing
   (* fire_when_enabled *)
   rule r2 (rw.wget() matches tagged Valid .v);
      $display("rw = %b", v);
      $display();
   endrule

   rule r3 (state == 1);
      let v <- $stime();
      let x = (v + 1) << 2;
      rw.wset(x);
      state <= state + 1;
   endrule

   rule r4 (state == 2);
      let v <- $stime();
      let x = (v + 2) << 3;
      rw.wset(x);
      state <= state + 1;
   endrule

   rule r5 (state == 3);
      let v <- $stime();
      let x = (v + 3) << 4;
      rw.wset(x);
      state <= state + 1;
   endrule

   rule r6 (state == 4);
      $finish(0);
   endrule

endmodule
