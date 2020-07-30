////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module sysDesign(Empty);

   for (Integer j = 0; j < 4; j = j + 1) 
      begin
	 Empty x();
	 mkJ the_x(x);
      end

endmodule

module mkJ(Empty);

   Reg#(Bit#(8)) g();
   mkReg#(12) the_g(g);


   for (Integer w = 0; w < 4; w = w + 1) 
      begin
	 Reg#(Bit#(8)) z();
	 mkReg#(12) the_z(z);

	 // Empty xyz <- mkL;
         mkL;

	 rule bax (True);
	    $display("def %d", 3);
	 endrule
	 
      end

endmodule

module mkL(Empty);
   
   rule baz (True);
      $display("XXX!");
   endrule
   
endmodule


////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

