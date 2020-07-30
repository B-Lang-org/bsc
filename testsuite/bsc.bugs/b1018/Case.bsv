interface IFC_Case;
	method Action start(Bit#(2) x);
endinterface

(* always_enabled, always_ready, synthesize *)

module mkCase(IFC_Case);

	Reg#(Bit#(4)) abc <- mkRegU;
		
	method Action start(a);
		case(a)
		  2'b00: abc <= 2;
		  2'b01: abc <= 5;
		  2'b10: abc <= 3;
		  2'b11: abc <= 0;
		  //Uncomment below written line and see difference in verilog
		  //for abc$EN
		  //default: abc <= abc;
		endcase
	endmethod
endmodule
