import param_test_case_new2 :: *;

interface IfcBangbang_fixed;
	(* always_ready,always_enabled *)
	method Action input_data(Bit#(33) in_data1,
                                 Bit#(33) in_data2,
                                 Bit#(3)  act46,
                                 Bit#(1)  mode46,
                                 Bit#(1)  mode810);
	(* always_ready,always_enabled *)
	method Action static_inputs(Bit#(6) maxbang);
	(* always_ready,always_enabled *)
	method Bit#(6) get_phase;

	
endinterface


(*synthesize*)
module mkBangbang_fixed(IfcBangbang_fixed);

	IfcBangbang#(3,33) dut <-mkBangbang;


	method Action input_data(Bit#(33) in_data1,
                                 Bit#(33) in_data2,
                                 Bit#(3)  act46,
                                 Bit#(1)  mode46,
                                 Bit#(1)  mode810);
		dut.input_data(in_data1,in_data2,act46,mode46,mode810);
	endmethod
	method Action static_inputs(Bit#(6) maxbang);
		dut.static_inputs(maxbang);
	endmethod
	
	method Bit#(6) get_phase;
		get_phase=dut.get_phase;
	endmethod
endmodule


