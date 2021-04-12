interface IfcBangbang#(type div_ratio, type div_ratio_x11);
	(* always_ready,always_enabled *)
	method Action input_data(Bit#(div_ratio_x11) in_data1,
                                 Bit#(div_ratio_x11) in_data2,
                                 Bit#(div_ratio)     act46,
                                 Bit#(1)             mode46,
                                 Bit#(1)             mode810);
	(* always_ready,always_enabled *)
	method Action static_inputs(Bit#(6) maxbang);
	(* always_ready,always_enabled *)
	method Bit#(6) get_phase;

	
endinterface


//(*synthesize*)
module mkBangbang (IfcBangbang#(div_ratio, div_ratio_x11))
  provisos (Mul#(div_ratio, 11, div_ratio_x11),            // constraint: dr * 11 = drx11

            Log#(div_ratio, log_div_ratio),                // derives log_div_ratio
            Add#(log_div_ratio, 5, log_div_ratio_plus5),   // derives log_div_ratio_plus5
            Add#(log_div_ratio, 8, log_div_ratio_plus8),   // derives log_div_ratio_plus8

            Add#(log_div_ratio_plus5, x, log_div_ratio_plus8),    // (A) from use of signExtend
            Add#(6, y, log_div_ratio_plus8));                     // (B) from use of zeroExtend

	
	Wire#(Bit#(6)) maxbangWire <-mkWire;



	Reg#(Int#(log_div_ratio_plus5)) count_sum <-mkRegA(0);
	Reg#(Int#(log_div_ratio_plus8)) bangint<-mkRegA(0);

	Reg#(Bit#(6)) phase_vector<-mkRegA(0);



	let div_ratio_int = fromInteger(valueof(div_ratio));

	(* descending_urgency = "r_phase_update_req_1, r_accumlate_1" *)
	rule r_accumlate_1;
		bangint<=bangint+signExtend(count_sum);    // see (A) above
	endrule

	rule r_phase_update_req_1 (bangint>=unpack(zeroExtend(maxbangWire)) || bangint<=unpack((-zeroExtend(maxbangWire))));  // see (B) above
		bangint<=0;
		if (bangint<0)
			phase_vector<=phase_vector+1;
		else
			phase_vector<=phase_vector-1;
	endrule


	method Action input_data (Bit#(div_ratio_x11) in_data1,
                                  Bit#(div_ratio_x11) in_data2,
                                  Bit#(div_ratio)     act46,
                                  Bit#(1)             mode46,
                                  Bit#(1)             mode810);
		
		Int#(log_div_ratio_plus5) count_pos=0;
		Int#(log_div_ratio_plus5) count_neg=0;


		for (int word_index=1;word_index<=div_ratio_int;word_index=word_index+1)
		begin
			Bit#(11) data1_temp=in_data1[(word_index*11-1):(word_index-1)*11];
			Bit#(11) data2_temp=in_data2[(word_index*11-1):(word_index-1)*11];
			Bit#(1)  act46_temp=act46[word_index-1];

			Bit#(10) equal1vect=data1_temp[10:1]^data2_temp[10:1];
			Bit#(10) equal2vect=data1_temp[10:1]^data2_temp[9:0];		
			
			for (int i=0;i<4;i=i+1)
			begin
				if (equal1vect[i]==1'b1)
					count_pos=count_pos+1;
				if (equal2vect[i]==1'b1)
					count_neg=count_neg+1;
			end
	
			if (mode46==0 || (mode810==1 && act46_temp==1))
			begin
				for (int i=4;i<6;i=i+1)
				begin
					if (equal1vect[i]==1'b1)
						count_pos=count_pos+1;
					if (equal2vect[i]==1'b1)
						count_neg=count_neg+1;
				end
			end
		
			if (mode46==0)
			begin
				for (int i=6;i<8;i=i+1)
				begin
					if (equal1vect[i]==1'b1)
						count_pos=count_pos+1;
					if (equal2vect[i]==1'b1)
						count_neg=count_neg+1;
				end
			end
		
			if (mode46==0 && mode810==1)
			begin
				for (int i=8;i<10;i=i+1)
				begin
					if (equal1vect[i]==1'b1)
						count_pos=count_pos+1;
					if (equal2vect[i]==1'b1)
						count_neg=count_neg+1;
				end
			end	
		end	
	

			
		count_sum<=count_pos-count_neg;
	endmethod
	method Action static_inputs(Bit#(6) maxbang);
		maxbangWire<=maxbang;
	endmethod 


	method Bit#(6) get_phase;
		get_phase=phase_vector;
	endmethod
endmodule
