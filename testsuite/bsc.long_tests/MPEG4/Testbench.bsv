/////////////////////////////////////////////////////////////////////////

import Mpeg4::*;
import RegFile::*;
import Screen::*;

typedef enum {FIRST,NEXT,NEXT1,NEXT2} CHECK_STATES
deriving (Eq,Bits);  
(*
 always_ready,
 always_enabled,
 synthesize
 *)

module mkTestbench ();
   Mpeg4_IFC dut();
   mkMpeg4 the_dut(dut);

   // Error: value processing error at line 208670 of file 'bitstream.txt'
   //    Malformed value.
   // Warning: file 'y.txt' does not completely fill the memory 'the_y_io'.
   // Warning: file 'u.txt' does not completely fill the memory 'the_u_io'.
   // Warning: file 'v.txt' does not completely fill the memory 'the_v_io'.

   RegFile#(Bit#(20),Bit#(8)) stimulus_io();
   mkRegFileLoad#("bitstream.txt",0,208670) the_stimulus_io(stimulus_io);

   RegFile#(Bit#(16),Bit#(113)) mbhdr();
   mkRegFileLoad#("usable_mb_hdr.txt",0,41578) the_mbhdr(mbhdr);

   RegFile#(Bit#(24),Bit#(8)) y_io();
   mkRegFileLoad#("y.txt",0,10644480) the_y_io(y_io);

   RegFile#(Bit#(24),Bit#(8)) u_io();
   mkRegFileLoad#("u.txt",0,2661120) the_u_io(u_io);

   RegFile#(Bit#(24),Bit#(8)) v_io();
   mkRegFileLoad#("v.txt",0,2661120) the_v_io(v_io);

   //RegFile#(Bit#(24),Bit#(8)) frame_buf_io();
   //mkRegFileLoad#("frames.txt",0,15966719) the_frame_buf_io(frame_buf_io);

   Reg#(CHECK_STATES) state();
   mkReg#(FIRST)  the_state(state);

   Reg#(Bool)     condition();
   mkReg#(True)  the_condition(condition);

   Reg#(Bool)     fail();
   mkReg#(False)  the_fail(fail);

   Reg#(Bool)     read_cond();
   mkReg#(False)  the_read_cond(read_cond);

   Reg#(Bit#(20)) counter();
   mkReg#(0)  the_counter(counter);

   Reg#(Bit#(16)) mbhdr_cnt();
   mkReg#(0)  the_mbhdr_cnt(mbhdr_cnt);

   Reg#(Bit#(24)) dct_cnt();
   mkReg#(0)  the_dct_cnt(dct_cnt);

   Reg#(Bit#(24)) y_cnt();
   mkReg#(0)  the_y_cnt(y_cnt);

   Reg#(Bit#(24)) u_cnt();
   mkReg#(0)  the_u_cnt(u_cnt);

   Reg#(Bit#(24)) v_cnt();
   mkReg#(0)  the_v_cnt(v_cnt);

   Reg#(Bit#(6)) read_counter();
   mkReg#(0)  the_read_counter(read_counter);


   Reg#(Bit#(3)) blk_cnt();
   mkReg#(0)  the_blk_cnt(blk_cnt);

   Reg#(Bit#(24)) data_cnt();
   mkReg#(0)  the_data_cnt(data_cnt);

   Reg#(Bit#(3))    ignore_cnt();
   mkReg#(0) the_ignore_cnt(ignore_cnt);

   Reg#(Bit#(24)) vop_no();
   mkReg#(0)  the_vop_no(vop_no);

   Reg#(int) frameCnt <- mkReg(0);

   rule fire_once(condition);
      dut.get_host_strobe(1);
      dut.get_host_select(2'b00);
      dut.get_host_address(8'h00);
      dut.get_host_datain(8'h01);
      condition <= False;
      //$display ("fire_once is done");

      // TODO: OPEN RGB window
   endrule

   rule give_simulatus (dut.vd_rd == 1'b1) ;
      let inputdata = stimulus_io.sub (counter);

      dut.get_vd_valid(1'b1);
      dut.get_vd_data(inputdata);
      counter <= counter + 1;
      if (counter == 208669 )
         begin
            if (fail)
               $display ("Simulation Fails");
            else
               $display ("Simulation Passes");
            $finish (2'b00);
         end
   endrule
   
   rule no_stumulus (dut.vd_rd != 1'b1);
      dut.get_vd_valid(1'b0);
   endrule
   
   /*
   rule check_result ((dut.pixelValid == 1'b1) || read_cond);
   Bit#(8)    exp_pixelVal;
   Bit#(24)    data_cnt;
   let actual_data = dut.pixelVal;
   if (blk_cnt < 4)
   begin
   exp_pixelVal = y_io.sub(y_cnt);
   y_cnt <= y_cnt + 1;
   data_cnt = y_cnt;
   end
            else if (blk_cnt == 4)
   begin
   exp_pixelVal = u_io.sub(u_cnt);
   u_cnt <= u_cnt + 1;
   data_cnt = u_cnt;
   end
            else 
   begin
   exp_pixelVal = v_io.sub(v_cnt);
   v_cnt <= v_cnt + 1;
   data_cnt = v_cnt;
   end

   if (read_counter == 63)
   begin
   read_counter <= 0;
   read_cond <= False;
   if (blk_cnt == 5)
   blk_cnt <= 0;
	    else
   blk_cnt <= blk_cnt + 1;
   end
	    else
   begin
   read_counter <= read_counter + 1;
   read_cond <= True;
   end
   if (actual_data == exp_pixelVal)
   begin
   //$display("Data Matched %h data_cnt = %d",exp_pixelVal,dct_cnt);
   ;
   end
	    else
   begin
   $display("Data MisMatch Expected = %h Actual = %h data_cnt = %d blk_cnt = %d",exp_pixelVal,actual_data,data_cnt,blk_cnt);
   fail <= True;
   end
   endrule
   */

   rule check_result0 (state == FIRST);
      if (dut.vop_done)
	 begin
            dut.read_vop(1'b1);
            state <= NEXT;
	    ignore_cnt  <= 0;
	    //$display("@@@@@@@@@@@@ VOP No %d  @@@@@@@@@@@",vop_no);
	 end
      else
         dut.read_vop(1'b0);
   endrule

   ////////////////////////////////////////////////////////////
   ////////////////////////////////////////////////////////////
   Screen screen <- mkScreen;

   rule check_result1 (state == NEXT);
      Bit#(8) exp_data = 0;
      if (!(dut.vop_rd_done && (ignore_cnt == 5)))
	 begin
	    if (ignore_cnt !=5)
	       ignore_cnt <= ignore_cnt + 1;
            dut.read_vop(1'b1);
            state <= NEXT;
	    Bit#(8) actual_data = dut.vop_data;
	    if (data_cnt != 38016)  begin
	       if (data_cnt < 25344)begin
	          exp_data = y_io.sub(y_cnt);
		  y_cnt <= y_cnt + 1;
		  data_cnt <= data_cnt + 1;
		  blk_cnt <= 0;
	       end
	       else if (data_cnt < 31680) begin
	          exp_data = u_io.sub(u_cnt);
		  u_cnt <= u_cnt + 1;
		  data_cnt <= data_cnt + 1;
		  blk_cnt <= 4;
	       end
	       else begin
	          exp_data = v_io.sub(v_cnt);
		  v_cnt <= v_cnt + 1;
		  data_cnt <= data_cnt + 1;
		  blk_cnt <= 5;
	       end

               // $display("viewer: data sent");
               screen.send( actual_data );

	       if (actual_data != exp_data) begin
		  $display("Data MisMatch Expected = %h Actual = %h data_cnt = %d y_cnt = %d u_cnt = %d v_cnt = %d blk_cnt = %d",exp_data,actual_data,data_cnt,y_cnt,u_cnt,v_cnt,blk_cnt);
		  fail <= True;
	       end
	       //else
	       // $display("Data Matched %h data_cnt = %d blk_cnt = %d",exp_data,data_cnt,blk_cnt);
	    end

  	    else begin
               $display("viewer: frame sent!");
               frameCnt <= frameCnt + 1;
	       data_cnt <= 0;
	       blk_cnt <= 0;
	    end

	 end
	          else
                     begin
	                dut.read_vop(1'b0);
		        state <= NEXT1;
		        data_cnt <= 0;
		        blk_cnt <= 0;
		        vop_no <= vop_no + 1;
	             end
   endrule

   rule resume_decoder(state == NEXT1);
      dut.get_host_strobe(1);
      dut.get_host_select(2'b00);
      dut.get_host_address(8'h01);
      dut.get_host_datain(8'h02);
      //$display ("resume is done");
      state <= FIRST;
      dut.read_vop(1'b0);
   endrule

   rule stopearlyfortesting (frameCnt == 30);
      $display("30 frames seen - stopping early!!!!");
      $finish;
   endrule

endmodule
