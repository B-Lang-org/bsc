/////////////////////////////////////////////////////////////////////////
/* Motion compensation block performs motion compensation decoding
   in the MPEG-4 decoder.
*/

package MCR;
import FIFOF::* ;
import Div::* ;
import ConfigReg :: *;

typedef enum {IDLE, 
              WAIT_LATCH, 
              LATCH, 
              START_READ_FIFO,
              CONT_READ_FIFO,
              PROCESS_MV,
              CHECK_MV,
              PROCESS_EVENEVEN_MV,
              PROCESS_ODDEVEN_MV,
              PROCESS_EVENODD_MV,
              PROCESS_ODDODD_MV} HSstates
        deriving (Eq,Bits);  

typedef Tuple2#(Bit#(a), Bit#(a)) Strobe#(type a)  ;

interface MCR_IFC;
  //Method used to set all inputs 
  method Action start(Bit#(1) rsValid,
                      Bit#(9) rsPixelVal,
                      Bit#(9) mbNum,
                      //Bit#(3) blkNum,
                      Bit#(4) cbpy,
                      Bit#(2) cbpc,
                      Bit#(1) hdr_rdy,
                      Bit#(1) mb_coded,
                      Bit#(1) isInter,
                      Bit#(48) mvx1,
                      Bit#(48) mvy1,
                      Bit#(8) refPixelValue,
                      Bit#(2) level); 
  method Bit#(1) rd_MV() ;
  method Bit#(18) refFrame_addr() ;
  method Bit#(1) rd_refFrame() ;
  method Bit#(1) pixelValid() ;
  method Bit#(8) pixelVal() ;
  method Bit#(18) curFrame_addr() ;  
endinterface : MCR_IFC

(* synthesize ,
   CLK = "clk",
   RST_N = "reset"
*)

module mkMCR (MCR_IFC);
  Reg#(HSstates)    state();
  mkReg#(IDLE)      t_state(state);

  RWire#(Bit#(1))   hdr_rdy1();
  mkRWire           t_hdr_rdy1(hdr_rdy1);

  RWire#(Bit#(1))   mb_coded();
  mkRWire           t_mb_coded(mb_coded);

  RWire#(Bit#(1))   isInter();
  mkRWire           t_isInter(isInter);

  //RWire#(Bit#(3))   blkNum();
  //mkRWire           t_blkNum(blkNum);
  Reg#(Bit#(3))     blkNum();
  mkReg#(0)          t_blkNum(blkNum);

  RWire#(Bit#(9))   mbNum();
  mkRWire           t_mbNum(mbNum);

  RWire#(Bit#(2))   level();
  mkRWire           t_level(level);

  RWire#(Bit#(1))   rsValid();
  mkRWire           t_rsValid(rsValid);

  RWire#(Bit#(9))   rsPixelVal();
  mkRWire           t_rsPixelVal(rsPixelVal);

  RWire#(Bit#(8))   refPixelValue();
  mkRWire           t_refPixelValue(refPixelValue);

  RWire#(Strobe#(48))  mvxy1();
  mkRWire                  the_mvxy1(mvxy1);

  RWire#(Bit#(4))  cbpy();
  mkRWire          the_cbpy(cbpy);

  RWire#(Bit#(2))  cbpc();
  mkRWire          the_cbpc(cbpc);

  Reg#(Bit#(48))    mvx();
  mkReg#(0)         the_mvx(mvx);

  Reg#(Bit#(48))    mvy();
  mkReg#(0)         the_mvy(mvy);

  Reg#(Bit#(16))    mvx_reg();
  mkReg#(0)         the_mvx_reg(mvx_reg);

  Reg#(Bit#(16))    mvy_reg();
  mkReg#(0)         the_mvy_reg(mvy_reg);

  Reg#(Bit#(16))    sumCol1();
  mkReg#(0)         the_sumCol1(sumCol1);

  Reg#(Bit#(16))    sumCol2();
  mkReg#(0)         the_sumCol2(sumCol2);

  Reg#(Bit#(1))     rd_MV_reg();
  mkReg#(0)         the_rd_MV_reg(rd_MV_reg);

  Reg#(Bit#(1))     pixelValid_reg();
  mkReg#(0)         the_pixelValid_reg(pixelValid_reg);

  Reg#(Bit#(8))     pixelVal_reg();
  mkReg#(0)         the_pixelVal_reg(pixelVal_reg);

  Reg#(Bit#(18))    curFrame_addr_reg();
  mkReg#(0)         the_curFrame_addr_reg(curFrame_addr_reg);

  Reg#(Bit#(18))    actualX();
  mkReg#(0)         the_actualX(actualX);

  Reg#(Bit#(18))    actualY();
  mkReg#(0)         the_actualY(actualY);

  FIFOF#(Bit#(9))    datafifo();
  mkSizedFIFOF#(384) the_datafifo(datafifo);

  Reg#(Maybe#(Bit#(7))) rsdatacnt();
  mkReg#(Invalid)       the_rsdatacnt(rsdatacnt);

  Reg#(Bit#(9))     pixelcnt();
  mkReg#(0)         the_pixelcnt(pixelcnt);

  Reg#(Bit#(6))     pixelcnt1();
  mkReg#(0)         the_pixelcnt1(pixelcnt1);

  Reg#(Bit#(7))     addr_cnt();
  mkReg#(0)         the_addr_cnt(addr_cnt);

  Reg#(Bit#(4))     addr_cnt_i();
  mkReg#(0)         the_addr_cnt_i(addr_cnt_i);

  Reg#(Bit#(4))     addr_cnt_j();
  mkReg#(0)         the_addr_cnt_j(addr_cnt_j);

  Reg#(Bit#(4))     a_cnt();
  mkReg#(0)         the_a_cnt(a_cnt);

  Reg#(Bit#(4))     pixcnt();
  mkReg#(0)         the_pixcnt(pixcnt);

  Reg#(Bit#(16))    idct_data();
  mkReg#(0)         the_idct_data(idct_data);

  Reg#(Bit#(7))     idct_data_cnt();
  mkReg#(0)         the_idct_data_cnt(idct_data_cnt);

  Reg#(Bit#(18))    refFrame_addr_reg();
  mkReg#(0)         the_refFrame_addr_reg(refFrame_addr_reg);

  Reg#(Bit#(1))     rd_refFrame_reg();
  mkReg#(0)         the_rd_refFrame_reg(rd_refFrame_reg);

  Reg#(Bit#(80))    a();
  mkConfigReg#(0)   the_a(a);

  Reg#(Bit#(8))     a0();
  mkConfigReg#(0)   the_a0(a0);

  Reg#(Bit#(8))     a1();
  mkConfigReg#(0)   the_a1(a1);

  Reg#(Bool)        motion_compensate();
  mkReg#(False)     the_motion_compensate(motion_compensate);

  Reg#(Bool)        empty_flag_d();
  mkReg#(False)     the_empty_flag_d(empty_flag_d);

  Reg#(Bool)        full_flag_d();
  mkReg#(False)     the_full_flag_d(full_flag_d);

  Bit#(2)           tmp_level = validValue(level.wget); 
  Bit#(4)           tmp_cbpy = fromMaybe(0 ,cbpy.wget);
  Bit#(2)           tmp_cbpc = fromMaybe(0 ,cbpc.wget);
  //Bit#(3)           tmp_blkNum = validValue(blkNum.wget);
  Bit#(3)           tmp_blkNum = blkNum;
  Bool              fifo_rd_cnd = (mb_coded.wget == Valid(0)) && 
                                   ((tmp_blkNum == 0 && (tmp_cbpy[3] == 1)) ||
                                    (tmp_blkNum == 1 && (tmp_cbpy[2] == 1)) ||
                                    (tmp_blkNum == 2 && (tmp_cbpy[1] == 1)) ||
                                    (tmp_blkNum == 3 && (tmp_cbpy[0] == 1)) ||
                                    (tmp_blkNum == 4 && (tmp_cbpc[1] == 1)) ||
                                    (tmp_blkNum == 5 && (tmp_cbpc[0] == 1)));
 
  Bit#(18)  width = ((tmp_level[1] == 1)? 22 : 11) * 
                    ((tmp_blkNum[2] == 1) ? 8 : 16);
  Bit#(18)  height = ((tmp_level[1] == 1) ? 18 : 9) * 
                     ((tmp_blkNum[2] == 1) ? 8 : 16);
  Bit#(18)  memOffset = (tmp_blkNum < 4) ? 0 : 
                         ((tmp_blkNum == 4) ? 
					     ((tmp_level[1] == 1) ? 18'd101376 : 18'd25344): 
					     ((tmp_level[1] == 1) ? 18'd126720 : 18'd31680));

  Bit#(8) tmp_compare = 8'd10*{4'd0,addr_cnt_i} + {4'd0,addr_cnt_j}; 

  Bit#(9) tmp_mbNum   = validValue(mbNum.wget);
  Bit#(9) frm_size    = (tmp_level[1] == 1) ? 9'd395 : 9'd98;
  Tuple3#(Bit#(1), Bit#(5),Bit#(5))  tmp_mbNum_remdiv = (tmp_level[1] == 1) ?
		                       funcQR({1'b0,tmp_mbNum},5'd22):
		                       funcQR({1'b0,tmp_mbNum},5'd11);
  Bit#(18) mult_factor = (tmp_blkNum[2] == 1) ?
		                 18'd8 :
		                 18'd16 ;

  Bit#(4) x_offset = (tmp_blkNum == 0)  ? 0 : 
                     ((tmp_blkNum == 1) ? 8 :
                     ((tmp_blkNum == 2) ? 0 :
                     ((tmp_blkNum == 3) ? 8 : 0 )));
	
  Bit#(4) y_offset = (tmp_blkNum == 0)  ? 0 : 
                     ((tmp_blkNum == 1) ? 0 :
                     ((tmp_blkNum == 2) ? 8 :
                     ((tmp_blkNum == 3) ? 8 : 0 )));
	

// Function to check if the x-coordinate of 
// reference block is within the frame
// it returns boundary value if out of frame.
  function Bit#(18) checkX(Bit#(18) x,Bit#(18) wdth);
	if (x[17] == 1)
	   return(18'd0);
    else if (x > (wdth - 1))
	   return(wdth - 1);
	else
	   return(x);
  endfunction

// Function to check if the y-coordinate of 
// reference block is within the frame
// it returns boundary value if out of frame.
  function Bit#(18) checkY(Bit#(18) y,Bit#(18) heght);
	if (y[17] == 1)
	   return(18'd0);
    else if (y > (heght - 1))
	   return(heght - 1);
	else
	   return(y);
  endfunction

// saturated signed pixel values to [min,max] range
// of [0,255]
  function Bit#(8) saturate(Bit#(16) in_data);
  if (in_data[15] == 1)
    return(8'd0);
  else if (in_data > 255)
    return(8'd255);
  else
    return(in_data[7:0]);
  endfunction
 
// function to calculate current frame address
// for storing pixels in frame buffer
  function Bit#(18) curFrame_addr_func(Tuple3#(Bit#(1), Bit#(5),Bit#(5)) tmp_mbNum_remdiv1, 
                                       Bit#(18) mult_factor1, 
                                       Bit#(4) y_offset1, 
                                       Bit#(6) pixelcnt11, 
                                       Bit#(18) width1, 
                                       Bit#(4) x_offset1, 
                                       Bit#(18) memOffset1);
      return((zeroExtend(tpl_3(tmp_mbNum_remdiv1)) * 
		                       zeroExtend(mult_factor1) + 
		                       zeroExtend(y_offset1) + 
							   zeroExtend(pixelcnt11[2:0])
							  ) * zeroExtend(width1) + 
							  (zeroExtend(tpl_2(tmp_mbNum_remdiv1)) * 
							   zeroExtend(mult_factor1) + 
							   zeroExtend(x_offset1) + 
							   zeroExtend(pixelcnt11[5:3])
							  ) + 
							  memOffset1);
  endfunction

// rule for writing residual pixel values into fifo
  rule write_fifo (True);
     if (rsValid.wget == Valid(1))
	begin
           rsdatacnt <= Valid(0);
	   if (isValid(rsPixelVal.wget))
	      begin
		 datafifo.enq(validValue(rsPixelVal.wget));
	      end
        end
     else if (rsdatacnt matches tagged Valid{ .x})
        begin
	   if (x == 63)
	      rsdatacnt <= Invalid;
	   else 
	      begin
		 rsdatacnt <= Valid( x + 1);
		 if (isValid(rsPixelVal.wget))
		    begin
		       datafifo.enq(validValue(rsPixelVal.wget));
		    end
	      end
	end
  endrule
	   
// motion compensation state machine is active only
// when headers for the blocks are available
/*
  rule wait_for_hdr_rdy (state == IDLE);
    if ((hdr_rdy1.wget == Valid(1))
	   begin
	     idct_data <= 0;
		 if (tmp_blkNum == 0)
		   begin
		     rd_MV_reg <= 1'b1;
	         state <= WAIT_LATCH;
		   end
		 else
		   begin
		     rd_MV_reg <= 1'b0;
	         state <= PROCESS_MV;
		   end
	   end
  endrule
  */

  rule wait_for_hdr_rdy (state == IDLE);
    idct_data_cnt <= 0;
    if (hdr_rdy1.wget == Valid(1)) 
	   begin
	     idct_data <= 0;
		 if (tmp_blkNum == 0)
		   begin
		     rd_MV_reg <= 1'b1;
	         state <= WAIT_LATCH;
		   end
		 else
		   begin
		     rd_MV_reg <= 1'b0;
	         state <= PROCESS_MV;
		   end
	   end
	else if ((hdr_rdy1.wget == Valid(0)) && (tmp_blkNum != 0))
      begin
		rd_MV_reg <= 1'b0;
		if ((mb_coded.wget == Valid(0)) && (isInter.wget == Valid(0)))
	       state <= START_READ_FIFO;
		else
	       state <= PROCESS_MV;
	    idct_data <= 0;
	  end
  endrule

  rule wait_motion_vectors (state == WAIT_LATCH);
	 state <= LATCH;
	 rd_MV_reg <= 1'b0;
  endrule

// reads motion vectors from header fifo
  rule read_motion_vectors (state == LATCH);
    if (mvxy1.wget matches tagged Valid({.x,.y}))
	   begin
		 if ((mb_coded.wget == Valid(0)) && (isInter.wget == Valid(0)))
	        state <= START_READ_FIFO;
		 else
	        state <= PROCESS_MV;
		 if (tmp_blkNum == 0)
		   begin
		     mvx  <= x;
		     mvy  <= y;
		   end
	   end
  endrule

  // execute rule when mbBlk is coded but not motion compensated
  // in this case output of IDCT block ( residual pixel values)
  // are the actual pixel values for current block.
  rule read_fifo_only (datafifo.notEmpty && ((state == START_READ_FIFO) || (state == CONT_READ_FIFO)));
   Bit#(9) tmp_val = 0;
   if (state == START_READ_FIFO)
	  begin
		tmp_val = datafifo.first;
	    pixelVal_reg <= saturate(signExtend(tmp_val));
	    datafifo.deq;
		pixelValid_reg <= 1'b1;
		curFrame_addr_reg <= (zeroExtend(tpl_3(tmp_mbNum_remdiv)) * 
		                      zeroExtend(mult_factor) + 
		                      zeroExtend(y_offset)
							 ) * zeroExtend(width) + 
							 (zeroExtend(tpl_2(tmp_mbNum_remdiv)) * 
							  zeroExtend(mult_factor) + 
							  zeroExtend(x_offset)
							 ) + 
							 memOffset;
		pixelcnt <= 1;
		state <= CONT_READ_FIFO;
	  end
	else if (pixelcnt < 384)
	  begin
		tmp_val = datafifo.first;
	    pixelVal_reg <= saturate(signExtend(tmp_val));
	    datafifo.deq;
		pixelValid_reg <= 1'b1;
	    pixelcnt <= pixelcnt + 1;
		curFrame_addr_reg <= (zeroExtend(tpl_3(tmp_mbNum_remdiv)) * 
		                      zeroExtend(mult_factor) + 
		                      zeroExtend(y_offset) + 
							  zeroExtend(pixelcnt[2:0])
							 ) * zeroExtend(width) + 
							 (zeroExtend(tpl_2(tmp_mbNum_remdiv)) * 
							  zeroExtend(mult_factor) + 
							  zeroExtend(x_offset) + 
							  zeroExtend(pixelcnt[5:3])
							 ) + 
							 memOffset;
		if (pixelcnt[5:0] == 63)
		   begin
		     if (blkNum == 5)
		       blkNum <= 0;
		     else
		       blkNum <= blkNum + 1;
		   end
	  end
	else 
	  begin
	    pixelValid_reg <= 1'b0;
	    pixelVal_reg <= 0;
		pixelcnt <= 0;
	  end
  endrule

  rule dont_read_fifo_when_empty (!datafifo.notEmpty && ((state == START_READ_FIFO) || (state == CONT_READ_FIFO)));
	pixelValid_reg <= 1'b0;
	pixelVal_reg <= 0;
	if (pixelcnt == 384)
	  begin
	    state <= IDLE;
		pixelcnt <= 0;
	  end
  endrule

  rule always_fire1(True);
    empty_flag_d <= datafifo.notEmpty;
	full_flag_d <= datafifo.notFull;
  endrule

  Bool empty_pulse = !datafifo.notEmpty && empty_flag_d;
  Bool full_pulse = !datafifo.notFull && full_flag_d;

  rule always_fire(empty_pulse);
     //$display("$$$$$$$$$$$$$$$$ MCR Datafifo is Empty $$$$$$$$$$$$$$$$$$$$$$");
  endrule

  rule always_fire2(full_pulse);
     //$display("$$$$$$$$$$$$$$$$ MCR Datafifo is FULL $$$$$$$$$$$$$$$$$$$$$$");
  endrule

// Rules processes motion vectors and determines the actual
// x-y coordinates of the reference block
  rule process_motion_vector (state == PROCESS_MV);
    Bit#(3) tmp_blkNum = 0;
    Bit#(16) sumMV_x = 0;
    Bit#(16) sumMV_y = 0;
    Bit#(16) tmp_sumMV_x = 0;
    Bit#(16) tmp_sumMV_y = 0;
    Bit#(16) tmp_div_x = 0;
    Bit#(16) tmp_div_y = 0;
    Bit#(2) lv_sumMV_x = 0;
    Bit#(2) lv_sumMV_y = 0;
    Bit#(16) t_MV_x = 0;
    Bit#(16) t_MV_y = 0;
    Bit#(4)  x_index = 0;
    Bit#(4)  y_index = 0;
    Bit#(1)  signMVx = 0;
    Bit#(1)  signMVy = 0;
    Bit#(16) tmp_MVx1 = 0;
    Bit#(16) tmp_MVy1 = 0;
    Bit#(16) mv_x = 0;
    Bit#(16) mv_y = 0;
     //case (validValue(blkNum.wget)) 
     case (blkNum) 
	   3'b000   :begin
				  mv_x = signExtend(mvx[47:36]);
				  mv_y = signExtend(mvy[47:36]);
	            end
	   3'b001   :begin
				  mv_x = signExtend(mvx[35:24]);
				  mv_y = signExtend(mvy[35:24]);
	            end
	   3'b010   :begin
				  mv_x = signExtend(mvx[23:12]);
				  mv_y = signExtend(mvy[23:12]);
	            end
	   3'b011  :begin
				  mv_x = signExtend(mvx[11:0]);
				  mv_y = signExtend(mvy[11:0]);
	            end
	   default :begin
				  sumMV_x = signExtend(mvx[47:36]) + 
				            signExtend(mvx[35:24]) + 
				            signExtend(mvx[23:12]) + 
				            signExtend(mvx[11:0]);
				  sumMV_y = signExtend(mvy[47:36]) + 
				            signExtend(mvy[35:24]) + 
				            signExtend(mvy[23:12]) + 
				            signExtend(mvy[11:0]);
				  signMVx = sumMV_x[15];
				  signMVy = sumMV_y[15];
				  tmp_sumMV_x = (signMVx == 1'b1) ? (-1) * sumMV_x : sumMV_x;
				  tmp_sumMV_y = (signMVy == 1'b1) ? (-1) * sumMV_y : sumMV_y;
				  tmp_div_x = tmp_sumMV_x >> 4;
				  tmp_div_y = tmp_sumMV_y >> 4;
				  x_index = tmp_sumMV_x[3:0];
				  y_index = tmp_sumMV_y[3:0];
				  lv_sumMV_x = (x_index < 3) ? 2'b00 : ((x_index < 14) ? 2'b01 : 2'b10);
				  lv_sumMV_y = (y_index < 3) ? 2'b00 : ((y_index < 14) ? 2'b01 : 2'b10);
				  t_MV_x = zeroExtend(lv_sumMV_x) + (tmp_div_x << 1);
				  t_MV_y = zeroExtend(lv_sumMV_y) + (tmp_div_y << 1);
				  mv_x = (signMVx == 1) ? (-1) * t_MV_x : t_MV_x;
				  mv_y = (signMVy == 1) ? (-1) * t_MV_y : t_MV_y;
	            end
		endcase

		tmp_MVx1 = {mv_x[15],mv_x[15:1]};
		tmp_MVy1 = {mv_y[15],mv_y[15:1]};
		mvx_reg <= mv_x;
		mvy_reg <= mv_y;
		actualX <= {13'd0,tpl_2(tmp_mbNum_remdiv)} * mult_factor + 
		           signExtend(tmp_MVx1) + {14'd0,x_offset};
		actualY <= {13'd0,tpl_3(tmp_mbNum_remdiv)} * mult_factor + 
		           signExtend(tmp_MVy1) + {14'd0,y_offset};
		state   <= CHECK_MV ;
  endrule

// checks the motion vectors to decide the type
// of motion vector alogrithm to be used for the
// current block.
  rule check_MV (state == CHECK_MV);
     if ((fifo_rd_cnd && datafifo.notEmpty) || !fifo_rd_cnd)
	    begin
          if ((mvx_reg[0] == 1) && (mvy_reg[0] == 0))
	        begin
	         state <= PROCESS_ODDEVEN_MV;
		   //$display("oddeven case");
	        end
          else if ((mvx_reg[0] == 0) && (mvy_reg[0] == 1))
            begin
              state <= PROCESS_EVENODD_MV;
               //$display("evenodd case");
            end
          else if ((mvx_reg[0] == 1) && (mvy_reg[0] == 1))
            begin
              state <= PROCESS_ODDODD_MV;
               //$display("oddodd case");
            end
	      else
	        begin
	         state <= PROCESS_EVENEVEN_MV;
		   //$display("eveneven case");
	        end
	       //$display("**************** Macroblock Number = %d blk_num = %d cbpy = %h cbpc = %h mb_coded = %d",tmp_mbNum,tmp_blkNum,tmp_cbpy,tmp_cbpc,validValue(mb_coded.wget));
	       //$display("actualX = %h actualY = %h ",actualX,actualY);
	    end
  endrule
  
// rule to read residual pixelvalues from the IDCT input fifo
  rule process_eveneven_getdatafifo ((((addr_cnt >= 1) && (state == PROCESS_EVENEVEN_MV)) ||
									 ((tmp_compare >= 12) && (state == PROCESS_ODDEVEN_MV)) || 
									 ((tmp_compare >= 3)  && (state == PROCESS_EVENODD_MV)) || 
									 ((tmp_compare >= 14)  && (state == PROCESS_ODDODD_MV))) 
                                      && fifo_rd_cnd);
     if (datafifo.notEmpty && 
	     (((addr_cnt < 65)  && (state == PROCESS_EVENEVEN_MV)) || 
	     ((!(addr_cnt_i == 9 && addr_cnt_j == 3)) && (state == PROCESS_ODDEVEN_MV)) || 
		 ((!(addr_cnt_i == 8 && addr_cnt_j == 4)) && (state == PROCESS_EVENODD_MV)&& (a_cnt != 0)) || 
	     ((!(addr_cnt_i == 9 && addr_cnt_j == 4)) && (state == PROCESS_ODDODD_MV) && (a_cnt != 0))  
		 ) && (idct_data_cnt != 64)
		)
	   begin
		 idct_data <= signExtend(datafifo.first);
	     datafifo.deq;
		 idct_data_cnt <= idct_data_cnt + 1;
	   end
  endrule

// rule generating the reference addresses in case of
// both motion vectors being even.
  rule process_eveneven_getrefdata (state == PROCESS_EVENEVEN_MV);
   Bit#(18) tmp_y = actualY + {15'd0,addr_cnt[2:0]};
   Bit#(18) tmp_x = actualX + {15'd0,addr_cnt[5:3]};
	   if (addr_cnt < 64)
	     begin
	       refFrame_addr_reg <= checkY(tmp_y,height) * width +
	                            checkX(tmp_x,width) + memOffset;
	       rd_refFrame_reg <= 1'b1;
		   if (addr_cnt >= 1)
		      motion_compensate <= True;
	       else
		      motion_compensate <= False;
		   addr_cnt <= addr_cnt + 1;
	     end
	   else if (addr_cnt == 64)
	     begin
	       rd_refFrame_reg <= 1'b0;
		   addr_cnt <= addr_cnt + 1;
	     end
	   else if (addr_cnt == 65)
		   addr_cnt <= addr_cnt + 1;
	   else if (addr_cnt == 66)
	     begin
		   addr_cnt <= 0;
		   motion_compensate <= False;
		   state <= IDLE;
	       pixelValid_reg <= 1'b0;
	       pixelcnt1 <= 0;
		   if (blkNum == 5)
		     blkNum <= 0;
		   else
		     blkNum <= blkNum + 1;
	     end
  endrule

  //rule send_output (motion_compensate);
  rule send_output ((state == PROCESS_EVENEVEN_MV) && (addr_cnt >= 2) &&
                     !(addr_cnt == 66));
	 Bit#(16) tmp_pixelVal_reg = 0;
	 Bit#(7) pixcnt = addr_cnt - 2;
	     tmp_pixelVal_reg = {8'd0,validValue(refPixelValue.wget)} + idct_data;
	     pixelVal_reg <= saturate(tmp_pixelVal_reg);
	     pixelValid_reg <= 1'b1;
	     pixelcnt1 <= pixelcnt1 + 1;
	     curFrame_addr_reg <= curFrame_addr_func(tmp_mbNum_remdiv,mult_factor,y_offset,pixelcnt1,width,x_offset,memOffset);
  endrule

// rule generating the reference addresses in case of
// x-motion vector being odd and y-motion vector being even
  rule process_oddeven_getrefdata (state == PROCESS_ODDEVEN_MV);
   Bit#(18) tmp_y = actualY + {14'd0,addr_cnt_j};
   Bit#(18) tmp_x = actualX + {14'd0,addr_cnt_i};
	     if ((addr_cnt_i < 9) && (addr_cnt_j < 8))
	       begin
	         refFrame_addr_reg <= checkY(tmp_y,height) * width +
	                              checkX(tmp_x,width) + memOffset;
	         rd_refFrame_reg <= 1'b1;
             if (addr_cnt_j == 7)
		       begin
		         addr_cnt_i <= addr_cnt_i + 1;
			     addr_cnt_j <= 4'd0;
		       end
		     else 
		       addr_cnt_j <= addr_cnt_j + 1;
	       end
	     else if (addr_cnt_i == 9 && addr_cnt_j == 3)
	       begin
	         addr_cnt_j <= 4'd0;
	         addr_cnt_i <= 4'd0;
		     state      <= IDLE;
	         pixelValid_reg <= 1'b0;
		     a <= 80'd0;
		     pixelcnt1 <= 0;
		     if (blkNum == 5)
		       blkNum <= 0;
		     else
		       blkNum <= blkNum + 1;
	       end
	     else 
	       begin
	         rd_refFrame_reg <= 1'b0;
	         addr_cnt_j <= addr_cnt_j + 1;
	       end
  endrule

  rule process_oddeven_getrefdata1 ((state == PROCESS_ODDEVEN_MV) && (tmp_compare >= 2));
	 a <= {8'd0,a[63:0],validValue(refPixelValue.wget)};
  endrule 

  rule process_oddeven_outdata ((state == PROCESS_ODDEVEN_MV) && 
                                (tmp_compare >= 13) && 
								!(addr_cnt_i == 9 && addr_cnt_j == 3));
	 Bit#(16) tmp_pixelVal_reg0 = ({8'd0,a[71:64]} + {8'd0,a[7:0]} + 1) >> 1 ;
	 Bit#(16) tmp_pixelVal_reg = tmp_pixelVal_reg0 + idct_data;
	 Bit#(4)  index_addr_cnt_i    = addr_cnt_i - 1;
	 Bit#(4)  index_addr_cnt_j    = addr_cnt_j - 3;
	     pixelcnt1 <= pixelcnt1 + 1;
	     pixelVal_reg <= saturate(tmp_pixelVal_reg);
	     pixelValid_reg <= 1'b1;
	     curFrame_addr_reg <= curFrame_addr_func(tmp_mbNum_remdiv,mult_factor,y_offset,pixelcnt1,width,x_offset,memOffset);
  endrule 

// rule generating the reference addresses in case of
// x-motion vector being even and y-motion vector being odd
  rule process_evenodd_getrefdata (state == PROCESS_EVENODD_MV);
   Bit#(18) tmp_y = actualY + {14'd0,addr_cnt_j};
   Bit#(18) tmp_x = actualX + {14'd0,addr_cnt_i};
	     if ((addr_cnt_i < 8) && (addr_cnt_j < 9))
	       begin
	         refFrame_addr_reg <= checkY(tmp_y,height) * width +
	                              checkX(tmp_x,width) + memOffset;
	         rd_refFrame_reg <= 1'b1;
             if (addr_cnt_j == 8)
		       begin
		         addr_cnt_i <= addr_cnt_i + 1;
			     addr_cnt_j <= 4'd0;
		       end
		     else 
		       addr_cnt_j <= addr_cnt_j + 1;
	       end
	     else if (addr_cnt_i == 8 && addr_cnt_j == 4)
	       begin
	         addr_cnt_j <= 4'd0;
	         addr_cnt_i <= 4'd0;
		     state      <= IDLE;
	         pixelValid_reg <= 1'b0;
		     a_cnt <= 0;
		     pixelcnt1 <= 0;
		     if (blkNum == 5)
		       blkNum <= 0;
		     else
		       blkNum <= blkNum + 1;
	       end
	     else 
	       begin
	         rd_refFrame_reg <= 1'b0;
	         addr_cnt_j <= addr_cnt_j + 1;
	       end
  endrule

  rule process_evenodd_geta0a1 ((state == PROCESS_EVENODD_MV) && (tmp_compare >= 2));
	     if (a_cnt == 0)
	       begin
	         a0 <= validValue(refPixelValue.wget);
	         a1 <= validValue(refPixelValue.wget);
		     a_cnt <= a_cnt + 1;
	       end
	     else
	       begin
	         a0 <= a1;
	         a1 <= validValue(refPixelValue.wget);
		     if (a_cnt == 8)
		       a_cnt <= 0;
		     else
		       a_cnt <= a_cnt + 1;
	       end
  endrule 

  rule process_evenodd_outdata ((state == PROCESS_EVENODD_MV) && 
                                (tmp_compare >= 4) && 
								!(addr_cnt_i == 8 && addr_cnt_j == 4));
	 Bit#(16) tmp_pixelVal_reg01 = ({8'd0,a0} + {8'd0,a1} + 1) >> 1 ;
	 Bit#(16) tmp_pixelVal_reg = tmp_pixelVal_reg01 + idct_data;
	 Bit#(4)  index_addr_cnt_i    = addr_cnt_i ;
	 Bit#(4)  index_addr_cnt_j    = addr_cnt_j - 4;
	     if (pixcnt == 8)
	       begin
	         pixelValid_reg <= 1'b0;
		     pixcnt <= 0;
	       end
	     else 
	       begin
		     pixcnt <= pixcnt + 1;
		     pixelcnt1 <= pixelcnt1 + 1;
	         pixelVal_reg <= saturate(tmp_pixelVal_reg);
	         pixelValid_reg <= 1'b1;
	         curFrame_addr_reg <= curFrame_addr_func(tmp_mbNum_remdiv,mult_factor,y_offset,pixelcnt1,width,x_offset,memOffset);
	       end
  endrule 

// rule generating the reference addresses in case of
// both motion vectors being odd.
  rule process_oddodd_getrefdata (state == PROCESS_ODDODD_MV);
   Bit#(18) tmp_y = actualY + {14'd0,addr_cnt_j};
   Bit#(18) tmp_x = actualX + {14'd0,addr_cnt_i};
	     if ((addr_cnt_i < 9) && (addr_cnt_j < 9))
	       begin
	         refFrame_addr_reg <= checkY(tmp_y,height) * width +
	                              checkX(tmp_x,width) + memOffset;
	         rd_refFrame_reg <= 1'b1;
             if (addr_cnt_j == 8)
		       begin
		         addr_cnt_i <= addr_cnt_i + 1;
			     addr_cnt_j <= 4'd0;
		       end
		     else 
		       addr_cnt_j <= addr_cnt_j + 1;
	       end
	     else if (addr_cnt_i == 9 && addr_cnt_j == 4)
	       begin
	         addr_cnt_j <= 4'd0;
	         addr_cnt_i <= 4'd0;
		     state      <= IDLE;
	         pixelValid_reg <= 1'b0;
		     a_cnt      <= 0;
		     pixelcnt1   <= 0;
		     if (blkNum == 5)
		       blkNum <= 0;
		     else
		       blkNum <= blkNum + 1;
	       end
	     else 
	       begin
	         rd_refFrame_reg <= 1'b0;
	         addr_cnt_j <= addr_cnt_j + 1;
	       end
  endrule

  rule process_oddodd_getrefdata1 ((state == PROCESS_ODDODD_MV) && (tmp_compare >= 2));
	 a <= {a[71:0],validValue(refPixelValue.wget)};
  endrule 

  rule process_oddodd_sumdata ((state == PROCESS_ODDODD_MV) && 
                                (tmp_compare >= 13) &&
	                            !(addr_cnt_i == 9 && addr_cnt_j == 4));
	     if (a_cnt == 0)
	       begin
	         sumCol1 <= {8'd0,a[79:72]} + {8'd0,a[7:0]};
	         sumCol2 <= {8'd0,a[79:72]} + {8'd0,a[7:0]};
		     a_cnt <= a_cnt + 1;
	       end
	     else
	       begin
	         sumCol2 <= {8'd0,a[79:72]} + {8'd0,a[7:0]};
	         sumCol1 <= sumCol2;
		     if (a_cnt == 8)
		       a_cnt <= 0;
		     else
		       a_cnt <= a_cnt + 1;
	       end
  endrule 

  rule process_oddodd_outdata ((state == PROCESS_ODDODD_MV) && 
                                (tmp_compare >= 15) && 
								!(addr_cnt_i == 9 && addr_cnt_j == 5));
	 Bit#(16) tmp_pixelVal_reg11 = (sumCol1 + sumCol2 + {14'd0,2'd2}) >> 2 ;
	 Bit#(16) tmp_pixelVal_reg1 = tmp_pixelVal_reg11 + idct_data;
	 Bit#(4)  index_addr_cnt_i    = addr_cnt_i - 1;
	 Bit#(4)  index_addr_cnt_j    = addr_cnt_j - 5;
	     if (pixcnt == 8)
	       begin
	         pixelValid_reg <= 1'b0;
		     pixcnt <= 0;
	       end
	     else 
	       begin
		     pixcnt <= pixcnt + 1;
		     pixelcnt1 <= pixelcnt1 + 1;
	         pixelVal_reg <= saturate(tmp_pixelVal_reg1);
	         pixelValid_reg <= 1'b1;
	         curFrame_addr_reg <= curFrame_addr_func(tmp_mbNum_remdiv,mult_factor,y_offset,pixelcnt1,width,x_offset,memOffset);
	       end
  endrule 

  method start (rsValid1,
                rsPixelVal1,
                mbNum1,
                //blkNum1,
                cbpy1,
                cbpc1,
                hdr_rdy,
                mb_coded1,
                isInter1,
                mvx1,
                mvy1,
                refPixelValue1,
                level1);
    action
	  rsValid.wset(rsValid1);
	  rsPixelVal.wset(rsPixelVal1);
	  mbNum.wset(mbNum1);
	  //blkNum.wset(blkNum1);
	  cbpy.wset(cbpy1);
	  cbpc.wset(cbpc1);
	  hdr_rdy1.wset(hdr_rdy);
	  mb_coded.wset(mb_coded1);
	  isInter.wset(isInter1);
	  refPixelValue.wset(refPixelValue1);
	  mvxy1.wset(tuple2(mvx1,mvy1));
	  level.wset(level1);
	endaction
  endmethod : start
    
  method rd_MV() ;
    rd_MV = rd_MV_reg;
  endmethod : rd_MV

  method refFrame_addr() ;
    refFrame_addr = refFrame_addr_reg;
  endmethod : refFrame_addr

  method rd_refFrame() ;
    rd_refFrame = rd_refFrame_reg;
  endmethod : rd_refFrame

  method pixelVal() ;
    pixelVal = pixelVal_reg;
  endmethod : pixelVal

  method pixelValid() ;
    pixelValid = pixelValid_reg;
  endmethod : pixelValid

  method curFrame_addr() ;
    curFrame_addr = curFrame_addr_reg;
  endmethod : curFrame_addr

endmodule : mkMCR

endpackage : MCR
