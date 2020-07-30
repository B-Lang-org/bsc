/////////////////////////////////////////////////////////////////////////
/* Performs arithmetic calculations related to MV prediction
*/

package MVarith;

import Defines :: *;

interface MVarith_IFC;
  method Bit#(12) median_x (Bit#(12) a,Bit#(12) b,Bit#(12) c);
  method Bit#(12) median_y (Bit#(12) a,Bit#(12) b,Bit#(12) c);
  method Bit#(12) shift_left (Bit#(3) r_size);
  method Bit#(12) get_high (Bit#(3) r_size);
  method Bit#(12) get_low (Bit#(3) r_size);
  method Bit#(12) getMVDx (Bit#(12) horizontal_mv_data,Bit#(12) horizontal_mv_residual,Bit#(12) f,Bit#(3) r_size);
  method Bit#(12) getMVDy (Bit#(12) vertical_mv_data,Bit#(12) vertical_mv_residual,Bit#(12) f,Bit#(3) r_size);
  method Bit#(12) saturate_mvx(Bit#(12) mvx,Bit#(12) high,Bit#(12) low,Bit#(12) range);
  method Bit#(12) saturate_mvy(Bit#(12) mvy,Bit#(12) high,Bit#(12) low,Bit#(12) range);
  method MVtype check_valid (Maybe#(Bit#(12)) mv1_x,Maybe#(Bit#(12)) mv1_y,
						  Maybe#(Bit#(12)) mv2_x,Maybe#(Bit#(12)) mv2_y,
						  Maybe#(Bit#(12)) mv3_x,Maybe#(Bit#(12)) mv3_y);
endinterface: MVarith_IFC

function Bit#(12) func_median(Bit#(12) a , Bit#(12) b , Bit#(12) c);
  Bit#(12) res;
  case ({a[11],b[11],c[11]})
    3'b000:
           begin
	         if (((a <= b) && (a >= c)) || ((a >= b) && (a <= c)))
	           res = a;
	         else if (((b <= c) && (b >= a)) || ((b >= c) && (b <= a)))
	           res = b;
	         else
	           res = c;
	       end 
    3'b001:
           begin
	         if (a <= b) 
	           res = a;
	         else
	           res = b;
	       end 
    3'b010:
           begin
	         if (a <= c) 
	           res = a;
	         else
	           res = c;
	       end 
    3'b011:
           begin
	         if (b <= c) 
	           res = c;
	         else
	           res = b;
	       end 
    3'b100:
           begin
	         if (b <= c) 
	           res = b;
	         else
	           res = c;
	       end 
    3'b101:
           begin
	         if (a <= c) 
	           res = c;
	         else
	           res = a;
	       end 
    3'b110:
           begin
	         if (a <= b) 
	           res = b;
	         else
	           res = a;
	       end 
    3'b111:
           begin
	         if (((a >= b) && (a <= c)) || ((a <= b) && (a >= c)))
	           res = a;
	         else if (((b >= a) && (b <= c)) || ((b <= a) && (b >= c)))
	           res = b;
	         else
	           res = c;
	       end 
    default : res = 0;
    endcase
  return res;
endfunction

function Bit#(12) func_shift_left(Bit#(12) value ,Bit#(3) r_size);
  Bit#(12) f;
  case (r_size)
    3'd0 : f = value;
	3'd1 : f = {value[10:0],1'b0};
	3'd2 : f = {value[9:0],2'b00};
	3'd3 : f = {value[8:0],3'b000};
	3'd4 : f = {value[7:0],4'b0000};
	3'd5 : f = {value[6:0],5'b00000};
	3'd6 : f = {value[5:0],6'b000000};
	3'd7 : f = {value[4:0],7'b0000000};
	default : f = 0;
  endcase
  return f;
endfunction

function Bit#(12) func_get_mvd(Bit#(12) mv_data,Bit#(12) mv_residual,Bit#(12) f,Bit#(3) r_size);
  Bit#(12) res;
  Bit#(12) abs_mv_data = (mv_data[11] == 1) ? ~mv_data : (mv_data - 1);
  if ((f == 1) || (mv_data == 0))
    res = mv_data; 
  else
    begin
	  let mvd = func_shift_left(abs_mv_data,r_size) + mv_residual + 1;
	  if (mv_data[11] == 1)
	    res = ~mvd + 1;
	  else
	    res = mvd ;
	end
  return res;
endfunction

function Bit#(12) saturate(Bit#(12) mv,Bit#(12) high,Bit#(12) low,Bit#(12) range);
  Bit#(12) res;
  if ((mv[11] == 1) && (mv < low))
    res = mv + range;
  else if ((mv[11] == 0) && (mv > high))
    res = mv - range;
  else
    res = mv;
  return res;
endfunction

function  MVtype check_valid_func (Maybe#(Bit#(12)) mv1_x,Maybe#(Bit#(12)) mv1_y,
						 Maybe#(Bit#(12)) mv2_x,Maybe#(Bit#(12)) mv2_y,
						 Maybe#(Bit#(12)) mv3_x,Maybe#(Bit#(12)) mv3_y);
  Bit#(12) tmp_mv1_x;
  Bit#(12) tmp_mv1_y;
  Bit#(12) tmp_mv2_x;
  Bit#(12) tmp_mv2_y;
  Bit#(12) tmp_mv3_x;
  Bit#(12) tmp_mv3_y;
  MVtype res;

	 if ((mv1_x == Nothing) && (mv1_y == Nothing) && 
	      (mv2_x == Nothing) && (mv2_y == Nothing) &&
	      (mv3_x != Nothing) && (mv3_y != Nothing))
	   begin
	     tmp_mv3_x = validValue(mv3_x);
	     tmp_mv3_y = validValue(mv3_y);
	     tmp_mv1_x = tmp_mv3_x ;
	     tmp_mv1_y = tmp_mv3_y ;
	     tmp_mv2_x = tmp_mv3_x ;
	     tmp_mv2_y = tmp_mv3_y ;
	   end
	 else if ((mv1_x != Nothing) && (mv1_y != Nothing) && 
	      (mv2_x == Nothing) && (mv2_y == Nothing) &&
	      (mv3_x == Nothing) && (mv3_y == Nothing))
	   begin
	     tmp_mv1_x = validValue(mv1_x);
	     tmp_mv1_y = validValue(mv1_y);
	     tmp_mv2_x = tmp_mv1_x ;
	     tmp_mv2_y = tmp_mv1_y ;
	     tmp_mv3_x = tmp_mv1_x ;
	     tmp_mv3_y = tmp_mv1_y ;
	   end
	 else if ((mv1_x == Nothing) && (mv1_y == Nothing) && 
	      (mv2_x != Nothing) && (mv2_y != Nothing) &&
	      (mv3_x == Nothing) && (mv3_y == Nothing))
	   begin
	     tmp_mv2_x = validValue(mv2_x);
	     tmp_mv2_y = validValue(mv2_y);
	     tmp_mv1_x = tmp_mv2_x ;
	     tmp_mv1_y = tmp_mv2_y ;
	     tmp_mv3_x = tmp_mv2_x ;
	     tmp_mv3_y = tmp_mv2_y ;
	   end
	 else if ((mv1_x == Nothing) && (mv2_x == Nothing) && 
	          (mv1_y == Nothing) && (mv2_y == Nothing) &&
	          (mv3_x == Nothing) && (mv3_y == Nothing))
	   begin
	     tmp_mv3_x = 0;
	     tmp_mv3_y = 0;
	     tmp_mv1_x = 0;
	     tmp_mv1_y = 0;
	     tmp_mv2_x = 0;
	     tmp_mv2_y = 0;
	   end
	 else
	   begin
	     if ((mv1_x == Nothing) && (mv1_y == Nothing))
		   begin
	         tmp_mv1_x = 0;
	         tmp_mv1_y = 0;
		   end
		 else
		   begin
	         tmp_mv1_x = validValue(mv1_x);
	         tmp_mv1_y = validValue(mv1_y);
		   end
	     if ((mv2_x == Nothing) && (mv2_y == Nothing))
		   begin
	         tmp_mv2_x = 0;
	         tmp_mv2_y = 0;
		   end
		 else
		   begin
	         tmp_mv2_x = validValue(mv2_x);
	         tmp_mv2_y = validValue(mv2_y);
		   end
	     if ((mv3_x == Nothing) && (mv3_y == Nothing))
		   begin
	         tmp_mv3_x = 0;
	         tmp_mv3_y = 0;
		   end
		 else
		   begin
	         tmp_mv3_x = validValue(mv3_x);
	         tmp_mv3_y = validValue(mv3_y);
		   end
	   end
  res = tuple6(tmp_mv1_x,tmp_mv1_y,tmp_mv2_x,tmp_mv2_y,tmp_mv3_x,tmp_mv3_y);
  return res;
endfunction

(* always_enabled,
   always_ready,
   synthesize ,
   CLK = "clk",
   RST_N = "reset"
*)
module mkMVarith(MVarith_IFC);

  method Bit#(12) median_x (a,b,c);
    median_x = func_median(a,b,c);
  endmethod : median_x

  method Bit#(12) median_y (a,b,c);
    median_y = func_median(a,b,c);
  endmethod : median_y

  method Bit#(12) shift_left (r_size);
    shift_left = func_shift_left(1,r_size);
  endmethod : shift_left

  method Bit#(12) get_high (r_size);
    get_high = func_shift_left(1,(r_size+5)) - 1;
  endmethod : get_high

  method Bit#(12) get_low (r_size);
    get_low = ~(func_shift_left(1,(r_size+5))) + 1;
  endmethod : get_low

  method Bit#(12) getMVDx (horizontal_mv_data,horizontal_mv_residual,f,r_size);
    getMVDx = func_get_mvd(horizontal_mv_data,horizontal_mv_residual,f,r_size);
  endmethod : getMVDx

  method Bit#(12) getMVDy (vertical_mv_data,vertical_mv_residual,f,r_size);
    getMVDy = func_get_mvd(vertical_mv_data,vertical_mv_residual,f,r_size);
  endmethod : getMVDy

  method Bit#(12) saturate_mvx (mvx,high,low,range);
    saturate_mvx = saturate(mvx,high,low,range);
  endmethod : saturate_mvx

  method Bit#(12) saturate_mvy (mvy,high,low,range);
    saturate_mvy = saturate(mvy,high,low,range);
  endmethod : saturate_mvy

  method  MVtype check_valid (mv1_x,mv1_y,mv2_x,mv2_y,mv3_x,mv3_y);
    check_valid = check_valid_func(mv1_x,mv1_y,mv2_x,mv2_y,mv3_x,mv3_y);
  endmethod : check_valid

endmodule: mkMVarith

endpackage : MVarith
