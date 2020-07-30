/////////////////////////////////////////////////////////////////////////
/* Performs FLC decoding for calculating RMAX and LMAX
*/

package FLCDecode;

interface FLCDecode_IFC;

   method Bit#(6) rmax (
                        Bool last,
			Bit#(12) level,
                        Bool     isIntra);

   method Bit#(12) lmax(
                        Bool last,
			Bit#(6) run,
                        Bool    isIntra);

endinterface: FLCDecode_IFC

function Bit#(6) func_rmax(Bool last,Bit#(12) level,Bool isIntra);
   Bit#(6) res;
   if (isIntra)
      begin
	 if (last == False)
	    begin
	       if (level == 1)
		  res = 14;
	       else if (level == 2)
		  res = 9;
	       else if (level == 3)
		  res = 7;
	       else if (level == 4)
		  res = 3;
	       else if (level == 5)
		  res = 2;
	       else if ((level >= 6) && (level <= 10))
		  res = 1;
	       else
		  res = 0;
	    end
               else
	          begin
		     if (level == 1)
		        res = 20;
		     else if (level == 2)
		        res = 6;
		     else if (level == 3)
		        res = 1;
		     else 
		        res = 0;
		  end
      end
                     else
                        begin
	                   if (last == False)
	                      begin
		                 if (level == 1)
		                    res = 26;
		                 else if (level == 2)
		                    res = 10;
		                 else if (level == 3)
		                    res = 6;
		                 else if (level == 4)
		                    res = 2;
		                 else if ((level == 5) || (level == 6))
		                    res = 1;
	                         else
		                    res = 0;
		              end
                                 else
	                            begin
		                       if (level == 1)
		                          res = 40;
		                       else if (level == 2)
		                          res = 1;
		                       else 
		                          res = 0;
		                    end
	                end
   res = res + 1; // since Type 2 requires adding 1
   return res;
endfunction

function Bit#(12) func_lmax(Bool last,Bit#(6) run,Bool isIntra);
   Bit#(12) res;
   if (isIntra )
      begin
	 if (last == False)
	    begin
	       if (run == 0)
		  res = 27;
	       else if (run == 1)
		  res = 10;
	       else if (run == 2)
		  res = 5;
	       else if (run == 3)
		  res = 4;
	       else if ((run >= 4) && (run <= 7))
		  res = 3;
	       else if ((run == 8) || (run == 9))
		  res = 2;
	       else 
		  res = 1;
	    end
               else
	          begin
		     if (run == 0)
		        res = 8;
		     else if (run == 1)
		        res = 3;
		     else if ((run >= 2) && (run <= 6))
		        res = 2;
		     else 
		        res = 1;
		  end
      end
   else
      begin
	 if (last == False)
	    begin
	       if (run == 0)
		  res = 12;
	       else if (run == 1)
		  res = 6;
	       else if (run == 2)
		  res = 4;
	       else if ((run >= 3) && (run <= 6))
		  res = 3;
	       else if ((run >= 7) && (run <= 10))
		  res = 2;
	       else 
		  res = 1;
	    end
               else
	          begin
		     if (run == 0)
		        res = 3;
		     else if (run == 1)
		        res = 2;
		     else 
		        res = 1;
		  end
      end
   return res;
endfunction

(* synthesize ,
 CLK = "clk",
 RST_N = "reset"
 *)
module mkFLCDecode(FLCDecode_IFC);

   method Bit#(6) rmax (last,level,isIntra);
      rmax = func_rmax(last,level,isIntra);
   endmethod : rmax

   method Bit#(12) lmax (last,run,isIntra);
      lmax = func_lmax(last,run,isIntra);
   endmethod : lmax

endmodule: mkFLCDecode

endpackage : FLCDecode
