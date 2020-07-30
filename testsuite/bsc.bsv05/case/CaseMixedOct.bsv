function String showBool(Bool b);
  return(b ? "True" : "False");
endfunction

function Bool matchOct(Bit#(15) b);
  case (b) matches
    15'o111??:return(True);
    15'o2?2?2:return(True);
    15'o?333?:return(True);
    15'o?4?4?:return(True);
    15'o55555:return(True);
    default: return (False);
  endcase
endfunction

Bit#(15) tests[20] = { 0,
    	 	       15'o11111,
		       15'o01111,
		       15'o11100,
   		       15'o21111,	       
   		       15'o22222,
		       15'o22022,
    		       15'o20202,
    		       15'o21211,
    		       15'o33333,
    		       15'o34333,
    		       15'o03330,
    		       15'o03340,
    		       15'o44444,
    		       15'o45444,
    		       15'o04040,
    		       15'o04050,
    		       15'o55555,
    		       15'o55550,
    		       15'o05555 };

(* synthesize *)
module sysCaseMixedOct();

  Reg#(UInt#(9)) r <- mkReg(0);
  Reg#(Bit#(15)) b <- mkReg(23405); // init to 15'o55555

  rule test;
    $display(showBool(matchOct(b)));
    b <= tests[r];
    if(r == 20) $finish(0);
    r <= r + 1;
  endrule

endmodule

  