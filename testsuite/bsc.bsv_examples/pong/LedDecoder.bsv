typedef Bit#(7) LedDisplay;
typedef Bit#(4) LedDigit;

interface LedDecoder;
    method LedDisplay decode (LedDigit x1);
endinterface: LedDecoder

module mkLedDecoder (LedDecoder);
        method decode(x);
          LedDisplay d;
	  case (x)
	    4'h0 :  d = 7'b1110111;
	    4'h1 :  d = 7'b0010010;
	    4'h2 :  d = 7'b1011101;
	    4'h3 :  d = 7'b1011011;
	    4'h4 :  d = 7'b0111010;
	    4'h5 :  d = 7'b1101011;
	    4'h6 :  d = 7'b1101111;
	    4'h7 :  d = 7'b1010010;
	    4'h8 :  d = 7'b1111111;
	    4'h9 :  d = 7'b1111011;
	    4'hA :  d = 7'b1111110;	
	    4'hB :  d = 7'b0101111;
	    4'hC :  d = 7'b0001101;
	    4'hD :  d = 7'b0011111;
	    4'hE :  d = 7'b1101101;
	    4'hF :  d = 7'b1101100;
            default : d = 7'b0000000; //should not need this default
	  endcase
          return d;
       endmethod: decode
endmodule
