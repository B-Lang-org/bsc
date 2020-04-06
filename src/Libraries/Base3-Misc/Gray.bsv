////////////////////////////////////////////////////////////////////////////////
//  Filename      : Gray.bsv
//  Author        : Todd Snyder
//  Description   : Gray coded package
////////////////////////////////////////////////////////////////////////////////
package Gray;

// Notes :

////////////////////////////////////////////////////////////////////////////////
/// Types
////////////////////////////////////////////////////////////////////////////////
typedef struct {
		Bit#(n) code;
		} Gray#(numeric type n) deriving (Bits, Eq);


// Instance of Literal allows conversion from Integers to Grey
instance Literal #( Gray#(n) )
   provisos(Add#(1, msb, n));
   function Gray#(n) fromInteger (Integer i);
      return grayEncode ( fromInteger (i));
   endfunction
   function Bool inLiteralRange (Gray#(n) g, Integer i);
      // Range is the same as Bit#(n),   yes -1 is included
      return inLiteralRange ( Bit#(n) ' (0), i);
   endfunction
endinstance

instance Bounded # ( Gray#(n) )
   provisos(Add#(1, msb, n));
   function Gray#(n) minBound ;
      return grayEncode ( Bit#(n) ' (minBound) );
   endfunction
   function Gray#(n) maxBound ;
      return grayEncode ( Bit#(n) ' (maxBound) );
   endfunction
endinstance


////////////////////////////////////////////////////////////////////////////////
/// Functions
////////////////////////////////////////////////////////////////////////////////
function Gray#(n) grayEncode(Bit#(n) value) provisos(Add#(1, msb, n));
   Bit#(n) gcode  = ?;
   Bit#(n) bcode  = value;
   Integer idxmsb = valueof(msb);

   gcode[idxmsb]  = bcode[idxmsb];
   for(Integer i = idxmsb-1; i >= 0; i = i - 1)
      gcode[i] = bcode[i+1] ^ bcode[i];

   return unpack(gcode);
endfunction

function Bit#(n) grayDecode(Gray#(n) value) provisos(Add#(1, msb, n));
   Bit#(n) bcode  = ?;
   Bit#(n) gcode  = pack(value);
   Integer idxmsb = valueof(msb);

   bcode[idxmsb]  = gcode[idxmsb];
   for(Integer i = idxmsb-1; i >= 0; i = i - 1)
      bcode[i] = bcode[i+1] ^ gcode[i];

   return bcode;
endfunction

function Gray#(n) grayIncrDecr(Bool decrement, Gray#(n) value) provisos(Add#(1, msb, n));
   Bit#(n) gcode  = pack(value);
   Bool    p      = unpack(parity(gcode));
   Integer switch = ?;
   Integer last1  = valueof(n);
   Integer idxmsb = valueof(msb);

   for(Integer i = idxmsb; i >= 0; i = i - 1) begin
      if (gcode[i] == 1) begin
	 last1 = i;
      end
   end

   if (p == decrement)
      switch = 0;
   else if (last1 < idxmsb)
      switch = last1 + 1;
   else
      switch = idxmsb;

   gcode[switch] = ~gcode[switch];

   return unpack(gcode);
endfunction

function Gray#(n) grayIncr(Gray#(n) value) provisos(Add#(1, msb, n));
   return grayIncrDecr(False, value);
endfunction

function Gray#(n) grayDecr(Gray#(n) value) provisos(Add#(1, msb, n));
   return grayIncrDecr(True, value);
endfunction

endpackage: Gray
