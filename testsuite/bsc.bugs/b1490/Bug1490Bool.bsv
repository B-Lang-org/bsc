import Vector::*;

typedef 21 Ports;

Integer ports = valueof(Ports);

(* noinline *)
function Bit#(Ports) arbitrate(Vector#(Ports, Bool) bs);
   Bit#(Ports) bits = 0;
   
   // Bit#(1) going = 1;
   Bool going = True;
   for (Integer i = 0; i < ports; i = i + 1) begin
      // if (unpack(going)) begin
      if(going) begin
	 if (bs[i]) begin
	    bits[i] = 1;
	    // going = 0;
	    going = False;
	 end
      end
   end
   
   return bits;
endfunction

