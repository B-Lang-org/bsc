import Vector::*;

typedef union tagged {
   UInt#(17) Extra;
   void T;
   void F;
   } MyBool deriving(Eq,Bits);

typedef 19 Ports;

Integer ports = valueof(Ports);

(* noinline *)
function Bit#(Ports) arbitrate_myunion(Vector#(Ports, MyBool) bs);
   Bit#(Ports) bits = 0;

   MyBool going = T;
   for (Integer i = 0; i < ports; i = i + 1) begin
      if(going == T) begin
	 if (bs[i] == T) begin
	    bits[i] = 1;
	    going = F;
	 end
      end
   end

   return bits;
endfunction

