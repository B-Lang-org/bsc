import Vector::*;

typedef enum { A, B, C } MyEnum deriving(Eq,Bits);

typedef 21 Ports;

Integer ports = valueof(Ports);

(* noinline *)
function Bit#(Ports) arbitrate_myenum(Vector#(Ports, MyEnum) bs);
   Bit#(Ports) bits = 0;
   
   MyEnum going = A;
   // find the first two elements marked "B" in bs
   for (Integer i = 0; i < ports; i = i + 1) begin
      if(going != C) begin
	 if (bs[i] == B) begin
	    bits[i] = 1;
	    if (going == A) 
	       going = B;
	    else if (going == B)
	       going =  C;
	 end
      end
   end
   
   return bits;
endfunction

