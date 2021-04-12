import Vector::*;
import FIFO::*;

// DeMarshaller

// A de-marshaller takes n input "chunks" and produces one larger value.

interface DeMarshaller#(parameter type in_T, parameter type out_T);

   // Enq a chunk
   method Action enq(in_T chunk);
   // Look at the whole completed value.
   method out_T  first();
   // Deq the whole completed value.
   method Action deq();

endinterface

module mkDeMarshaller
   // interface:
       (DeMarshaller#(in_T, out_T))
   provisos
       (Bits#(in_T, in_SZ),
        Bits#(out_T, out_SZ),
        Div#(out_SZ, in_SZ, k__));

   Integer maxIdx = valueof(k__) - 1;

   // The output we build up as we go along.
   Vector#(k__, Reg#(Maybe#(Bit#(in_SZ)))) chunks = newVector();

   for (Integer x = maxIdx; x >= 0; x = x - 1)
   begin
     chunks[x] <- mkReg(Invalid);
   end

   // We are ready to dequeue when all chunks have been filled.
   // IE: when index overflow occurs.
   Bool ready = isValid(chunks[0]);


   // enq

   // Add the chunk to the current place in the vector.

   method Action enq(in_T chunk) if (!ready);

     chunks[maxIdx] <= tagged Valid pack(chunk);

     // Do the shift with a for loop
     for (Integer x = maxIdx; x > 1; x = x - 1)
     begin
       chunks[x-1] <= chunks[x];
     end

   endmethod

   // first

   // Return the entire vector.

   method out_T first() if (ready);

     Bit#(out_SZ) final_val = 0;

     // Do the shift with a for loop
     for (Integer x = 0; x < valueof(out_SZ); x = x + 1)
     begin

        Integer j = x / valueof(in_SZ);
        Integer k = x % valueof(in_SZ);
        final_val[x] = validValue(chunks[j])[k];

     end

     return unpack(final_val);

   endmethod

   // deq

   // Reset the index to 0 so we start over.

   method Action deq() if (ready);

     for (Integer x = 0; x < maxIdx; x = x + 1)
     begin
       chunks[x] <= Invalid;
     end

   endmethod

endmodule

(* synthesize *)
module sysTest1 (DeMarshaller#(Bit#(8), Bit#(32)));

 let m <- mkDeMarshaller();

 return m;

endmodule
