import Vector::*;
import RegFile::*;

Vector#(4, String) filenames = 
cons ("file1", cons ("file10", cons ("file11", cons ("file100", nil))));

(* synthesize *) 
module mkRegFileTest#(parameter UInt#(2) offset)();
   
   Vector#(4, RegFile#(Bit#(16), Bit#(32))) rfs = ?;
   for(Integer i = 0; i < 2; i = i + 1)
      rfs[i] <- mkRegFileFullLoad(filenames[fromInteger(i)+offset]+".hex");
   
endmodule

(* synthesize *)
module sysBug1489();
   
   mkRegFileTest(2);

   rule test;
     $finish(0);
   endrule
   
endmodule
