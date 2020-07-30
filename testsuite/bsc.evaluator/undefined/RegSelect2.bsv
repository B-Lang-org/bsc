import Vector::*;

typedef 512 Size;
Integer size = valueof(Size);

(* synthesize *)
module sysRegSelect2(Empty);
   Vector#(Size, Reg#(Bit#(17))) regs = ?;
   for(Integer i = 0; i < size; i = i + 1)
     regs[i] <- mkReg(0);
   
   Reg#(Bit#(17)) count <- mkReg(0);
   
   rule step(count < fromInteger(size));
      regs[count] <= count;
      count <= count + 1;
   endrule
   
   rule exit(count == fromInteger(size));
      for(Integer i = 0; i < size; i = i + 1)
	 $display("%0d", regs[i]);
      $finish(0);
   endrule
   
endmodule

   
   
