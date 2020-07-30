import Vector::*;

typedef 10 Size;

Integer size = valueof(Size);

(* synthesize *)
module sysTwoDUpdateTest(Empty);
   Reg#(Vector#(Size, Vector#(Size, Bool))) rvv <- 
   mkReg(replicate(replicate(False)));
   
   Vector#(Size, Reg#(Vector#(Size, Bool))) vrv <- 
      replicateM(mkReg(replicate(False)));
   
   Vector#(Size, Vector#(Size, Reg#(Bool))) vvr <- 
      replicateM(replicateM(mkReg(False)));
   
   Reg#(UInt#(32)) i <- mkReg(0);
   Reg#(UInt#(32)) j <- mkReg(0);
   
   rule count;
      if (i < fromInteger(size))
	 i <= i + 1;
      else if (j < fromInteger(size)) begin
	 i <= 0;
	 j <= j + 1;
      end
      else begin
	 $display("Test complete");
	 $finish(0);
      end
      
   endrule
   
   rule update;
      rvv[i][j] <= True;
      vrv[i][j] <= True;
      vvr[i][j] <= True;
   endrule
   
   rule check;
      
      Bool pass = True;

      if (i < fromInteger(size) &&
          j < fromInteger(size))
        pass = rvv[i][j] == vrv[i][j] &&
	       vrv[i][j] == vvr[i][j] &&
               !vvr[i][j];

      if(i > 0 && j < fromInteger(size))
	 pass = pass && rvv[i-1][j] &&
	        vrv[i-1][j] && vvr[i-1][j];
      
      if(j > 0 && i < fromInteger(size))
         pass = pass && rvv[i][j-1] &&
                vrv[i][j-1] && vvr[i][j-1];
  
      if(pass)
	 $display("Pass %0d %0d", i, j);
      else
         $display("Fail %0d %0d", i, j);   
   endrule
   
endmodule
