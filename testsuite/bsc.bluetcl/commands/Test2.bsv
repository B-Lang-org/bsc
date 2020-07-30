import Test :: *;
import Vector :: * ;

// Some funky hierarchy testing with Vectors and such

(* synthesize *)
module mkTest #(Inout#(Bar) i) ();
   Vector#(4,Reg#(int)) x = ? ;
   Vector#(4,Reg#(int)) y <- replicateM(mkRegU);

   Vector#(4,Reg#(int)) aa = ? ;
   Vector#(4,Reg#(int)) bb = ? ;
   
   Vector#(5,Reg#(int)) zw <- mapM (mkReg, genWith (fromInteger));
   
   
   Vector#(2,Foo#(Bar)) xx <- zipWithM( mkBVI, genWith(fromInteger), replicate(i));
   
   for (Integer i = 0 ; i < 4 ; i = i + 1) begin
      x[i] <- mkRegU; 
   end

   for (Integer i = 0 ; i < 4 ; i = i + 1) begin
     aa[i] <- mkRegU; 
     bb[i] <- mkRegU; 
   end
   
   
   Vector#(2,Sub_Ifc) subis <- mapM( mkSub, genWith(fromInteger) );
   
endmodule

interface Sub_Ifc;
   (*always_ready*)
   method Action foo(int x);
   (*ready="RadyOnTheReadMethod"*)  method int bar ;
endinterface

(* synthesize *)
module mkSub( Bit#(3) ax, Sub_Ifc ifc );
   Reg#(int) foo2 <- mkReg(0);
   Reg#(Bit#(3)) barx <- mkReg(3);
   method Action foo (int xx);
      foo2 <= xx;
   endmethod
   method int bar ;
      return unpack(extend(barx)) + foo2;
   endmethod
endmodule
