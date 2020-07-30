typedef Bit#(16) Tin;
typedef Bit#(32) Tout;

// Wire set in a Rule and Read in a Method using Multiplier Example
interface Mult_IFC;
    method Action  start (Tin m1, Tin m2);
    method Tout    result();
endinterface

(* synthesize *)
module mkDesign( Mult_IFC );

// Multiplier * Multiplicand = Product
   Reg#(Tout)    product   <- mkReg(?);
   Reg#(Tout)    mcand     <- mkReg(?);
   Reg#(Tin)     mplr      <- mkReg(0);
   RWire#(Tin)   mplr_wire <- mkRWire;

   rule cycle ( validValue(mplr_wire.wget) != 0 ); // check mplr_wire is not zero
      if (mplr[0] == 1) product <= product + mcand;
      mcand   <= mcand << 1; // left shift multiplicand
      mplr    <= mplr  >> 1; // right shit multiplier
   endrule

// Set Multiplier value into Wire
   rule always_fire;
	  mplr_wire.wset(mplr);
   endrule

// Wire read in method after checking mplr_wire is zero
   method Action start(Tin m1, Tin m2) if ((validValue(mplr_wire.wget) == 0));
       product <= 0;
       mcand   <= {0, m1};
       mplr    <= m2;
   endmethod
   
// Return product after checking mplr_wire is zero
   method Tout result() if (validValue(mplr_wire.wget) == 0);
      return product;
   endmethod
   
endmodule
