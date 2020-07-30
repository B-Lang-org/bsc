
import DefaultValue :: *;
import FShow :: *;
import FixedPoint :: *;
import Vector :: * ;
import StmtFSM ::*;

typedef struct {
                UInt#(8) f1 ;
                UInt#(8) f2 ;
                UInt#(8) f3 ;
                UInt#(8) f4 ;                
                } MyStruct 
deriving (Bits );

instance DefaultValue #(MyStruct);
   defaultValue = MyStruct {
      f1:1, f2:5, f3:10, f4:64
      };
endinstance

instance FShow#(MyStruct);
   function Fmt fshow(MyStruct v);
      return $format("MyStruct(", fshow(v.f1), fshow(v.f2), fshow(v.f3), fshow(v.f4), ")");
   endfunction
endinstance

(*synthesize*)
module sysDefaultValueTest ();
   
   
   Reg#(Bool) rb <- mkReg(defaultValue);
   Reg#(Maybe#(Bool)) rmb <- mkReg(defaultValue);
   Reg#(UInt#(5))    rui5 <- mkReg(defaultValue);
   Reg#(Int#(4))     ri4 <- mkReg(defaultValue);
   Reg#(Bit#(2))     rb2 <- mkReg(defaultValue);
   //Reg#(void) rv <- mkReg(defaultValue);
   Reg#(Tuple2#(Bool, FixedPoint#(5,4))) rt2 <- mkReg(defaultValue);
   Reg#(Tuple3#(Bool,Maybe#(Bool), Int#(5))) rt3 <- mkReg(defaultValue);
   Reg#(MyStruct)    rs <- mkReg(defaultValue);
   Reg#(Vector#(10,MyStruct)) vrs <- mkReg(defaultValue);
        
   let ts = (seq
                $display( fshow(rb) );
                $display( fshow(rmb) );
                $display( fshow(rui5) );
                $display( fshow(ri4) );
                $display( fshow(rb2) );
                $display( fshow(rt2) );
                $display( fshow(rt3) );
                $display( fshow(rs) );
                $display( fshow(vrs) );
                noAction;
             endseq);
   mkAutoFSM( ts);
   
endmodule
