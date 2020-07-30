
typedef struct {
   Bit#(66) addr;
   Bit#(6)  size;
} S deriving (Bits); 

interface SubIfc;
   method S get();
endinterface: SubIfc


interface TopIfc;
   (* prefix = "" *) // required
   interface SubIfc sub_ifc;
endinterface: TopIfc

(* synthesize *)
module mkBug(TopIfc);

   SubIfc sub <- mkSub();
   
   interface SubIfc sub_ifc = sub;
      
endmodule: mkBug

module mkSub(SubIfc);
   
   Reg#(Bit#(66)) x <- mkReg(0);
      
   method S get();
      return S { addr: x, size: '1};
   endmethod: get

endmodule: mkSub



