package ImportForeignModuleBug;

interface Reg #(type a);
    method Action _write(a x1);
    method a _read();
endinterface: Reg

interface VReg #(type n);
    method Action set(Bit#(n) x1);
    method Bit#(n) get();
 endinterface: VReg

import "BVI" MyRegN = module vMkReg#(Integer nn, Bit#(n) v)(VReg#(n));
  default clock clk(CLK);
  method (* reg *)Q_OUT get();
  method set(D_IN) enable(EN);
  schedule get CF get;
  schedule get SB set;
  schedule set SBR set;
endmodule: vMkReg


module mkReg#(a v)(Reg#(a))
   provisos (Bits#(a, sa));
   let _m = liftModule(vMkReg(valueOf(sa), pack(v)));
   VReg#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method _read() ;   return (unpack(_r.get));
   endmethod: _read

   method _write(x) ;   return (_r.set)(pack(x));
   endmethod: _write

endmodule: mkReg

(* synthesize *)
module sysImportForeignModule(Empty);
   Reg#(Bool) x();
   mkReg#(False) the_x(x);

   rule invert;
      x <= !x;
   endrule
endmodule

endpackage: ImportForeignModuleBug

