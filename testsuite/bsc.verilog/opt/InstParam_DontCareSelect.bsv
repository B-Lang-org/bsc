typedef struct {
   Bool b;
} MyStruct;

instance Bits#(MyStruct, 96);
   function Bit#(96) pack(MyStruct s);
      Bit#(96) retval = 0;
      UInt#(4) opcode = 0;

      // This order used to fail:
      retval[80] = pack (s.b);
      retval[67:64] = pack (opcode);

      /*
      // This order worked:
      retval[67:64] = pack (opcode);
      retval[80] = pack (s.b);
      */

      return retval;
   endfunction

   function MyStruct unpack(Bit#(96) bs);
      return (MyStruct { b: False });
   endfunction
endinstance

(* synthesize *)
module sysInstParam_DontCareSelect();
   // The parameter value for a submodule instantiation contains a don't-care
   // whose value is chosen in ASyntax, so the final value can only be
   // optimized after that point.  (Worse, if the expression requires
   // declaring defs, in AVeriQuirks, then it will be unrepresentable and
   // BSC will internal error -- for instance, if range selection is not
   // optimized away.)
   //
   Reg#(MyStruct) rg <- mkReg(?);
endmodule
