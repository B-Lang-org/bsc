typedef union tagged {
  struct { Bit#(5) rd; Bit#(5) ra; Bit#(5) rb; } Add;
  struct { Bit#(5) cd; Bit#(5) addr; } Jz;
  struct { Bit#(5) rd; Bit#(10) v; } LoadC;
} Instr deriving(Bits);


module mkPrimConcatThree (Empty);
   Reg#(Instr) r();
   mkRegU the_r(r);

   rule r1 (True);
      // These two only concatenate two items:
      //   r <= LoadC {rd:1, v:5};
      //   r <= Add {rd:1, ra:10, rb:10};
      // This results in PrimConcat of three items:
      r <= Jz { cd:1, addr:10 };
   endrule
endmodule
