typedef union tagged {
   struct {
      Bool first;
      Bool second;
   } OneTwo;
   void Three;
} TaggedUnionStruct;

module mkFoo#(TaggedUnionStruct obj)();
    Reg#(Bool) r();
    mkRegU r_inst(r);
    rule bogus(obj matches tagged OneTwo { first: True, second: .second });
        r <= !r;
    endrule
endmodule
