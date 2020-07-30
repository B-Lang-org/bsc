typedef struct {
   Bool f1;
} MyStruct deriving (Eq, Bits);

function MyStruct mkMyStruct(Bool b);
   return (MyStruct { f1: b });
endfunction

module sysTest();
   Reg#(MyStruct) rg <- mkRegU;

   rule r;
      // forget the argument here
      let res = mkMyStruct;
      res.f1 = True;
      rg <= res;
   endrule
endmodule

