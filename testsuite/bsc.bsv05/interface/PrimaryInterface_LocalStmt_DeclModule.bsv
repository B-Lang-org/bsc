
interface Ifc;
    method Module#(Reg#(Bool)) m();
endinterface

function Ifc mkFn();
  return (
     interface Ifc;
        module [Module] mkM(Reg#(Bool));
            let _i <- mkRegU;
            return _i;
        endmodule

        method m = mkM;
     endinterface
   );
endfunction

