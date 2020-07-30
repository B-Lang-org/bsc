// Don't import GetPut and Sub doesn't re-export it
import StructSelect_NotImported_Sub::*;

module sysStructSelect_NotImported();
  SubIfc s <- mkSub;

  rule r;
    int x <- s.reqGet.get;
    $display("%h", x);
  endrule
endmodule

