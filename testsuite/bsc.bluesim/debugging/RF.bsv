import RegFile::*;

module mkRF();

  RegFile#(UInt#(5),UInt#(72)) rf <- mkRegFileFull;
  Reg#(UInt#(5)) addr <- mkReg(0);
  Reg#(UInt#(72)) data <- mkReg('haaaaaaaaaaaaaaaaaa);
  Reg#(UInt#(4)) counter <- mkReg(0);

  rule count;
    counter <= counter + 1;
  endrule: count

  (* descending_urgency = "update2, update" *)

  rule update (counter < 15);    
    rf.upd(addr,data);   
    addr <= addr + 1;
    data <= 7*data + zeroExtend(addr);
  endrule: update

  rule update2 (counter == 8);
    rf.upd(addr,data);
    addr <= addr - 1;
    data <= 3*data;
  endrule: update2

  rule tick;
    $display($time);
  endrule: tick

  rule done (counter == 15);
    $finish(0);
  endrule: done

endmodule
