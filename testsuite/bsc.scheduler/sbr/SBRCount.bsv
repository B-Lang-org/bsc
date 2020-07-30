interface Count;
  method Bit#(26) readCount;
  method Action incCount;
endinterface

(* synthesize *)
module mkSBRCount(Count);

  Reg#(Bit#(26)) counter <- mkReg(0);
  Wire#(Bit#(26)) counterWire <- mkWire;

  rule driveCounter;
    counterWire <= counter;
    counter <= 0;
  endrule

  method readCount = counter;

  method Action incCount;
     counter <= counterWire + 1;
  endmethod

endmodule
