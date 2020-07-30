import LevelFIFO::*;
import Vector::*;

(* synthesize *)
module sysLevelFIFOTest();

  FIFOLevelIfc#(UInt#(16), 7) f <- mkFIFOLevel;

  Vector#(8, Bool) lessThan    = replicate(False);
  Vector#(8, Bool) greaterThan = replicate(False);

  for(Integer i = 0; i < 8; i = i + 1) begin
    lessThan[i] = f.isLessThan(i);
    if (i < 7) greaterThan[i] = f.isGreaterThan(i);
  end

  Reg#(UInt#(16)) count <- mkReg(0);

  Reg#(Bool) do_deq <- mkReg(False);

  rule print_levels;
    $display("Current count: %0d", count);
    $display("Less    than: %0b", lessThan);
    $display("Greater than: %0b", greaterThan); 
  endrule

  rule inc_count;
    $display("Incrementing counter");
    count <= count + 1;
  endrule

  rule enq(!do_deq && (count < 5 || count > 5));
    $display("Enq %0d", count);
    f.enq(count);
  endrule

  rule deq(do_deq);
    $display("Deq %0d", f.first);
    f.deq;
  endrule

  rule clear(count == 5);
    $display("Clear");
    f.clear;
  endrule

  rule start_deq(!f.notFull && !do_deq);
    $display("FIFO full. Start deq...");
    do_deq <= True;
  endrule

  rule exit(!f.notEmpty && do_deq);
    $display("FIFO empty. Exiting...");
    $finish(0);
  endrule
    
endmodule

  
  
  