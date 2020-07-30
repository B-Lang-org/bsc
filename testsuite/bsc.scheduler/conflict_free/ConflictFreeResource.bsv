import RegFile::*;

// we have enough resource, but we allocate it poorly
// because of the conflict_free attribute
(* synthesize *)
module sysConflictFreeResource();

  RegFile#(Bit#(3), Bit#(4)) rf <- mkRegFileFull;

  Reg#(Bool) init <- mkReg(False);
  Reg#(Bit#(3)) init_count <- mkReg(0);

  rule do_init(!init);
    rf.upd(init_count, 15 - zeroExtend(init_count));
    init_count <= init_count + 1;
    if(init_count == 7) init <= True;
  endrule

  (* conflict_free = "read_f_e_d, read_c_b" *)
  rule read_f_e_d(init);
    for(Bit#(3) i = 0; i < 3; i = i + 1)
    begin
      $display("rf[%0d]: %h", i, rf.sub(i));
    end
  endrule

  rule read_c_b(init);
    for(Bit#(3) i = 3; i < 5; i = i + 1)
    begin
      $display("rf[%0d]: %h", i, rf.sub(i));
    end
  endrule

  rule exit(init);
    init <= False; // scheduling cheat
    $finish(0);
  endrule

endmodule


  