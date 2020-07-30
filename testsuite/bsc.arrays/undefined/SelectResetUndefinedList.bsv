(* synthesize *)
module sysSelectResetUndefinedList();

  List#(Reset) l = ?;
  
  Reset rst = l[0];

  Reg#(Bool) r <- mkReg(False, reset_by(rst));

endmodule
