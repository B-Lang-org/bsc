UInt#(32) num_ports = 32; 

(* synthesize *)
module test();

  Reg#(Bool) result <- mkReg(False);
  
  Reg#(UInt#(32)) i <- mkReg(0);

  rule test;
    Bool temp = False;
     for(UInt#(32) j = 0; j < num_ports; j = j + 1)
     begin
	if (i == j && !temp) temp = True;
	$display("Iteration %0d %b", j, temp);
     end
    result <= temp;
  endrule

endmodule
 
