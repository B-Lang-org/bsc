package MkArrayFullFile;

import RegFile::*;
import RegFile::*;

module mkDesign_MkArrayFullFile(RegFile#(Bit#(3),Bit#(8)));
  RegFile#(Bit#(3),Bit#(8)) dut();
  mkRegFileFullLoad#("input_file") the_dut(dut);
  return(dut);
endmodule: mkDesign_MkArrayFullFile 

module mkTestbench_MkArrayFullFile();

  RegFile#(Bit#(3),Bit#(8)) stimulus_io();
  mkRegFileFullLoad#("input_file") the_stimulus_io(stimulus_io);
  Reg#(Bit#(32)) counter <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);


  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule check_result (counter == 24);
	if (fail)
	  $display("Simulation Fails");
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule
  
  rule initial_display (counter < 8);
	 $display("%h %h",counter[2:0],stimulus_io.sub(counter[2:0]));
  endrule
  
  rule update ((counter >= 8) && (counter < 16));
     stimulus_io.upd(counter[2:0],(8'h55 + counter[7:0]));
  endrule

  rule display_value ((counter >= 16) && (counter < 24));
	 $display("%h %h",counter[2:0],stimulus_io.sub(counter[2:0]));
	 if ((stimulus_io.sub(counter[2:0])) != (8'h55 + counter[7:0] - 8))
        fail <= True;
  endrule
 


endmodule: mkTestbench_MkArrayFullFile
                 
endpackage: MkArrayFullFile






