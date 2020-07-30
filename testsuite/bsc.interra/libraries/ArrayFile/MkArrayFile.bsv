package MkArrayFile;

import RegFile::*;
import RegFile::*;

module mkDesign_MkArrayFile(RegFile#(Bit#(4),Bit#(8)));
  RegFile#(Bit#(4),Bit#(8)) dut();
  mkRegFileLoad#("input_file",0,7) the_dut(dut);
  return(dut);
endmodule: mkDesign_MkArrayFile 


module mkTestbench_MkArrayFile();

  RegFile#(Bit#(4),Bit#(8)) stimulus_io();
  mkRegFileLoad#("input_file",0,7) the_stimulus_io(stimulus_io);
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
	 $display("%h %h",{1'b0,counter[2:0]},stimulus_io.sub({1'b0,counter[2:0]}));
  endrule
  
  rule update ((counter >= 8) && (counter < 16));
     stimulus_io.upd({1'b0,counter[2:0]},(8'h55 + counter[7:0]));
  endrule

  rule display_value ((counter >= 16) && (counter < 24));
	 $display("%h %h",{1'b0,counter[2:0]},stimulus_io.sub({1'b0,counter[2:0]}));
	 if ((stimulus_io.sub({1'b0,counter[2:0]})) != (8'h55 + counter[7:0] - 8))
        fail <= True;
  endrule
 


endmodule: mkTestbench_MkArrayFile
                 
endpackage: MkArrayFile






