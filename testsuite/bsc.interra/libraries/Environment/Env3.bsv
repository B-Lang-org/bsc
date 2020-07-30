package Env3;

import List :: *;
import Environment::*;

module mkTestbench_Env3();

  rule fire_once (True);
    $display("genVerilog = %d",genVerilog);
	$finish(2'b00);
  endrule
endmodule: mkTestbench_Env3

endpackage: Env3
