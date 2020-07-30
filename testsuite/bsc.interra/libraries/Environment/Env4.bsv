package Env4;

import List :: *;
import Environment::*;

module mkTestbench_Env4();

  rule fire_once (True);
    $display("compilerversion = %d",compilerVersion);
    $display("date = %s",date);
	$finish(2'b00);
  endrule
endmodule: mkTestbench_Env4

endpackage: Env4
