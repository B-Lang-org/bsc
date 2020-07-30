package Env;

import List :: *;
import Environment::*;

module mkTestbench_Env();

  rule fire_once (True);
    $display("testAssert = %d",testAssert);
	$finish(2'b00);
  endrule
endmodule: mkTestbench_Env

endpackage: Env
