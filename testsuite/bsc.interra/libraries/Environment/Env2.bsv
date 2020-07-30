package Env2;

import List :: *;
import Environment::*;

module mkTestbench_Env2();

  rule fire_once (True);
    $display("GenC = %d",genC);
	$finish(2'b00);
  endrule
endmodule: mkTestbench_Env2

endpackage: Env2
