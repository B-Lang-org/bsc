////////////////////////////////////////////////////
// FileName : IfElseIf.bsv
// Author   : Interra
// BugID    : 238
// CommandLine : bsc IfElseIf.bsv
// Status : Fixed
//////////////////////////////////////////////////// 
package IfElseIf;


module mkDesign();

  Reg#(Bool) x <- mkReg(True) ;
  rule always_true (True);
    if (True) 
	  x <= False;
  endrule

endmodule: mkDesign
endpackage: IfElseIf
