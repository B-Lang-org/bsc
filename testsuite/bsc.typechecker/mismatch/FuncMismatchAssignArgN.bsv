function Action f(Bool x1, Integer x2, Bool x3);
   $display(x1, x2, x3);
endfunction

interface IFC;
   method Action g(Bool x1, Bool x2, Bool x3);
endinterface

IFC x = interface IFC;
	   method g = f;
	endinterface;


