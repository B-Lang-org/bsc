package Design;
import List:: *;

function Bit #(1) calparity (Bit#(n) theInput);
   function Bit #(1) f (Integer j, Bit #(1) c);
      Bit #(1) temp;
      if (theInput[fromInteger (j):fromInteger (j)] == 0)
        temp = c ^ 1'b0;
      else 
        temp = c ^ 1'b1;
      f = temp;
   endfunction: f
      calparity = foldr (f, 0, (upto (0, valueOf (n) - 1))) ;
endfunction: calparity


interface Design_IFC;
  method Bit #(1) parity (Bit #(8) in_data);
endinterface : Design_IFC

(*
    always_enabled,
    always_ready,
    CLK = "clk",
    RST_N = "reset"
*)
module mkDesign (Design_IFC);
   method parity (in_data);
      parity = calparity (in_data);
   endmethod : parity
endmodule : mkDesign

endpackage : Design
