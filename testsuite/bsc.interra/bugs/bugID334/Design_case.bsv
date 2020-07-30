package Design_case;
         
interface Design_case_IFC;  
    method Action start(Bit#(1) load);
    method Bit#(1) case();
endinterface : Design_case_IFC

(*
    always_ready,
    always_enabled,
    CLK = "clk",
    RST_N = "reset"
*)

module mkDesign_case (Design_case_IFC);
    Reg #(Bit#(1)) temp_reg <- mkRegA(0);
  
    method Action start(Bit#(1) load);
        action
         if (load == 1)
           begin
             temp_reg <= 1'b1;
           end
         else
           begin
             temp_reg <= 1'b0;
           end

        endaction
    endmethod: start

    method case();
       case = temp_reg;
    endmethod: case

endmodule: mkDesign_case

endpackage : Design_case
