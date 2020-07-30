////////////////////////////////////////////////////
// FileName : Design_return.bsv
// Author   : Interra
// BugID    : 340
// CommandLine : bsc Design_return.bsv
// Status : NEW for BSC 3.8.6
////////////////////////////////////////////////////

package Design_return;
         
interface Design_IFC;  
    method Action return(Bit#(1) load);
    method Bit#(1) result();
endinterface : Design_IFC

(*
    always_ready,
    always_enabled,
    CLK = "clk",
    RST_N = "reset"
*)

module mkDesign_return (Design_IFC);
    Reg #(Bit#(1)) temp_reg <- mkReg(0);
  
    method Action return(Bit#(1) load);
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
    endmethod: return

    method result();
       result = temp_reg;
    endmethod: result

endmodule: mkDesign_return

endpackage : Design_return
