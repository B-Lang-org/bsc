typedef enum {ZERO, ONE, TWO, THREE} STATES
          deriving (Eq,Bits);  

interface Four_IFC;
    method (STATES) state(); 
      
endinterface: Four_IFC

(*
       always_ready,
       always_enabled,
 synthesize 
*)

module mkFour (Four_IFC);

  Reg#(STATES)    reg_state();
  mkRegA#(ZERO)      ireg_state(reg_state);

  rule zeroRule (reg_state == ZERO);
    begin
         reg_state  <= ONE;
    end
  endrule

  rule oneRule (reg_state == ONE);
    begin
         reg_state  <= TWO;
    end 
  endrule

  rule twoRule (reg_state == TWO);
    begin
         reg_state  <= THREE;
    end
  endrule

  rule threeRule (reg_state == THREE);
    begin
         reg_state  <= ZERO;
    end
  endrule

 method state(); 
    state = reg_state; 
 endmethod


endmodule: mkFour

