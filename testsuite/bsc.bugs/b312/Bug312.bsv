typedef enum {Ang0,Ang45,Ang135,Ang90,Ang315,Ang270,Ang180,Ang225} AngStates
                 deriving(Eq,Bits);

function  AngStates fsmBehavior(AngStates currentState,  Bit#(1) movecw,
 Bit#(1) moveccw);
 AngStates nxtState;

 if(currentState==Ang0)
 begin
    if (movecw ==1)
         nxtState = Ang45;
    else if (moveccw ==1)
         nxtState = Ang315;
    else
         nxtState = Ang0;
 end
 else if(currentState == Ang45)
 begin
    if (movecw  == 1)
         nxtState = Ang90;
    else if (moveccw  ==1)
         nxtState = Ang0;
    else
         nxtState = Ang45;
 end
 else if (currentState==Ang90)
 begin
    if(movecw  == 1) 
         nxtState = Ang135;
    else if (moveccw  == 1)
         nxtState = Ang45;
    else
         nxtState = Ang90; 
 end
 else if(currentState == Ang135)
 begin
    if(movecw  == 1) 
         nxtState = Ang180;
    else if (moveccw  == 1)
         nxtState = Ang90;
    else 
         nxtState = Ang135; 
 end
 else if(currentState == Ang180)
 begin
    if(movecw  == 1) 
          nxtState = Ang225;
    else if (moveccw  == 1)
          nxtState = Ang135;
    else 
          nxtState = Ang180; 
 end
 else if(currentState == Ang225)
 begin
    if(movecw  == 1) 
          nxtState = Ang270;
    else if (moveccw  == 1)
          nxtState = Ang180;
    else 
          nxtState = Ang225; 
 end
 else if (currentState == Ang270)
 begin
    if(movecw  == 1) 
          nxtState = Ang315;
    else if (moveccw  == 1)
          nxtState = Ang225;
    else
          nxtState = Ang270;
 end
 else // if(currentState == Ang315)
 begin
    if(movecw  == 1) 
          nxtState = Ang0;
    else if (moveccw  == 1)
          nxtState = Ang270;
    else 
          nxtState = Ang315;
 end
    
 return nxtState;
endfunction: fsmBehavior
         
interface Design_IFC;  
    method AngStates newpostn ();
endinterface : Design_IFC

(*
    always_ready,
    always_enabled,
    CLK = "clk",
    RST_N = "reset"
*)

module sysBug312  #(parameter Bit#(1) movecw, Bit#(1) moveccw,AngStates postn) (Design_IFC);
    Reg #(AngStates) currentState <- mkReg (postn);
    Reg #(AngStates) nextState <- mkRegU;

    rule fsm; 
      nextState <= fsmBehavior(currentState,movecw,moveccw);
    endrule: fsm

    rule start;
             currentState <= nextState;
    endrule: start

    method newpostn ();
      newpostn = currentState;
    endmethod: newpostn
endmodule: sysBug312
