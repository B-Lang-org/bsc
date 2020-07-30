typedef enum {Ang0,Ang45,Ang135,Ang90,Ang315,Ang270,Ang180,Ang225} AngStates
                 deriving(Eq,Bits);

         
interface Design_IFC;  
    method AngStates newpostn ();
    method Action start(AngStates postn,Bit#(1) movecw,Bit#(1) moveccw);
endinterface : Design_IFC

(*
    always_ready,
    always_enabled,
    CLK = "clk",
    RST_N = "reset"
*)

module mkDesign (Design_IFC);
    Reg #(AngStates) currentState <- mkRegA (Ang0);
    Reg #(AngStates) nextState <- mkRegU;

  
    method Action start(AngStates postn,Bit#(1) movecw,Bit#(1) moveccw);
        action
           if(currentState==Ang0)
           begin
              if (movecw ==1)
                 currentState <= Ang45;
              else if (moveccw ==1)
                 currentState <= Ang315;
              else
                 currentState <= Ang0;
           end
           else if(currentState == Ang45)
           begin
              if (movecw  == 1)
                 currentState <= Ang90;
              else if (moveccw  ==1)
                 currentState <= Ang0;
              else
                 currentState <= Ang45;
           end
           else if (currentState==Ang90)
           begin
              if(movecw  == 1) 
                currentState <= Ang135;
              else if (moveccw  == 1)
                currentState <= Ang45;
              else
                currentState <= Ang90; 
           end
           else if(currentState == Ang135)
           begin
              if(movecw  == 1) 
                 currentState <= Ang180;
              else if (moveccw  == 1)
                 currentState <= Ang90;
              else 
                 currentState <= Ang135; 
           end
           else if(currentState == Ang180)
           begin
              if(movecw  == 1) 
                 currentState <= Ang225;
              else if (moveccw  == 1)
                 currentState <= Ang135;
              else 
                 currentState <= Ang180; 
          end
          else if(currentState == Ang225)
          begin
              if(movecw  == 1) 
                  currentState <= Ang270;
              else if (moveccw  == 1)
                  currentState <= Ang180;
              else 
                  currentState <= Ang225; 
         end
         else if (currentState == Ang270)
         begin
            if(movecw  == 1) 
               currentState <= Ang315;
            else if (moveccw  == 1)
               currentState <= Ang225;
            else
                currentState <= Ang270;
         end
         else if(currentState == Ang315)
         begin
            if(movecw  == 1) 
                currentState <= Ang0;
            else if (moveccw  == 1)
                currentState <= Ang270;
            else 
                currentState <= Ang315;
        end
        endaction
    endmethod: start

    method newpostn ();
      newpostn = currentState;
    endmethod: newpostn
endmodule: mkDesign
        

