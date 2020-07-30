package Design_def;

typedef enum  {Idle , First_F6 , Second_F6 , Third_F6 , First_28 , Second_28, Detected} Datastates 
    deriving (Eq,Bits);

interface Design_IFC;
   method Action data_in (Bit#(8) in_data); 
   method Bool sof();
endinterface: Design_IFC
          
(*
       always_ready ,
 always_enabled ,
 synthesize
*)

module mkDesign_def (Design_IFC);
 Reg#(Datastates) state();
 mkRegA#(Idle)      t_state(state);

    method data_in(in_data);
        action  
           case (state)
              Idle: begin
                if (in_data == 8'hF6)
                    state <= First_F6;
                else
                    state <= Idle;
              end
              First_F6: begin
                if (in_data == 8'hF6) 
                    state <= Second_F6;
                else 
                    state <= Idle;
              end
              Second_F6: begin 
                if (in_data == 8'hF6) 
                    state <= Third_F6;
                else 
                    state <= Idle;
              end
              Third_F6: begin
                if (in_data == 8'hf6)
                    state <= Third_F6;
                else if (in_data == 8'h28) 
                    state <= First_28;
                else 
                    state <= Idle;
              end
              First_28: begin 
                if (in_data == 8'hF6) 
                    state <= First_F6;
                else if (in_data == 8'h28) 
                    state <= Second_28;
                else 
                    state <= Idle;
              end
              Second_28: begin 
                if (in_data == 8'hF6) 
                    state <= First_F6;
                else if (in_data == 8'h28) 
                    state <= Detected;
                else 
                    state <= Idle ;
              end
              Detected: begin
                if(in_data == 8'hf6)
                    state <= First_F6;
                else
                    state <= Idle;
                        end
              // Catch error condition
              default:
              state <= Idle ;
           endcase
        endaction  
    endmethod: data_in

    method sof();
       sof = (state == Detected);
    endmethod: sof

endmodule: mkDesign_def
endpackage: Design_def
