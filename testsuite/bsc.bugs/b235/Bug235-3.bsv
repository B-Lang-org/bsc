typedef enum { STOP , SLOW , MEDIUM , FAST} ActualSpeed
             deriving (Eq,Bits);

interface Design_IFC #(parameter type a,parameter type b);
    method Action start(a brake,a accelerate);
    method b speed();
endinterface:  Design_IFC

(* always_enabled, always_ready *)
module mkDesign(Design_IFC #(Bit#(1),ActualSpeed));
    Reg#(ActualSpeed) actualSpeed();
    mkReg#(STOP) the_actualSpeed(actualSpeed);

    method Action start(Bit#(1) brake,Bit#(1) accelerate);
        action
            if(accelerate == 1)  
            begin
                case (actualSpeed) 
                        STOP   : actualSpeed <= SLOW;
                        SLOW   : actualSpeed <= MEDIUM;
                        MEDIUM : actualSpeed <= FAST;
                        FAST   : actualSpeed <= FAST;
                endcase
            end
            else if(brake == 1)
            begin
                case (actualSpeed)
                        STOP   : actualSpeed <= STOP;
                        SLOW   : actualSpeed <= STOP;
                        MEDIUM : actualSpeed <= SLOW;
                        FAST   : actualSpeed <= MEDIUM;
                endcase
            end
            else
            begin
                actualSpeed <= actualSpeed;
            end
        endaction
    endmethod: start

    method ActualSpeed speed();
       speed = actualSpeed;
    endmethod: speed   

endmodule: mkDesign 

