// FSMx One-hot encoding with next_state logic in rule

export ArithIO_IFC(..);

export mkFSM;
export StateType;

typedef enum {S0, S1, S2, S3} StateType
  deriving (Eq, Bits);

interface ArithIO_IFC #(type aTyp);
    method aTyp result();
endinterface: ArithIO_IFC

(* synthesize *)
module mkFSM(ArithIO_IFC#(StateType));

  Reg#(StateType) curr_state();
  mkReg#(S0) the_curr_state(curr_state);

   rule state_S0 (curr_state == S0);
      curr_state <= S1;
   endrule
   
   rule state_S1 (curr_state == S1);
      curr_state <= S2;
   endrule
  
   rule state_S2 (curr_state == S2); 
      curr_state <= S3;
   endrule

         (* fire_when_enabled *)
   rule state_S3 (curr_state == S3);
      curr_state <= S0;
   endrule

  method result(); 
    return (curr_state);
  endmethod: result
endmodule: mkFSM


