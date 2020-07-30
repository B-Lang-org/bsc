// FSMx Encoded states with next state logic inside the rule

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

   (* fire_when_enabled *)
  rule rule1_StateChange (True); 
        StateType next_state;
	  case (curr_state)
	    S0 : next_state = S1;
	    S1 : next_state = S2;
	    S2 : next_state = S3;
	    S3 : next_state = S0;
            default : next_state = S0;
	  endcase
          curr_state <= next_state;
  endrule: rule1_StateChange

  method result(); 
    return (curr_state);
  endmethod: result
endmodule: mkFSM


