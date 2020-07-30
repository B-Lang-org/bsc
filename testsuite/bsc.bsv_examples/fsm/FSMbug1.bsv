// FSMx Not One-hot encoding with next_state logic in rule
// BUGx Missing () in interface declaration

export ArithIO_IFC(..);

export mkFSM;
export StateType;

import ConfigReg::*;

typedef enum {S0, S1, S2, S3} StateType
  deriving (Eq, Bits);

interface ArithIO_IFC #(type aTyp);
    method aTyp result();
endinterface: ArithIO_IFC

(* synthesize *)
module mkFSM(ArithIO_IFC#(StateType));

//Correct line  
//Reg#(StateType) curr_state();
//Missing ()
  Reg#(StateType) curr_state; 
  mkConfigReg#(S0) the_curr_state(curr_state);

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


