// FSMx Encoded states with next_state logic in a function, no local var in fnc

export ArithIO_IFC(..);

export mkFSM;
export StateType;

typedef enum {S0, S1, S2, S3} StateType
  deriving (Eq, Bits);
function StateType next_state (StateType curr_state);
  case (curr_state)
    S0 : next_state = S1;
    S1 : next_state = S2;
    S2 : next_state = S3;
    S3 : next_state = S0;
    default : next_state = S0;
  endcase
endfunction

interface ArithIO_IFC #(type aTyp);
    method aTyp result();
endinterface: ArithIO_IFC

(* synthesize *)
module mkFSM(ArithIO_IFC#(StateType));
  Reg#(StateType) curr_state();
  mkReg#(S0) the_curr_state(curr_state);

  rule rule1_StateChange (True);
         curr_state <= next_state(curr_state);
  endrule: rule1_StateChange

  method result(); 
    return (curr_state);
  endmethod: result
endmodule: mkFSM


