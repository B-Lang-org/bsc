// FSMx Encoded states with next_state logic in a function, local var in fnc

export ArithIO_IFC(..);

export mkFSM;
export StateType;


typedef enum {S0, S1, S2, S3} StateType
  deriving (Eq, Bits);
function StateType next_state (StateType curr_state);
  StateType myLocalVar;
  case (curr_state)
    S0 : myLocalVar = S1;
    S1 : myLocalVar = S2;
    S2 : myLocalVar = S3;
    S3 : myLocalVar = S0;
    default : myLocalVar = S0;
  endcase
  return myLocalVar;
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


