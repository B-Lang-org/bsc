import FIFO :: *;

interface Buggy;
    method Bit #(8) result();
endinterface

(* synthesize *)
module mkBug  (Buggy);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);

    rule always_fire;
        counter <= counter + 1;
    endrule

    method result if (counter == ?);
        return (counter);
    endmethod
   
endmodule
