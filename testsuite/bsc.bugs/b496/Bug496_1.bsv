
//here parameter a will be of type Bit 16
//and parameter b will be of type Bit 1

interface Design_IFC #(parameter type a,parameter type b);
    method Action start(a term,b load);
    method a fact();
    method b done();
endinterface:  Design_IFC

(*
   always_enabled,
   always_ready 
*)
module mkDesign(Design_IFC #(Bit#(16),Bit#(1)));
    Reg#(Bit#(16)) count();
    mkReg#(0) the_count(count);

    Reg#(Bit#(16)) fact_val();
    mkReg#(1) the_fact_val(fact_val);

    Reg#(Bit#(1)) done_reg();
    mkReg#(0) the_done_reg(done_reg);

    Reg#(Bit#(1)) enable();
    mkReg#(0) the_enable(enable);

    Reg#(Bit#(16)) term();
    mkReg#(0) the_term(term);

    method Action start(Bit#(16) term,Bit#(1) load);
        action
            if ((load == 1) && (count == 0))  
            begin
                    count    <= 0 ;
                    term     <= term;
                    done_reg <= 0;
                    fact_val <= 1;
                    enable   <= 1;
            end
            else if ((enable == 1) && (count != term)) 
            begin
                    count    <=  count + 1;
                    fact_val <= fact_val * (count + 1);
            end
            else 
            begin
                  count <= 0;
                  done_reg <= 1;
                  enable <= 0;
            end
        endaction          
    endmethod: start

    method Bit#(16) fact();
       fact = fact_val;
    endmethod: fact
 
    method Bit#(1) done();     
      done = done_reg;
    endmethod: done
endmodule: mkDesign

