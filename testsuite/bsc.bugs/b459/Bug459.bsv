package Testbench ;

typedef enum  {Start , Wait,State0 , State1 , State2 , State3 , State4 , State5 } State deriving (Eq, Bits);



module mkTestbench (Empty);

    Reg #(Bit#(8)) counter <- mkReg(0);
    Reg #(State) state <- mkReg(Start);

    rule rule_1 (state == Start);
       action 
             state <= State1;
       endaction
    endrule

     rule rule_2 (state == State1);
     action
            if(counter != 100)
            begin
              counter <= counter + 1;
              state <= State1;
            end
            else
            begin
              state <= State2;
            end
     endaction  
     endrule

    
      rule rule_1 (state == State2);
       action 
             counter <= 0;
             state <= State3;
       endaction
    endrule


endmodule: mkTestbench
endpackage: Testbench



