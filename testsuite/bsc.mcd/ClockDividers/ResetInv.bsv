import Clocks :: *;

(* synthesize *)
module sysResetInv();
   Reset rstin <- exposeCurrentReset;
   Clock clkin <- exposeCurrentClock;
   
   // Create a reset signal
   let rstA  <- mkReset(3, True, clkin);
   
   // Create an inverted reset signal
   Reset rstB  <- mkResetInverter(rstA.new_rst);
   
   Reg#(int)  counterA <- mkReg(0, reset_by rstA.new_rst);
   Reg#(int)  counterB <- mkReg(0, reset_by rstB);
   
   Reg#(int)  counter  <- mkReg(0);
   
   rule everyA;
      counterA <= counterA + 1;
      $display("CounterA clocked and its current value is %d", counterA);
   endrule
   
   rule everyB;
      counterB <= counterB + 1;
      $display("CounterB clocked and its current value is %d", counterB);
   endrule
   
   rule every;
      counter <= counter + 1;
   endrule
   
   rule reset_switchover(counter == 10 || counter == 43);
      rstA.assertReset();
   endrule
   
   rule testing(counter == 100);
      $finish(0);
   endrule
   
endmodule

