package Testbench;

import Design::*;
import List::*;

typedef enum {Done,Waiting} State deriving (Eq,Bits);

module mkTestbench(Empty);
        Design_IFC top <- mkDesign;

                               // ack  start   valid
        List#(Maybe#(Tuple3#(Bit#(1), Bit#(1), Bit#(1)))) test;
        test = Cons( Just (tuple3 (1'b1, 1'b0, 1'b0)),
               Cons( Just (tuple3 (1'b1, 1'b0, 1'b0)),
               Cons( Just (tuple3 (1'b1, 1'b0, 1'b0)),
               Cons( Just (tuple3 (1'b1, 1'b0, 1'b0)),
               Cons( Nothing, Nil))))) ;

        Reg #(Bit#(16)) counter <- mkReg(0);
        Reg #(State) state <- mkReg(Done); 
        Reg #(Bit#(32)) passes <- mkReg(0);
        Reg #(Bit#(32)) fails <- mkReg(0);

        rule start (state == Done);
           action
             case (select (test, counter)) matches
                tagged Nothing: 
                    begin
                      $display("Passes %d, Fails %d\n", passes, fails);
                      $finish(2'b00);
                    end
                tagged Just ({.x,.y,.z}) :
                    begin
                      if (top.req == 1'b1) 
                         begin
                           $display("\nStarting with New Request\n\n");
                           top.setInput (x);
                           state <= Waiting;
                         end
                      else
                         begin
                           noAction;
                      end
                    end
             endcase
           endaction
        endrule
             

        rule recdRequest ((top.done == 1'b0) && (top.start == 1'b1) && (top.valid == 1'b1) && (state == Waiting));
           action
             case (select (test,counter)) matches
                tagged Nothing :
                    begin
                      noAction;
                    end
                tagged Just ({.x,.y,.z}) :
                    begin
                      $display("HandshakeProtocol :Step1: start =%d (expected = 1'b1), valid = %d (expected = 1'b1) \n", top.start, top.valid);
                      state <= Waiting;
                    end
             endcase
           endaction
        endrule

        rule recdAck ((top.done == 1'b0) && (top.start == 1'b0) && (top.valid == 1'b1) && (state == Waiting));
           action
             case (select (test,counter)) matches
                tagged Nothing :
                    begin
                      noAction;
                    end
                tagged Just ({.x,.y,.z}) :
                    begin
                      $display ("HandshakeProtocol :Step2: start =%d (expected = 1'b0), valid = %d (expected = 1'b1) \n", top.start, top.valid);
                       top.setInput (1'b0);
                       state <= Waiting;
                    end
             endcase
           endaction
        endrule

        rule done ((top.done == 1'b1) && (state == Waiting));
           action
              case (select (test,counter)) matches
                 tagged Just ({.x,.y,.z}) :
                     begin
                       state <= Done;
                       counter <= counter + 1; 
                       $display ("HandshakeProtocol :Step3: start =%d (expected = %d), valid = %d (expected = %d) \n", top.start, y, top.valid, z);
                        if ((top.start == y) && (top.valid == z))
                            passes <= passes + 1;
                        else 
                            fails <= fails + 1;
                     end
              endcase
           endaction
        endrule

endmodule: mkTestbench
endpackage: Testbench
