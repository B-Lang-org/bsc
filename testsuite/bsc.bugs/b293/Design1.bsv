package Design1 ;

interface Design_IFC ;
    method Action shift_and_add (Bit#(4) a,Bit#(4) b,Bit#(1) load);
    method Bit#(1) done();
    method Bit#(8) product();
endinterface: Design_IFC


  
(*
       synthesize,
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
*)
module mkDesign1 (Design_IFC);

  Reg#(Bit#(4)) multiplier <- mkReg(0);
  Reg#(Bit#(8)) multiplicand <- mkReg(0);
  Reg#(Bit#(8)) accumulator  <- mkReg(0);
  Reg#(Bit#(1)) done_reg <- mkReg(0);
  Reg#(Bit#(4)) count    <- mkReg(0);
  Reg#(Bit#(1)) enable   <- mkReg(0);

rule working ((enable == 1) && (count != 4)) ;
        begin
     Bit#(1) x;
          //if (multiplier[0] == 1'b1) 
          x = multiplier[0];
          if (x == 1) 
             accumulator <= accumulator + multiplicand ;
          else 
             accumulator <= accumulator;
          multiplier <= multiplier >> 1;
          multiplicand <= multiplicand << 1;
          count <= count + 1;
          done_reg <= 1'b0;
        end
endrule

rule done_rule ;
        begin
          count <= 0;
          done_reg <= 1;
          enable <= 0;
        end
endrule 

  method  shift_and_add (a,b,load);
    action
     if ((load == 1) && (count == 0 )) 
        begin
          accumulator <= 0;
          multiplicand <= {4'b0000,a};
          multiplier <= b;
          count <= 0;
          done_reg <= 1'b0;
          enable <= 1'b1;
        end
    endaction
  endmethod: shift_and_add

  method done();
     done = done_reg;
  endmethod: done

  method product();
     product = accumulator;
  endmethod: product


endmodule: mkDesign1
endpackage: Design1 
