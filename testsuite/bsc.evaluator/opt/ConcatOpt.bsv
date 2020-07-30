// Test optimization of e1 ++ e2 == e3
(* synthesize *)
module sysConcatOpt(Empty);

  Reg#(Bit#(3)) r();
  mkReg#(3'b111) i_r(r);

  Reg#(Bit#(5)) s();
  mkReg#(5'b01010) i_s(s);

  Reg#(Bit#(4)) counter();
  mkReg#(0) i_counter(counter);

  rule done (counter == 2);
    $finish(0);
  endrule: done

  rule increment (True);
    counter <= counter + 1;
    if(counter < 2)
    begin
      r <= truncate(s);
      s <= zeroExtend(r);
    end
  endrule: increment

  rule check (True);
   if(counter == 0) // r == 3'b111, s == 5'b01010
     begin 
       if({r,2'b0} == 'b11100)
         $display("Pass 1");
       else
         $display("Fail 1");
       if({2'b0,r} == 'b11100)
         $display("Fail 2");
       else
         $display("Pass 2"); 
       if({s,r} == 'b01010111)
         $display("Pass 3");
       else
         $display("Fail 3");
       if({r,r} == 'b11111)
         $display("Fail 4");
       else
         $display("Pass 4");
       if({r,s} == 'b11101010)
         $display("Pass 5");
       else 
         $display("Fail 5");
     end 
   else if (counter == 1) // r == 3'010 s == 5'00111
     begin
       if({s,2'b0} == 'b0011100)
         $display("Pass 6");
       else
         $display("Fail 6");
       if({2'b0,s} == 'b0000111)
         $display("Pass 7");
       else
         $display("Fail 7");
       if({r,s} == 'b01000111)
         $display("Pass 8");
       else
         $display("Fail 8");
       if({s,s} == 'b00111)
         $display("Fail 9");
       else
         $display("Pass 9");
       if({s,r} == 'b00111010)
         $display("Pass 10");
       else
         $display("Fail 10");
     end
  endrule: check
endmodule