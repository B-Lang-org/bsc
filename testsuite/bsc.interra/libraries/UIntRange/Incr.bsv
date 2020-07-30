package Incr;
import UIntRange :: *;

module mkTestbench_Incr ();

   Reg #(UIntRange #(5, 10)) mydata();
   mkReg #(10) the_mydata(mydata);
   
   Reg #(UInt #(4)) check_mydata();
   mkReg #(10) the_check_mydata(check_mydata);

   Reg #(Bit #(8)) count();
   mkReg #(0) the_count(count);

   Reg #(Bool) fail();
   mkReg #(False) the_fail(fail);

   rule fire_always (count < 8'b11111110);
       UIntRange #(5, 10) mydata_in = unpack(pack (check_mydata));
       count <= count + 1;
       $display("Data = %d", mydata);
       mydata <= incr (mydata);
       if (mydata_in != mydata)
          fail <= True;
       if (check_mydata == 10)
          check_mydata <= 5;
       else
          check_mydata <= check_mydata + 1;
   endrule

   rule endsim (count == 8'b11111110);
      if (!fail) 
         $display ("Simulation Passes");
      else
         $display ("Simulation Fails");
      $finish (2'b00);
   endrule


endmodule : mkTestbench_Incr

endpackage : Incr
