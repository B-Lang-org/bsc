import Connectable::*;

//this example should fail to compile, because they are two different clocks

(*synthesize*)
module sysCheckClocks_ConnectTwoModArg_DiffClock
         (Clock c1,
          Clock c2,
          (*clocked_by="c1", reset_by="no_reset"*)
          Inout#(int) x1,
          (*clocked_by="c2", reset_by="no_reset"*)
          Inout#(int) x2,
          Empty e);
   mkConnection(x1,x2);
endmodule

