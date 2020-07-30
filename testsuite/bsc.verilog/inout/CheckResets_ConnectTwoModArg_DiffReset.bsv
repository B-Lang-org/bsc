import Connectable::*;

//this example should fail to compile, because they are two different resets

(*synthesize*)
module sysCheckResets_ConnectTwoModArg_DiffReset
         (Reset r1,
          Reset r2,
          (*reset_by="r1"*)
          Inout#(int) x1,
          (*reset_by="r2"*)
          Inout#(int) x2,
          Empty e);
   mkConnection(x1,x2);
endmodule

