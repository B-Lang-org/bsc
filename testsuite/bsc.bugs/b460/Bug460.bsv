// --------------------------------------------------------
//
//    BSC-3.8.7 fails to detect the condition where a Bool
//    and an Interface are inadvertently called the same name.
//
//    In this test case an Interface and a Bool are both called
//    by the same name, rdy. BSC does not detect this condition
//    and generates verilog without any errors or warnings.
//    Inspection of the resulting verilog indicates the order
//    of instantiation affects what value gets chosen by method
//    get_rdy.  If "Interface rdy" is defined after "Bool rdy"
//    then "Interface rdy" is used.  If "Bool rdy" is defined
//    after the interface then "Bool rdy" is used.
//
// ---------------------------------------------------------

interface Interface_reg #(type addr_type, type data_type);
   method Bool get_rdy();
endinterface // interface_reg

(* synthesize *)
module bug_reg_bool_same_name (Interface_reg #(Bool,Bool));

   Bool rdy = True;

   Reg#(Bool) rdy();
   mkReg #(False) u_rdy (rdy);

   method Bool get_rdy();
      get_rdy = rdy;
   endmethod

endmodule // module_reg

