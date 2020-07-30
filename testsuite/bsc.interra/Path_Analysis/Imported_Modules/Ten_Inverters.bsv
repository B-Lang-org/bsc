//This case creates ten back to back inverters, each inverter inside a module.

package Ten_Inverters;

interface Inoutv;
  method Action func (Bit #(1) in1);
  method Bit #(1) outval();
endinterface


import "BVI" Imported_Verilog = 
    module mkInverterv (Inoutv);
        method func (In1) enable(Enable);
        method OutVal outval();
        path (In1, OutVal);
    endmodule

interface Inout;
  method Action func (Bool in1);
  method Bool outval();
endinterface

(* synthesize *)
module [Module] mkInverter (Inout);
  
  Inoutv dut ();
  mkInverterv the_dut(dut);

  method Action func (in1);
      dut.func (in1 ? 1 : 0);
  endmethod

  method Bool outval();
      return (dut.outval==1 ? True : False);
  endmethod

endmodule



(* synthesize *)
module mkTen_Inverters();

  Inout t1();
  mkInverter the_t1 (t1);
  
  Inout t2();
  mkInverter the_t2 (t2);

  Inout t3();
  mkInverter the_t3 (t3);

  Inout t4();
  mkInverter the_t4 (t4);

  Inout t5();
  mkInverter the_t5 (t5);

  Inout t6();
  mkInverter the_t6 (t6);

  Inout t7();
  mkInverter the_t7 (t7);

  Inout t8();
  mkInverter the_t8 (t8);

  Inout t9();
  mkInverter the_t9 (t9);

  Inout t10();
  mkInverter the_t10 (t10);

  rule always_true;
      t1.func (t10.outval);
      t2.func (t1.outval);
      t3.func (t2.outval);
      t4.func (t3.outval);
      t5.func (t4.outval);
      t6.func (t5.outval);
      t7.func (t6.outval);
      t8.func (t7.outval);
      t9.func (t8.outval);
      t10.func (t9.outval);
  endrule
  
endmodule 
endpackage 


