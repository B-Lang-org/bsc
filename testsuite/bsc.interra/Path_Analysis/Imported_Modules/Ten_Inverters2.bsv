//This case creates ten back to back inverters, each inverter inside a module.


package Ten_Inverters2;

interface Inoutv;
  method Bit #(1) func(Bit #(1) a);
endinterface

interface Inout;
  method Bool func (Bool a);
endinterface


import "BVI" Imported_Verilog = 
    module mkInverterv (Inoutv);
        method Bit #(1) func (In1, Out1);
        path (In1, Out1);
    endmodule

(* synthesize *)
module [Module] mkInverter(Inout);
    
    Inoutv dut();
    mkInverterv the_dut (dut);

    method func(a);
        return (dut.func (a?1:0) == 1 ? True : False);
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

  RWire #(Bool) temp();
  mkRWire the_temp (temp);

  rule always_true;
      temp.wset (t1.func (t2.func (t3.func (t4.func (t5.func (t6.func
              (t7.func (t8.func (t9.func (t10.func(unJust(temp.wget))))))))))));
      
  endrule
  
endmodule 
endpackage 


