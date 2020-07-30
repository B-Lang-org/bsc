//This case creates ten back to back inverters, each inverter inside a module.

package Ten_Inverters;

interface Inout;
  method Action func (Bool in1);
  method Bool outval();
endinterface


(* synthesize *)
module mkInverter (Inout);
  
  RWire #(Bool) temp1();
  mkRWire the_temp1 (temp1);
  
  RWire #(Bool) temp2();
  mkRWire the_temp2 (temp2);
  
  rule always_fire;
      Bool inp = ! (unJust (temp1.wget));
      temp2.wset (inp);
  endrule
      
  method Action func (in1);
      temp1.wset (in1);
  endmethod

  method outval;
      return (unJust (temp2.wget));
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


