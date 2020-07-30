import "BVI" Foo =
   module mkFoo#(String v) (Reg#(Bool));
      parameter p = v;
      method _write(D_IN) enable(EN);
      method Q_OUT _read;
      schedule _read SB _write;
      schedule _read CF _read;
      schedule _write SBR _write;
   endmodule
