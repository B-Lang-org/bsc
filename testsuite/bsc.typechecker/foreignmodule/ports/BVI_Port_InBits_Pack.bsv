import "BVI" Foo =
   module mkFoo#(UInt#(32) v) (Reg#(Bool));
      port p = pack(v);
      method _write(D_IN) enable(EN);
      method Q_OUT _read;
      schedule _read SB _write;
      schedule _read CF _read;
      schedule _write SBR _write;
   endmodule
