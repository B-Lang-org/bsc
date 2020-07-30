import "BVI" Foo =
   module mkFoo (Reg#(Bool));
      parameter p = 1.2;
      method _write(D_IN) enable(EN);
      method Q_OUT _read;
      schedule _read SB _write;
      schedule _read CF _read;
      schedule _write SBR _write;
   endmodule
