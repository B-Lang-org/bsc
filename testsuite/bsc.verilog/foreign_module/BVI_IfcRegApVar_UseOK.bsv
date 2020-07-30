import "BVI"
module mkMod(Reg#(a));
   method       _write(D_IN) enable(EN);
   method Q_OUT _read();
   schedule _read CF _read;
   schedule _read SB _write;
   schedule _write SBR _write;
endmodule

(* synthesize *)
module sysBVI_IfcRegApVar_UseOK();
   Reg#(Bool) rg <- mkMod;
endmodule
