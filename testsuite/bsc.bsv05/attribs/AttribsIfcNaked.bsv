function ActionValue#(Reg#(Bool)) f();
   actionvalue
      (* foo *)
      interface Reg;
	 method _read = ?;
	 method _write = ?;
      endinterface
      return ?;
   endactionvalue
endfunction


