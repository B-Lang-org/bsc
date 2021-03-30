interface IFC;
   method Bool get();
endinterface

module mkModuleParametersInModule (IFC);
   module mkParams#(parameter Bool v) (IFC);
      method get = v;
   endmodule

   IFC i <- mkParams(True);

   method get = i.get;
endmodule
