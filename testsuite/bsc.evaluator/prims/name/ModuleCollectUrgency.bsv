import ModuleCollect::*;

module [ModuleCollect#(Bool)] mkMCUSub(Empty);
   Reg#(Bool) r <- mkReg(False);
   rule updatePosition;
      r <= !r;
   endrule
endmodule

module [ModuleCollect#(Bool)] mkMCUInner(Empty);
   Reg#(Bool) x <- mkReg(False);
   Empty controller();
   mkMCUSub the_controller(controller);
   (* descending_urgency = "tick,the_controller.updatePosition" *)
   rule tick;
      x <= !x;
   endrule
endmodule

(* synthesize *)
module sysModuleCollectUrgency(Empty);
   IWithCollection#(Bool, Empty) ecs <- exposeCollection(mkMCUInner);
endmodule
