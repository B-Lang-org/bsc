package EdgeDetect;

interface RequestDetect;
   method Action send();
   method Bool   pulse();
   // Whether a request is in progress
   method Bool   pending();
   // If the sender is holding the value high and the user of the
   // edge pulse is ready for another request, call this method.
   method Action ack();
endinterface

module mkRequestDetect (RequestDetect);

   Reg#(Bool) inRequest <- mkReg(False);
   PulseWire send_wire <- mkPulseWire();
   PulseWire ack_wire  <- mkPulseWire();
   PulseWire edge_wire <- mkPulseWire();

   (* fire_when_enabled, no_implicit_conditions *)
   rule update;
      if (!inRequest) begin
         if (send_wire) begin
            inRequest <= True;
            edge_wire.send();
         end
      end
      else begin // inRequest
         if (!send_wire || ack_wire) begin
            inRequest <= False;
         end
      end
   endrule

   method send = send_wire.send;
   method ack  = ack_wire.send;

   method pulse = edge_wire;
   method pending = inRequest;

endmodule

endpackage
