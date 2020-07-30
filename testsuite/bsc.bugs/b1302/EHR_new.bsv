import Vector::*;
import Probe::*;

typedef  Vector#(n_sz, Reg#(alpha)) EHR#(type n_sz, type alpha);

module mkEHR#(alpha init) (EHR#(n,alpha)) provisos(Bits#(alpha, asz),
						   Add#(li,1,n));

   Reg#(alpha)  r <- mkReg(init);
   Vector#(n, RWire#(alpha)) wires  <- replicateM(mkRWire);
   Vector#(n, Wire#(alpha)) probes <- replicateM(mkWire);
   Vector#(n, Reg#(alpha)) vidx = newVector();
   Vector#(n, alpha) chain = newVector();

   for(Integer i = 0; i < valueOf(n); i = i + 1)
      begin
        if(i==0) chain[i] = r;
        else chain[i] = fromMaybe(chain[i-1], wires[i-1].wget());
      end

   for(Integer j = 0; j < valueOf(n); j = j + 1)
      begin
        vidx[j] = interface Reg
                      method _read();
                         return chain[j];
                      endmethod
                      method Action _write(x);
                         (probes[j]) <= chain[j];
                         wires[j].wset(x);
                      endmethod
                   endinterface;
      end

   rule do_stuff(True);
      r <= fromMaybe(chain[valueOf(li)], wires[valueOf(li)].wget());
   endrule

   return  vidx;
endmodule

