import Vector::*;

interface Ifc#(numeric type max_elems, type elem_type);
   method Vector#(max_elems, elem_type) recv();
endinterface


module sysContextTooWeakDeferred(Ifc#(m,e))
   provisos ( Bits#(e, esz), Div#(esz, 8, e_bytes) );

   Reg#(Vector#(TMul#(m, e_bytes), Bit#(8))) in_buf <- mkRegU();

   // XXX used the wrong variable names in the type signature
   method Vector#(max_elems, elem_type) recv();

      Vector#(max_elems, Vector#(e_bytes, Bit#(8))) bs = unpack(pack(in_buf));
      function bytes_to_elem(v) = unpack(truncate(v));
      Vector#(max_elems, elem_type) es = map(bytes_to_elem, bs);

      return es;
   endmethod

endmodule

