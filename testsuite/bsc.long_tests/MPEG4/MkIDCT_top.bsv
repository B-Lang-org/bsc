////////////////////////////////////////////////////////////////////////////
/////////////Integrated IDCT Module/////////////////////////////////

package MkIDCT_top;

import MkIDCT_1D :: *;
import MkIDCT_col :: *;
import MkIDCT_row :: *;
import TBuffer :: *;


(*synthesize,
  CLK = "clk",
  RST_N = "reset"
*)

module mkIDCT_top (IDCT_1D_IFC#(12,9));
    
    IDCT_1D_IFC#(12,16) row();
    mkIDCT_row the_row(row);
    IDCT_1D_IFC#(16, 9) col();
    mkIDCT_col the_col(col);
    TBuffer_IFC#(16) tbuffer();
    mkTBuffer the_buffer(tbuffer);
   
    rule always_fire (True);
        tbuffer.start (row.result);
        col.start (tpl_1(tbuffer.result), tpl_2(tbuffer.result));
    endrule
    
    method start (a, b);
     action
        row.start (a,b);
     endaction
    endmethod : start
    
    method result ();
        return (col.result); 
    endmethod : result

endmodule : mkIDCT_top


endpackage : MkIDCT_top
