/* Bit Stream Parser parses the MPEG4 stream and performs VLD,
   inverse scan,inverse quantisation , AC/DC prediction , 
   MV  prediction in the MPEG-4 decoder.
*/

package Mpeg4;
import FrmBuffer :: *;
import MCR :: *;
import MkIDCT_1D :: *;
import MkIDCT_top :: *;
import BtStrmPrsr :: *;

interface Mpeg4_IFC;
  method Action get_host_strobe (Bit#(1) host_strobe) ;
  method Action get_host_select (Bit#(2) host_select) ;
  method Action get_host_address (Bit#(8) host_address) ;
  method Action get_host_datain (Bit#(8) host_datain) ;
  method Action get_vd_valid (Bit#(1) vd_valid) ;
  method Action get_vd_data  (Bit#(8) vd_data) ;
  method Bit#(1)  vd_rd () ;
  method Bit#(1)  pixelValid () ;
  method Bit#(8)  pixelVal () ;
  method Bool     busy;
  method Bool     vop_done;
  method Action   read_vop(Bit#(1) rd_vop);
  method Bit#(8)  vop_data;
  method Bool     vop_rd_done;
endinterface : Mpeg4_IFC

(* always_ready,
   always_enabled,
   synthesize ,
   CLK = "clk",
   RST_N = "reset"
*)

module mkMpeg4 (Mpeg4_IFC);

  RWire#(Bit#(1))   host_strobe();
  mkRWire           t_host_strobe(host_strobe);

  RWire#(Bit#(2))   host_select();
  mkRWire           t_host_select(host_select);

  RWire#(Bit#(8))   host_address();
  mkRWire           t_host_address(host_address);

  RWire#(Bit#(8))   host_datain();
  mkRWire           t_host_datain(host_datain);

  RWire#(Bit#(1))   vd_valid();
  mkRWire           t_vd_valid(vd_valid);

  RWire#(Bit#(8))   vd_data();
  mkRWire           t_vd_data(vd_data);

  RWire#(Bit#(1))   rdmv();
  mkRWire           t_rdmv(rdmv);

// ###############################################
// Instantiations of sub-block are done here
  IDCT_1D_IFC#(12,9) idct <- mkIDCT_top; 
  MCR_IFC            mcr  <- mkMCR;
  FrmBuffer_IFC      frmbuf <- mkFrmBuffer;
  BtStrmPrsr_IFC  parser <- mkBtStrmPrsr;

// ###############################################

  rule always_fire;

      idct.start(unpack(parser.dct_data_out),unpack(parser.dct_data_valid));
      let {idctdata,idctvalid} = idct.result;
	  let mbhdrdata = parser.header_data;
	  Bit#(9) mbNum    = tpl_1(mbhdrdata);
	  Bit#(1) mb_coded = tpl_2(mbhdrdata);
	  Bit#(4) cbpy     = tpl_3(mbhdrdata);
	  Bit#(2) cbpc     = tpl_4(mbhdrdata);
	  Bit#(1) isInter  = tpl_5(mbhdrdata);
	  Bit#(48) mvx     = tpl_6(mbhdrdata);
	  Bit#(48) mvy     = tpl_7(mbhdrdata);
      Bit#(1)  rsValid    = pack(idctvalid);
      Bit#(9)  rsPixelVal = pack(idctdata);
	  mcr.start(rsValid,
	            rsPixelVal,
			    mbNum,
			    cbpy,
			    cbpc,
			    parser.hdr_rdy,
			    mb_coded,
			    isInter,
			    mvx,
			    mvy,
			    frmbuf.sent_rd_data,
			    0);

      Tuple3#(Bit#(1),Bit#(18),Bit#(8))  write_frmdata = 
	         tuple3(mcr.pixelValid,mcr.curFrame_addr,mcr.pixelVal);

	  frmbuf.set_level(0);
	  frmbuf.write_d(write_frmdata,0);
	  frmbuf.read_d(tuple2(mcr.rd_refFrame,mcr.refFrame_addr));
	  //frmbuf.set_disable_mb_done(parser.disable_mb_done);
      parser.get_rdmv(mcr.rd_MV);
      parser.get_mb_done(frmbuf.mb_done);
     
     //if (frmbuf.vop_done)	    $display("VOP DONE HAS BEEN SET");
     //if (frmbuf.mb_done == 1)	    $display("MB DONE HAS BEEN SET");
  endrule

  rule assign_disable_mb_done_1 ( parser.disable_mb_done == 1);
    frmbuf.set_disable_mb_done(1'b1);
     //$display("DISABLING MB DONE ........");

  endrule

  rule assign_disable_mb_done_0 ( parser.disable_mb_done == 0);
    frmbuf.set_disable_mb_done(1'b0);
  endrule

  method get_host_strobe (x); 
    action 
      parser.get_host_strobe(x);
	endaction 
  endmethod : get_host_strobe 
  
  method get_host_select (x); 
    action 
      parser.get_host_select(x);
    endaction 
  endmethod : get_host_select 
  
  method get_host_address (x); 
    action
      parser.get_host_address(x);
	endaction 
  endmethod : get_host_address 
  
  method get_host_datain (x); 
    action 
      parser.get_host_datain(x);
    endaction 
  endmethod : get_host_datain 
  
  method get_vd_valid (x); 
    action 
      parser.get_vd_valid(x);
    endaction
  endmethod : get_vd_valid 
  
  method get_vd_data (x); 
    action 
      parser.get_vd_data(x);
    endaction 
  endmethod : get_vd_data 
  
  method vd_rd (); 
    vd_rd = parser.vd_rd;
  endmethod : vd_rd 
  
  method pixelValid (); 
    pixelValid = mcr.pixelValid;
  endmethod : pixelValid 
  
  method pixelVal (); 
    pixelVal = mcr.pixelVal;
  endmethod : pixelVal 
  
  method vop_done;
    vop_done = frmbuf.vop_done;
  endmethod : vop_done 

  method busy;
    busy = parser.busy;
  endmethod : busy 

  method read_vop(x);
    action 
      frmbuf.set_rd_vop(x);
    endaction
  endmethod : read_vop 

  method Bit#(8) vop_data;
    vop_data = frmbuf.vop_data;
  endmethod : vop_data 

  method vop_rd_done;
    vop_rd_done = frmbuf.vop_rd_done;
  endmethod : vop_rd_done 

endmodule : mkMpeg4

endpackage : Mpeg4
