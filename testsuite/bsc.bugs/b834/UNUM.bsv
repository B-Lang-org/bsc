package UNUM;

import Vector::*;

/**************************************************/
/* Typedefs                                       */
/**************************************************/

typedef Vector#(n, Maybe#(a)) PluriBUS#(type a, type n);

/**************************************************/
/* Interfaces                                     */
/**************************************************/

//For now exceptions live in the bundles on the front end (Pre-CCU).
//And in the Responses in the back end (post-CCU).
//Later we may hide them in PluriBUS.

interface ICache #(type iaddress, 
                   type packed_inst_bundle, 
                   //Bus width
		   type out_w);

    //for Fetch

    method Action handleICacheRequest(iaddress x);
    method ActionValue#(PluriBUS#(packed_inst_bundle, out_w)) iCacheResponse();

    method Action flush();
    
endinterface


interface Fetch #(type inst_bundle, 
      	      	  type packed_inst_bundle, 
		  type inst_addr, 
		  type bpred_update,
                  //Bus widths
                  type in_w, 
		  type out_w);

    //For Decode
    
    method ActionValue#(PluriBUS#(inst_bundle, out_w)) fetch();
    
    //For CCU
    
    method Action handleSetPC(inst_addr data);
    method Action updateBranchPredictor(bpred_update x);
    
    //For ICache
    
    method Action handleICacheResponse(PluriBUS#(packed_inst_bundle, in_w) data);
    method ActionValue#(inst_addr) iCacheRequest();
    
    method Action flush();
    
endinterface


interface Decode #(type dec_inst, 
                   type inst_bundle, 
                   //Bus widths
		   type in_w, 
		   type out_w);

    //For CCU

    method ActionValue#(PluriBUS#(dec_inst, out_w)) decode();

    //For Fetch

    method Action handleFetch(PluriBUS#(inst_bundle, in_w) data);

    method Action flush();
    
endinterface


interface CCU #(type dec_inst,  	 type inst_addr, 
    	        type bpred_update,	 type fuu_inst, 
	        type fuu_res,		 type bru_inst,
		type bru_res,            type lsu_inst, 
	        type lsu_res,		 type lsu_tag,
                //Bus widths
                type dec_w,		 type fuu_in_w, 
	        type fuu_out_w, 	 type bru_in_w,
		type bru_out_w,          type lsu_ccu_w, 
	        type ccu_lsu_w, 	 type lsu_com_w);

    //From Decode

    method Action handleDecode(PluriBUS#(dec_inst, dec_w) data);

    //For Fetch

    method ActionValue#(inst_addr) setPC();

    //For Branch Predictor (Fetch)

    method ActionValue#(bpred_update) updateBranchPredictor();

    //For FUU

    method ActionValue#(PluriBUS#(fuu_inst, fuu_in_w)) issue();
    method Action handleComplete(PluriBUS#(fuu_res, fuu_out_w) data);

    //For BRU
    
    method ActionValue#(PluriBUS#(bru_inst, bru_in_w)) issueBR();
    method Action handleBRComplete(PluriBUS#(bru_res, bru_out_w) data);

    //For LSU

    method ActionValue#(PluriBUS#(lsu_inst, ccu_lsu_w)) issueLS();
    method Action handleLSComplete(PluriBUS#(lsu_res, lsu_ccu_w) data); 
    method ActionValue#(PluriBUS#(lsu_tag,lsu_com_w)) commitStore();
    method ActionValue#(Tuple2#(lsu_tag,lsu_tag)) invalidateStore();

    method Action flush();
    
endinterface


interface FUU #(type fuu_inst, 
    	        type fuu_result, 
                //Bus widths
                type in_w, 
	        type out_w);

    //For CCU

    method Action handleIssue(PluriBUS#(fuu_inst, in_w) data);
    method ActionValue#(PluriBUS#(fuu_result, out_w)) complete();

    method Action flush();
    
endinterface


interface BRU #(type bru_inst, 
                type bru_result, 
                //Bus widths
                type in_w, 
		type out_w);
   
   //For CCU
          
   method Action handleBRIssue(PluriBUS#(bru_inst, in_w) x);
   method ActionValue#(PluriBUS#(bru_result, out_w)) completeBR();

   method Action flush();

endinterface


interface LSU #(type dcache_resp, 
                type dcache_req, 
                type lsu_inst, 
		type lsu_res, 
		type lsu_tag,
                //Bus widths
                type ccu_lsu_w, 
		type lsu_ccu_w, 
		type ccu_com_w, 
                type dcache_in_w, 
		type dcache_out_w);

    //For DCache

    method Action handleCacheResponse(PluriBUS#(dcache_resp, dcache_out_w) data);
    method ActionValue#(PluriBUS#(dcache_req, dcache_in_w)) lsRequest();

    //For CCU

    method Action handleLSIssue(PluriBUS#(lsu_inst, ccu_lsu_w) data);
    method ActionValue#(PluriBUS#(lsu_res, lsu_ccu_w)) completeLS();

    method Action handleCommitStore(PluriBUS#(lsu_tag, ccu_com_w) data);
    method Action handleInvalidateStore(lsu_tag oldest, lsu_tag newest);

    method Action flush();

endinterface


interface DCache #(type dcache_req, 
                   type dcache_resp, 
                   //Bus widths
		   type in_w, 
		   type out_w);

    //For LoadStore

    method Action handleLSRequest(PluriBUS#(dcache_req, in_w) data);
    method ActionValue#(PluriBUS#(dcache_resp, out_w)) cacheResponse();

    method Action flush();
    
endinterface


interface RegisterFile #(type reg_addr, 
    	    	    	 type reg_data, 
                         //Bus widths
			 type read_w, 
			 type write_w);

    //For CCU

    // XXX Split because of Bug 247
    method PluriBUS#(reg_data, read_w)  readReg_Value(PluriBUS#(reg_addr, read_w) data);
    method Action                       readReg_Action(PluriBUS#(reg_addr, read_w) data);

    method Action writeReg(PluriBUS#(Tuple2#(reg_addr, reg_data), write_w) data);

    method Action flush();
    
endinterface

interface SplitPortRegFile #(type reg_addr, 	    type reg_data, 
                             type ccu_rw,   	    type fuu_rw, 
			     type lsu_rw,   	    type other_rw,
		    	     type ccu_ww,   	    type fuu_ww, 
			     type lsu_ww,   	    type other_ww);
    
    //For CCU
    method PluriBUS#(reg_data, ccu_rw) readCCU(PluriBUS#(reg_addr, ccu_rw) data);
    method Action                      readCCU_Action(PluriBUS#(reg_addr, ccu_rw) data);

    method Action writeCCU(PluriBUS#(Tuple2#(reg_addr, reg_data), ccu_ww) data);
    
    //For FUU
    method PluriBUS#(reg_data, fuu_rw) readFUU(PluriBUS#(reg_addr, fuu_rw) data);
    method Action                      readFUU_Action(PluriBUS#(reg_addr, fuu_rw) data);

    method Action writeFUU(PluriBUS#(Tuple2#(reg_addr, reg_data), fuu_ww) data);
    
    
    //For LSU
    method PluriBUS#(reg_data, lsu_rw) readLSU(PluriBUS#(reg_addr, lsu_rw) data);
    method Action                      readLSU_Action(PluriBUS#(reg_addr, lsu_rw) data);

    method Action writeLSU(PluriBUS#(Tuple2#(reg_addr, reg_data), lsu_ww) data);
    
    //For any other user
    method PluriBUS#(reg_data, other_rw) readOther(PluriBUS#(reg_addr, other_rw) data);
    method Action                        readOther_Action(PluriBUS#(reg_addr, other_rw) data);

    method Action writeOther(PluriBUS#(Tuple2#(reg_addr, reg_data), other_ww) data);
    
    method Action flush(); 
    
endinterface


interface Processor;

  //More needed here?
  method Action start();
  method Action stop();

endinterface


interface Monitor #(type iaddress,	     type instbundle,
    	    	    type bundle,	     type dec_bundle, 
                    type bpred_update,       type fuu_inst, 
		    type fuu_res,	     type bru_inst,
		    type bru_res,            type lsu_inst, 
		    type lsu_res,	     type lsu_tag, 
		    type dcache_req,	     type dcache_resp,
                    type fetch_w,	     type decode_w, 
		    type ccu_w, 	     type fuu_in_w, 
		    type fuu_out_w,	     type bru_in_w,
		    type bru_out_w,          type lsu_in_w, 
		    type lsu_out_w,	     type lsu_com_w, 
		    type dcache_in_w,	     type dcache_out_w);

    //General for the Processor
    method Action start();
    method Action stop();

    //for ICache/Fetch
    method Action monitorICacheRequest(iaddress x);
    method Action monitorICacheResponse(PluriBUS#(instbundle, fetch_w) x);
    
    //for Fetch/Decode
    method Action monitorFetch(PluriBUS#(bundle, decode_w) data);
    
    //for Decode/CCU
    method Action monitorDecode(PluriBUS#(dec_bundle, ccu_w) data);
    
    //for CCU/Fetch
    method Action monitorSetPC(iaddress data);
    method Action monitorBranchPredictor(bpred_update x);
    
    //for CCU/FUU
    method Action monitorIssue(PluriBUS#(fuu_inst, fuu_in_w) data);
    method Action monitorComplete(PluriBUS#(fuu_res, fuu_out_w) data);
    
    //for CCU/BRU
    method Action monitorBRIssue(PluriBUS#(bru_inst, bru_in_w) data);
    method Action monitorBRComplete(PluriBUS#(bru_res, bru_out_w) data);

    //for CCU/LSU
    method Action monitorLSIssue(PluriBUS#(lsu_inst, lsu_in_w) data);
    method Action monitorLSComplete(PluriBUS#(lsu_res, lsu_out_w) data);
    method Action monitorCommitStore(PluriBUS#(lsu_tag, lsu_com_w) data);
    method Action monitorInvalidateStore(lsu_tag oldest, lsu_tag newest);
    
    //for LSU/DCache
    method Action monitorLSRequest(PluriBUS#(dcache_req, dcache_in_w) data);
    method Action monitorCacheResponse(PluriBUS#(dcache_resp, dcache_out_w) data);
    
endinterface


module mkEmptyMonitor (Monitor#(iaddress,   	    instbundle, 
    	    	    	    	bundle,     	    dec_bundle, 
                		bpred_update, 	    fuu_inst, 
				fuu_res,    	    bru_inst,
				bru_res,            lsu_inst, 
				lsu_res,    	    lsu_tag, 
				dcache_req, 	    dcache_resp,
                		fetch_w,    	    decode_w, 
				ccu_w,      	    fuu_in_w, 
				fuu_out_w,  	    bru_in_w,
				bru_out_w,          lsu_in_w, 
				lsu_out_w,  	    lsu_com_w, 
				dcache_in_w, 	    dcache_out_w));

    method Action start();
      noAction;
    endmethod

    method Action stop();
      noAction;
    endmethod
    
    method Action monitorICacheRequest(iaddress x);
      noAction;
    endmethod
    
    method Action monitorICacheResponse(PluriBUS#(instbundle, fetch_w) x);
      noAction;
    endmethod
    
    method Action monitorFetch(PluriBUS#(bundle, decode_w) data);
      noAction;
    endmethod
    
    method Action monitorDecode(PluriBUS#(dec_bundle, ccu_w) data);
      noAction;
    endmethod
    
    method Action monitorSetPC(iaddress data);
      noAction;
    endmethod
    
    method Action monitorBranchPredictor(bpred_update x);
      noAction;
    endmethod
    
    method Action monitorIssue(PluriBUS#(fuu_inst, fuu_in_w) data);
      noAction;
    endmethod
    
    method Action monitorComplete(PluriBUS#(fuu_res, fuu_out_w) data);
      noAction;
    endmethod
    
    method Action monitorBRIssue(PluriBUS#(bru_inst, bru_in_w) data);
      noAction;
    endmethod
    
    method Action monitorBRComplete(PluriBUS#(bru_res, bru_out_w) data);
      noAction;
    endmethod
    
    method Action monitorLSIssue(PluriBUS#(lsu_inst, lsu_in_w) data);
      noAction;
    endmethod
    
    method Action monitorLSComplete(PluriBUS#(lsu_res, lsu_out_w) data);
      noAction;
    endmethod
    
    method Action monitorCommitStore(PluriBUS#(lsu_tag, lsu_com_w) data);
      noAction;
    endmethod
    
    method Action monitorInvalidateStore(lsu_tag oldest, lsu_tag newest);
      noAction;
    endmethod
    
    method Action monitorLSRequest(PluriBUS#(dcache_req, dcache_in_w) data);
      noAction;
    endmethod
    
    method Action monitorCacheResponse(PluriBUS#(dcache_resp, dcache_out_w) data);
      noAction;
    endmethod
    
endmodule


module [Module] mkProcessor #(ICache#(iaddress, inst, fetch_w)	     	    icache,

                              Fetch#(bundle, inst, iaddress, 
			      	     bp_update, fetch_w, dec_w)     	    fetch,
				     
			      Decode#(dec_bundle, bundle, 
			    	      dec_w, ccu_w) 	    	    	    decode,
				      
			      CCU#(dec_bundle, iaddress, bp_update, 
			      	   fuu_req, fuu_resp, bru_req,
				   bru_resp, lsu_req, lsu_resp, 
				   lsu_tag, ccu_w, fuu_in_w, 
				   fuu_out_w, bru_in_w, bru_out_w,
				   lsu_out_w, lsu_in_w, lsu_com_w)     	    ccu,
				   
			      FUU#(fuu_req, fuu_resp, 
			    	   fuu_in_w, fuu_out_w)     	    	    fuu,
				   
			      BRU#(bru_req, bru_resp, 
			    	   bru_in_w, bru_out_w)     	    	    bru,
				   
			      LSU#(dcache_resp, dcache_req, 
			      	   lsu_req, lsu_resp, lsu_tag,
			    	   lsu_in_w, lsu_out_w, lsu_com_w, 
				   dc_in_w, dc_out_w) 	    	    	    lsu,
				   
			      DCache#(dcache_req, dcache_resp, 
			      	      dc_in_w, dc_out_w)    	    	    dcache,
			      
			      Monitor#(iaddress, inst, bundle, 
			      	       dec_bundle, bp_update, 
				       fuu_req, fuu_resp, bru_req,
				       bru_resp, lsu_req, lsu_resp, 
				       lsu_tag, dcache_req, dcache_resp, 
				       fetch_w, dec_w, ccu_w, fuu_in_w, 
				       fuu_out_w, bru_in_w, bru_out_w,
				       lsu_in_w, lsu_out_w, lsu_com_w,
			    	       dc_in_w, dc_out_w)   	    	    monitor,
				       
			      Action 	    	    	    	    	    onStart, 
			      Action 	    	    	    	    	    onStop) 
			      
			      (Processor);
			     
  (* fire_when_enabled *)			     
  rule fetch_to_icache;
    let x <- fetch.iCacheRequest();
    monitor.monitorICacheRequest(x);
    icache.handleICacheRequest(x);
  endrule

  (* fire_when_enabled *)
  rule icache_to_fetch;
    let x <- icache.iCacheResponse();
    monitor.monitorICacheResponse(x);
    fetch.handleICacheResponse(x);
  endrule

  (* fire_when_enabled *)
  rule fetch_to_decode;
      let x <- fetch.fetch();
      monitor.monitorFetch(x);
      decode.handleFetch(x);
  endrule
  
  (* fire_when_enabled *)
  rule decode_to_ccu;
      let x <- decode.decode();
      monitor.monitorDecode(x);
      ccu.handleDecode(x);
  endrule
  
  (* fire_when_enabled *)
  rule ccu_to_lsu;
      let x <- ccu.issueLS();
      monitor.monitorLSIssue(x);
      lsu.handleLSIssue(x);
  endrule

  (* fire_when_enabled *)
  rule lsu_to_ccu;
      let x <- lsu.completeLS();
      monitor.monitorLSComplete(x);
      ccu.handleLSComplete(x);
  endrule

  (* fire_when_enabled *)
  rule ccu_to_lsu_commit;
      let x <- ccu.commitStore();
      monitor.monitorCommitStore(x); 
      lsu.handleCommitStore(x); 
  endrule

  (* fire_when_enabled *)
  rule ccu_to_lsu_invalidate;
      let x <- ccu.invalidateStore();
      match {.oldest,.newest} = x;
      monitor.monitorInvalidateStore(oldest, newest); 
      lsu.handleInvalidateStore(oldest, newest); 
  endrule
  
  (* fire_when_enabled *)
  rule fuu_to_ccu;
      let x <- fuu.complete();
      monitor.monitorComplete(x);
      ccu.handleComplete(x);
  endrule

  (* fire_when_enabled *)
  rule ccu_to_fuu;
      let x <- ccu.issue();
      monitor.monitorIssue(x);
      fuu.handleIssue(x);
  endrule
  
  (* fire_when_enabled *)
  rule bru_to_ccu;
      let x <- bru.completeBR();
      monitor.monitorBRComplete(x);
      ccu.handleBRComplete(x);
  endrule

  (* fire_when_enabled *)
  rule ccu_to_bru;
      let x <- ccu.issueBR();
      monitor.monitorBRIssue(x);
      bru.handleBRIssue(x);
  endrule
  
  (* fire_when_enabled *)
  rule lsu_to_dcache;
      let x <- lsu.lsRequest();
      monitor.monitorLSRequest(x);
      dcache.handleLSRequest(x);
  endrule

  (* fire_when_enabled *)
  rule dcache_to_lsu;
      let x <- dcache.cacheResponse();
      monitor.monitorCacheResponse(x);
      lsu.handleCacheResponse(x);
  endrule

  (* fire_when_enabled *)
  rule ccu_to_fetch_bpred;
      let x <- ccu.updateBranchPredictor();
      monitor.monitorBranchPredictor(x);
      fetch.updateBranchPredictor(x);
  endrule 

  (* fire_when_enabled *)
  rule ccu_to_fetch_PC;
      let x <- ccu.setPC();
      monitor.monitorSetPC(x);
      fetch.handleSetPC(x);
  endrule

  method Action start();
    onStart();
    monitor.start();
  endmethod
  
  method Action stop();
    onStop();
    monitor.stop();
  endmethod

endmodule


endpackage

