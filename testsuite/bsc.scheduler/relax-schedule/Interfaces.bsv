package Interfaces;

import Vector::*;

/**************************************************/
/* Typedefs - Making things slightly more legible */
/*            since approximately... now.         */
/**************************************************/

typedef Vector#(n, Maybe#(a)) IBus#(type a, type n);

/**************************************************/
/* Interfaces                                     */
/**************************************************/

interface FXU #(type fuu_inst, type fuu_result, 
                type in_w, type out_w);

    //For CCU

    method Action handleIssue(IBus#(fuu_inst, in_w) data);
    method ActionValue#(IBus#(fuu_result, out_w)) complete();

    method Action flush();
endinterface: FXU

interface DCache #(type dcache_req, type dcache_resp, type in_w, type out_w);

    //For LoadStore

    method Action handleLSRequest(IBus#(dcache_req, in_w) data);
    method ActionValue#(IBus#(dcache_resp, out_w)) cacheResponse();

    method Action flush();
endinterface: DCache

interface LSU #(type dcache_resp, type dcache_req, 
                type lsu_inst, type lsu_res, type lsu_tag,
                //Bus widths
                type ccu_in_w, type ccu_out_w, type ccu_com_w, 
                type dcache_in_w, type dcache_out_w);

    //For DCache

    method Action handleCacheResponse(IBus#(dcache_resp, dcache_in_w) data);
    method ActionValue#(IBus#(dcache_req, dcache_out_w)) lsRequest();

    //For CCU

    method Action handleLSIssue(IBus#(lsu_inst, ccu_in_w) data);
    method ActionValue#(IBus#(lsu_res, ccu_out_w)) completeLS();
    method Action handleCommitStore(IBus#(lsu_tag, ccu_com_w) data);

    method Action flush();

endinterface: LSU

interface RegFile #(type reg_addr, type reg_data, type read_w, type write_w);

    //For CCU

    // XXX Convert back when Bug 247 is dead   
    method IBus#(reg_data, read_w)  readReg_Value(IBus#(reg_addr, read_w) data);
    method Action                  readReg_Action(IBus#(reg_addr, read_w) data);

    method Action writeReg(IBus#(Tuple2#(reg_addr, reg_data), write_w) data);

    method Action flush();
endinterface: RegFile

interface CCU#(type dec_inst, type inst_addr, type bpred_update, 
               type fuu_inst, type fuu_res, 
               type lsu_inst, type lsu_res, type lsu_tag,
               type dec_w, type fuu_in_w, type fuu_out_w,
               type lsu_in_w, type lsu_out_w, type lsu_com_w);

    //From Decode

    method Action handleDecode(IBus#(dec_inst, dec_w) data);

    //For Fetch

    method ActionValue#(inst_addr) setPC();

    //For Branch Predictor (Fetch)

    method ActionValue#(bpred_update) updateBranchPredictor();

    //For FXU

    method ActionValue#(IBus#(fuu_inst, fuu_out_w)) issue();
    method Action handleComplete(IBus#(fuu_res, fuu_in_w) data);

    //For LSU

    method ActionValue#(IBus#(lsu_inst, lsu_out_w)) issueLS();
    method Action handleLSComplete(IBus#(lsu_res, lsu_in_w) data); 
    method ActionValue#(IBus#(lsu_tag, lsu_com_w)) commitStore();

    method Action flush();
endinterface: CCU


interface Decode #(type dec_inst, type inst_bundle, type opcode, type deinfo, type in_w, type out_w);

    //For CCU

    method ActionValue#(IBus#(dec_inst, out_w)) result();

    //For Fetch

    method Action decode(IBus#(inst_bundle, in_w) data);

    method Action flush();

    //For decode table
    method Action handleDEResponse(deinfo data);

    method ActionValue#(opcode) deRequest ();

endinterface: Decode

interface Fetch #(type tbtrace_v, type tbtrace_bundle, type inst_bundle, type packed_inst, type inst_addr, type bpred_update,
                  type in_w, type out_w);

    //For Decode
    
    method ActionValue#(IBus#(tbtrace_bundle, out_w)) getInstructions();
    
    //For CCU
    
    method Action handleSetPC(inst_addr data);
    method Action updateBranchPredictor(bpred_update x);

    //From TBuffer
    method Action handleTBufferResponse(tbtrace_v x, Bool y);
    method ActionValue#(Bit#(1)) tBufferRequest();
    
    //For IBuffer
    
    method Action handleIBufferResponse(IBus#(Tuple2#(packed_inst, inst_addr), in_w) data);
    method ActionValue#(inst_addr) iBufferRequest();
    
    method Action flush();
endinterface: Fetch

interface IBuffer #(type inst_addr, type packed_inst, type in_w, type out_w);
 
    //For Fetch

    method Action handleIBufferRequest(inst_addr data);
    method ActionValue#(IBus#(Tuple2#(packed_inst, inst_addr), out_w)) iBufferResponse();
    method Action flushAddress(inst_addr x);
    
    //For ICache
    
    method ActionValue#(inst_addr) cacheRequest();
    method Action handleCacheResponse(Tuple2#(inst_addr, IBus#(packed_inst, in_w)) data);
    
    method Action flush();
endinterface: IBuffer

interface ICache #(type iaddress, type packed_inst, type out_w);

    //For IBuffer

    method Action handleCacheRequest(iaddress x);
    method ActionValue#(Tuple2#(iaddress, IBus#(packed_inst, out_w))) cacheResponse();

    method Action flush();
endinterface: ICache

endpackage: Interfaces

