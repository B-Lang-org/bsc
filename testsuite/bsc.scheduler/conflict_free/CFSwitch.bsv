// test that ports are tied to uses correctly with RegFile

import RegFile::*;
import Vector::*;
import FIFO::*;
import StmtFSM::*;

typedef Tuple2#(Tag, Bit#(16)) Packet;

typedef Bit#(4) Tag;
Integer numTags = valueOf(TExp#(SizeOf#(Tag)));

typedef 5 NumInChans;
Integer numInChans = valueOf(NumInChans);

typedef UInt#(3) OutAddr;

typedef 8 NumOutChans;
Integer numOutChans = valueOf(NumOutChans);

(* options ="-aggressive-conditions" *)
(* synthesize *)
module sysCFSwitch();

  Reg#(UInt#(32)) cycle <- mkReg(0);
  
  rule count_cycles;
    cycle <= cycle + 1;
  endrule  
  
  RegFile#(Tag, OutAddr) chanMap <- mkRegFileFull;

  Reg#(Bool) mapReady <- mkReg(False);

  OutAddr routes[numTags] = {0,7,5,6,2,
                             1,2,3,4,5,
                             6,7,0,7,0,
                             7};
 
  Vector#(NumOutChans, Reg#(Bool)) drainOut = ?;
  Vector#(NumOutChans, FIFO#(Packet)) outs  = ?;

  for(Integer i = 0; i < numOutChans; i = i + 1)
  begin
    outs[i] <- mkFIFO;
    drainOut[i] <- mkReg(True);
    rule drain_output(drainOut[i]);
       let tag  = tpl_1(outs[i].first);
       let data = tpl_2(outs[i].first);
       $display("Receiving packet (%h,%h) on output %0d at cycle %0d", tag, data, i, cycle);
       outs[i].deq;
    endrule
  end

  Vector#(NumInChans, FIFO#(Packet)) ins <- replicateM(mkFIFO);
  for(Integer i = 0; i < numInChans; i = i + 1)
  begin
    ins[i] <- mkFIFO;
  end

  function Action sendPacket(Integer chan, Tag tag, Bit#(16) data);
  action
     $display("Sending packet (%h,%h) on input %0d at cycle %0d", tag, data, chan, cycle);
     ins[chan].enq(tuple2(tag,data));
  endaction
  endfunction

  Rules r = emptyRules;

  for(Integer i = 0; i < numInChans; i = i + 1)
  begin
    Rules newRule =
    	        rules 
                 rule route_in(mapReady);
                    let guid = tpl_1(ins[i].first);
                    OutAddr dest = chanMap.sub(guid);
                    outs[dest].enq(ins[i].first);
                    ins[i].deq;
                    $display("Routing packet (%h,%h) from input %0d to output %0d at cycle %0d",
		             guid, tpl_2(ins[i].first), i, dest, cycle);
                 endrule
                endrules;
     r = rJoinConflictFree(newRule, r);
  end

  addRules(r);
 
    
  Stmt testStmts = 
  seq

    // initialize channel map
    chanMap.upd(0, routes[0]);
    chanMap.upd(1, routes[1]);
    chanMap.upd(2, routes[2]);
    chanMap.upd(3, routes[3]);
    chanMap.upd(4, routes[4]);
    chanMap.upd(5, routes[5]);
    chanMap.upd(6, routes[6]);
    chanMap.upd(7, routes[7]);
    chanMap.upd(8, routes[8]);
    chanMap.upd(9, routes[9]);
    chanMap.upd(10, routes[10]);
    chanMap.upd(11, routes[11]);
    chanMap.upd(12, routes[12]);
    chanMap.upd(13, routes[13]);
    chanMap.upd(14, routes[14]);
    chanMap.upd(15, routes[15]);
    mapReady <= True;
 
    // no conflict
    action
      sendPacket(0,0,16'hdead);
      sendPacket(1,1,16'hbeef);
      sendPacket(2,2,16'hbaad);
      sendPacket(3,3,16'hf00d);
      sendPacket(4,4,16'hc01d);
    endaction

    // no conflict
    action
      sendPacket(0,5,16'hdead);
      sendPacket(1,6,16'hbeef);
      sendPacket(2,7,16'hbaad);
      sendPacket(3,8,16'hf00d);
      sendPacket(4,9,16'hc01d);
    endaction

    // two conflict pairs
    action
      sendPacket(0,'ha,16'hdead);
      sendPacket(1,'hb,16'hbeef);
      sendPacket(2,'hc,16'hbaad);
      sendPacket(3,'hd,16'hf00d);
      sendPacket(4,'he,16'hc01d);
    endaction

    // maximum conflict #1
    action		
      sendPacket(0,'hf,16'hdead);
      sendPacket(1,'hf,16'hbeef);
      sendPacket(2,'hf,16'hbaad);
      sendPacket(3,'hf,16'hf00d);
      sendPacket(4,'hf,16'hc01d);
    endaction

    // maximum conflict #2
    action		
      sendPacket(0,'hf,16'hdead);
      sendPacket(1,'hf,16'hbeef);
      sendPacket(2,'hf,16'hbaad);
      sendPacket(3,'hf,16'hf00d);
      sendPacket(4,'hf,16'hc01d);
    endaction

    action
      $display("Turning off output 7 at cycle %0d", cycle);
      drainOut[7] <= False;
    endaction
    
    noAction;
    noAction;

    // prove that -aggressive-conditions works with this
    par
      seq
        sendPacket(0,5,16'hdead);
        sendPacket(1,6,16'hbeef);
        sendPacket(2,7,16'hbaad);
        sendPacket(3,8,16'hf00d);
        sendPacket(4,9,16'hc01d);

        action
          $display("Turning on output 7 at cycle %0d", cycle); 
          drainOut[7] <= True;
        endaction

        noAction;
        noAction;
        noAction;
        noAction;
        noAction;

      endseq
       seq 
        sendPacket(0,'hf,16'hdead);
        sendPacket(1,'hb,16'hbeef);
        sendPacket(0,'hf,16'hbaad);
        sendPacket(0,'hd,16'hf00d);
      endseq

    endpar
    endseq;

    mkAutoFSM(testStmts);

endmodule

