import FIFOF::*;
	      
Module#(Lookup) sysLookupU;
sysLookupU = mkLookup;
		      
typedef  Bit#(32) Address;
			  
typedef  Bit#(32) Entry;
			
typedef union tagged {
    void Start;
    void Step1;
    void Step2;
    void Step3;
} Step deriving (Eq, Bits);
			   
function Bit#(16) bh(Address x);
return (x[31:16]);
endfunction: bh
	       
function Bit#(16) bl(Address x);
return (x[15:0]);
endfunction: bl
	       
function Bit#(28) pntr(Entry x);
return (x[31:4]);
endfunction: pntr
		 
function Bit#(4) offset(Entry x);
return (x[3:0]);
endfunction: offset
		   
function Bit#(8) nextHop(Address x);
return (x[11:4]);
endfunction: nextHop
		    
function Address cwloc(Address addr, Entry entry);
        Bit#(32) pointer;
	pointer = zeroExtend(pntr(entry));
	Bit#(16) q;
	q = selectBits16(offset(entry), bl(addr));
	Bit#(32) s;
	s = {20'b0, q[15:4]};
	cwloc = pointer + s;
endfunction: cwloc
		  
function Nat countBits16(Bit#(16) bs);
return (countBits(0, 16, bs));
endfunction: countBits16
			
function Nat countBits(Integer l, Integer h, Bit#(n) bs);
    Nat ret;
    if (h == l + 1)
       ret = {0,bs[fromInteger(l)]};
    else
       begin
           Integer m = h + l % 2;
           ret = countBits(l,m,bs) + countBits(m,h,bs);
       end
    return ret;
endfunction: countBits
		      
function Bit#(16) selectBits16(Bit#(4) n, Bit#(16) bs);
return (selectBits(0, 15, n, bs));
endfunction: selectBits16
			 
function Bit#(m) selectBits(Integer l, Integer h, Bit#(n) n, Bit#(m) bs);
return (l <= h ?
	    n == fromInteger(h - l) ? bs[fromInteger(h):fromInteger(l)] : selectBits(l + 1, h, n, bs)
	:   0);
endfunction: selectBits
		       
function Bit#(32) compCNHAIndex(Address addr, Entry e1, Entry e2);
        Bit#(16) q;
	Bit#(4) w;
	Bit#(32) wbars;
	Bit#(32) t;
	q = selectBits16(offset(e1), bl(addr));
	w = q[3:0];
	wbars = countBits16(selectBits16(w, bh(e2)));
	t = zeroExtend(bl(e2)) + wbars - 1;
	compCNHAIndex = t;
endfunction: compCNHAIndex
			  
function Address compCNHALoc(Address addr, Entry e1, Bit#(32) index);
        Bit#(32) pointer;
	Nat offsetlen;
	pointer = zeroExtend(pntr(e1));
	offsetlen = zeroExtend(offset(e1));
	compCNHALoc = pointer + 1 << offsetlen - 3 + index >> 2;
endfunction: compCNHALoc
			
function Bit#(8) selectEntry(Bit#(2) index, Entry entries);
        selectEntry = (entries << Bit#(32)'(zeroExtend(index)) << 3)[31:24];
endfunction: selectEntry
			
interface Lookup;
    method FIFOF#(Address) dar;
    method FIFOF#(Bit#(8)) drr;
    method FIFOF#(Address) sri;
    method FIFOF#(Entry) sro;
endinterface: Lookup
		    
module mkLookup(Lookup);
  FIFOF#(Address) darS();
  mkFIFOF the_darS(darS);
  FIFOF#(Bit#(8)) drrS();
  mkFIFOF the_drrS(drrS);
  FIFOF#(Address) sriS();
  mkFIFOF the_sriS(sriS);
  FIFOF#(Entry) sroS();
  mkFIFOF the_sroS(sroS);
  Reg#(Step) lstate();
  mkReg#(Start) the_lstate(lstate);
  Reg#(Entry) entry1();
  mkRegU the_entry1(entry1);
  Reg#((Bit#(2))) index();
  mkRegU the_index(index);
  addRules(mkLookupRules(darS, drrS, sriS, sroS, lstate, entry1, index));
  method dar(); dar = darS;
  endmethod: dar
  method drr(); drr = drrS;
  endmethod: drr
  method sri(); sri = sriS;
  endmethod: sri
  method sro(); sro = sroS;
  endmethod: sro
  
endmodule: mkLookup
		   
function Rules mkLookupRules(FIFOF#(Address) dar,
			     FIFOF#((Bit#(8))) drr,
			     FIFOF#(Address) sri,
			     FIFOF#(Entry) sro,
			     Reg#(Step) lstate,
			     Reg#(Entry) entry1,
			     Reg#((Bit#(2))) index);
return (rules
	rule r1 (lstate == Start &&  dar.notEmpty &&  sri.notFull);
	    sri.enq(zeroExtend(bh(dar.first))); lstate <= Step1;
	endrule
	rule r2 (lstate == Step1 &&  pntr(sro.first) <= 255 &&  dar.notEmpty &&  drr.notFull &&  sro.notEmpty);
	    drr.enq(zeroExtend(nextHop(sro.first))); dar.deq; sro.deq; lstate <= Start;
	endrule
	rule r3 (lstate == Step1 &&  pntr(sro.first) > 255 &&  dar.notEmpty &&  sri.notFull &&  sro.notEmpty);
	    entry1 <= sro.first; sro.deq; sri.enq(cwloc(dar.first, sro.first)); lstate <= Step2;
	endrule
	rule r4 (lstate == Step2 &&  sro.notEmpty &&  offset(entry1) < 3 &&  dar.notEmpty &&  drr.notFull);
	    drr.enq(sro.first[7:0]); sro.deq; lstate <= Start;
	endrule
	rule r5 (lstate == Step2 &&  sro.notEmpty &&  offset(entry1) >= 3 &&  dar.notEmpty &&  sri.notFull);
	    Bit#(32) t;
	    t = compCNHAIndex(dar.first, entry1, sro.first);
	      sri.enq(compCNHALoc(dar.first, entry1, t)); sro.deq; dar.deq; index <= t[1:0]; lstate <= Step3;
	endrule
	rule r6 (lstate == Step3 &&  sro.notEmpty &&  drr.notFull);
	    drr.enq(selectEntry(index, sro.first)); sro.deq; lstate <= Start;
	endrule
	
	endrules);
endfunction: mkLookupRules
