import Push::*;

import GetPut::*;

import ClientServer::*;

import LFSR::*;


// ========================================

typedef Server#(Tuple2 #(UInt#(n), UInt#(TLog#(n))), UInt#(n)) Shifter #(type n);

module mkShifter64(Shifter#(64));
  Tuple2 #(Get#(UInt#(64)), Put#(UInt#(64))) getR_putR();
  mkGPFIFO the_GPFIFO (getR_putR);

  Put#(UInt#(64)) putResult = tpl_2(getR_putR);
  Get#(UInt#(64)) getResult = tpl_1(getR_putR);
    
  Push#(Tuple2 #(UInt#(64), UInt#(6))) shifter;
  shifter <- pipe(passed(shift1),
	     pipe(passed(shift1),
	     pipe(qbuffer,
	     pipe(passed(shift1),
	     pipe(passed(shift1),
	     pipe(qbuffer,
	     pipe(passed(shift1),
	     pipe(passed(shift1),
	     pipe(passed(strip),
             pipe(compose(pass, tee(putResult.put)),
             sink))))))))));

  method request();
    return (interface Put;
	      method put(valby); return ((shifter.push)(valby));
	      endmethod: put
	    endinterface: Put);
  endmethod: request

  method response(); return (getResult);
  endmethod: response

endmodule: mkShifter64

function Tuple2 #(UInt#(n), UInt#(mm)) shift1(Tuple2 #(UInt#(n), UInt#(m)) valby)
  provisos (Add#(1, mm, m));
    UInt#(n) val = tpl_1(valby);
    UInt#(m) by = tpl_2(valby);

    Nat i =  fromInteger(valueOf(mm));
    Bool shift =  (pack(by))[i:i] == 1;
    UInt#(n) val2 =  shift ? val << (1 << i) : val;
    UInt#(mm) by2 =  truncate(by);

    return (tuple2(val2 , by2));
endfunction: shift1

function UInt#(n) strip(Tuple2 #(UInt#(n), UInt#(0)) x_b);
  return (tpl_1(x_b));
endfunction: strip


// ========================================

(* synthesize *)
module sysTestShifter64(Empty);
  Shifter#(64) shifter();
  mkShifter64 the_shifter(shifter);

  Tuple2 #(Get#(UInt#(64)), Put#(UInt#(64))) gExPEx <- mkGPSizedFIFO(10);
  Get#(UInt#(64)) getExpected = tpl_1(gExPEx);
  Put#(UInt#(64)) putExpected = tpl_2(gExPEx);

  Get#(Tuple2 #(UInt#(64), UInt#(6))) randoms();
  mkRandoms the_randoms(randoms);

  Reg#(UInt#(32)) count();
  mkReg#(0) the_count(count);

  rule requestHandler
   (True);
      Tuple2 #(UInt#(64), UInt#(6)) valby <- randoms.get;
      (shifter.request.put)(valby);
      (putExpected.put)(tpl_1(valby) << (pack(UInt#(6)'(tpl_2(valby)))));
  endrule

  rule responseHandler
   (count < 100);
     action
      UInt#(64) result <- shifter.response.get;
      UInt#(64) expected <- getExpected.get;
      if (result == expected) $display("Test %0d:   PASSED\n", pack(count)) ;
                         else $display("Test %0d:   FAILED\n", pack(count));
      count <= (count + 1);
     endaction
  endrule

  rule endTest
   (count >= 100);
     action
      $finish(0);
     endaction
  endrule
endmodule: sysTestShifter64


module mkRandoms(Get#(Tuple2 #(UInt#(64), UInt#(6))));
  LFSR#(Bit#(6)) lfsr6();
  mkFeedLFSR#('h20) the_lfsr6(lfsr6);

  LFSR#(Bit#(64)) lfsr64();
  mkFeedLFSR#('hDEADBEEFBADF00D) the_lfsr64(lfsr64);

  method get();
    actionvalue
      lfsr6.next;
      lfsr64.next;
      return(tuple2(unpack(lfsr64.value) , unpack(lfsr6.value)));
    endactionvalue
  endmethod: get
endmodule: mkRandoms


