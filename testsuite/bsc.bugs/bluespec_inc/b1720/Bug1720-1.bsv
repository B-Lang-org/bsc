import GetPut::*;
import ClientServer::*;
import FIFO::*;
import BRAM::*;
import Vector::*;

typedef TDiv#(TSub#(TAdd#(a,1),b), b) TDivF#(numeric type a, numeric type b);

typedef TSub#(a, TMul#(b, TDivF#(a,b))) TMod#(numeric type a, numeric type b);

typedef TMod#(TSub#(8, a), 8) TPadding#(numeric type a);

typedef struct {
    UInt#(TLog#(beamWidth)) parent;
    dataType data;
    UInt#(TPadding#(TAdd#(TLog#(beamWidth), SizeOf#(dataType)))) unused;
} BacktrackNode#(numeric type beamWidth, type dataType) deriving (Bits, Eq);

typedef Vector#(beamWidth, BacktrackNode#(beamWidth, dataType)) BacktrackBeam#(numeric type beamWidth, type dataType);

interface BacktrackRAM#(numeric type beamWidth,
                        numeric type numCodeSteps,
                        type dataType);
    interface Put#(BacktrackBeam#(beamWidth, dataType)) put;
    interface Get#(BacktrackNode#(beamWidth, dataType)) get;
    method Action request(UInt#(TLog#(numCodeSteps)) codeStep, UInt#(TLog#(beamWidth)) index);
endinterface: BacktrackRAM

/* Vectorization parameter
 *
 * Be sure to pick a power of two so that we can do division with shifts.
 * Also make beamwidth be divisible by N for sanity.
 */
typedef 1 N;

module mkBacktrackRAM(BacktrackRAM#(beamWidth, numCodeSteps, dataType))
    provisos (Bits#(dataType, dataBits),
              NumAlias#(TLog#(N), wordShift),
              NumAlias#(TLog#(beamWidth), beamWidthBits),
              NumAlias#(TLog#(numCodeSteps), codeStepBits),
              NumAlias#(TAdd#(beamWidthBits, codeStepBits), addressSize),
              NumAlias#(TSub#(addressSize, wordShift), wordAddressSize),
              Alias#(UInt#(beamWidthBits), beamIndexType),
              Alias#(UInt#(codeStepBits), codeStepType),
              Alias#(UInt#(addressSize), addressType),
              Alias#(UInt#(wordAddressSize), wordAddressType),
              Alias#(BacktrackNode#(beamWidth, dataType), nodeType),
              Alias#(BacktrackBeam#(beamWidth, dataType), beamType),
              Alias#(Vector#(N, nodeType), wordType),
              Add#(a__, wordShift, addressSize),
              Bits#(nodeType, nodeBits),
              Div#(TMul#(N, nodeBits), N, nodeBits)
             );

    BRAM_Configure cfg = defaultValue;
    cfg.allowWriteResponseBypass = False;
    BRAM2PortBE#(wordAddressType, wordType, N) ram <- mkBRAM2ServerBE(cfg);
    FIFO#(beamType) inFIFO <- mkFIFO;

    Reg#(beamIndexType) nextWriteIndex <- mkReg(0);
    Reg#(codeStepType) nextCodeStep <- mkReg(0);

    beamIndexType wrapIndex = truncate(UInt#(TAdd#(beamWidthBits, 1))'(fromInteger(valueOf(beamWidth))));

    Integer wordShift = valueOf(TLog#(N));

    FIFO#(UInt#(TLog#(N))) wordIndex <- mkFIFO;

    rule fillRAM;
        beamType beam = inFIFO.first;
        beamIndexType index = nextWriteIndex;
        codeStepType codeStep = nextCodeStep;
        wordType word = newVector;
        for (Integer i=0; i<valueOf(N); i=i+1)
            word[i] = beam[index + fromInteger(i)];
        addressType address = extend(index) + (extend(codeStep) << valueOf(beamWidthBits));
        wordAddressType wordAddress = truncate(address >> valueOf(wordShift));
        $display ("Filling 0x%1x", address);
        let req = BRAMRequestBE {
            writeen: '1,
            responseOnWrite: False,
            address: wordAddress,
            datain: word
        };
        ram.portA.request.put(req);
        if (index + fromInteger(valueOf(N)) == wrapIndex) begin
            index = 0;
            codeStep = codeStep + 1;
            inFIFO.deq;
        end else
            index = index + fromInteger(valueOf(N));
        nextWriteIndex <= index;
        nextCodeStep <= codeStep;
    endrule

    interface Put put = fifoToPut(inFIFO);
    interface Get get;
        method ActionValue#(nodeType) get();
            let v <- ram.portB.response.get();
            wordIndex.deq;
            return v[wordIndex.first];
        endmethod
    endinterface

    method Action request(UInt#(TLog#(numCodeSteps)) codeStep, UInt#(TLog#(beamWidth)) index);
        addressType address = extend(index) + (extend(codeStep) << valueOf(beamWidthBits));
        wordAddressType wordAddress = truncate(address >> valueOf(wordShift));
        let req = BRAMRequestBE {
            writeen: 0,
            responseOnWrite: False,
            address: wordAddress,
            datain: ?
        };
        ram.portB.request.put(req);
        wordIndex.enq(truncate(address));
    endmethod
endmodule

module mkTb ()
    provisos (NumAlias#(32, beamWidth),
              NumAlias#(3, dataBits),
              NumAlias#(8, numCodeSteps),
              Alias#(UInt#(dataBits), dataType));
    Reg#(UInt#(32)) cycle <- mkReg(0);
    Reg#(UInt#(32)) step <- mkReg(0);
    BacktrackRAM#(beamWidth, 8, dataType) backtrackRAM <- mkBacktrackRAM();
    Reg#(UInt#(32)) startCycle <- mkReg(0);
    Reg#(UInt#(TLog#(beamWidth))) followIndex <- mkDWire(0);

    rule stuff (step < fromInteger(valueOf(numCodeSteps)));
        $display ("Stuffing");
        BacktrackBeam#(beamWidth, dataType) v = newVector;
        for (Integer i=0; i<valueOf(beamWidth); i=i+1) begin
            v[i] = BacktrackNode {
                parent: fromInteger(i) + truncate(step)*13,
                data: fromInteger(i % valueOf(TExp#(dataBits)))
            };
        end
        backtrackRAM.put.put(v);
        step <= step + 1;
    endrule

    rule unstuff (step >= fromInteger(valueOf(numCodeSteps)));
        let start = startCycle;
        if (start == 0)
            start = cycle + 2*fromInteger(valueOf(beamWidth));
        if (cycle >= start && cycle < start + fromInteger(valueOf(numCodeSteps))) begin
            UInt#(TLog#(numCodeSteps)) codeStep = truncate(fromInteger(valueOf(numCodeSteps))-1 - (cycle-start));
            let index = followIndex;
            backtrackRAM.request(codeStep, index);
            $display ("Requesting step %2d, index %1d", codeStep, index);
        end
        startCycle <= start;
    endrule

    rule getresult;
        let r <- backtrackRAM.get.get();
        $display ("Got back BactrackNode {parent: %2d, tag: %1x}", r.parent, r.data);
        followIndex <= r.parent;
    endrule

    rule count;
        cycle <= cycle + 1;
        $display ("cycle %1d", cycle);
        if (cycle == 300)
            $finish(0);
    endrule: count
endmodule: mkTb
