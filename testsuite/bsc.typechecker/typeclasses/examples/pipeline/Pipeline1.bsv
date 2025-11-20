
import Vector::*;
import List::*;
import FIFOF::*;
import SpecialFIFOs::*;
import ModuleContext::*;

typeclass LE#(numeric type a, numeric type b);
endtypeclass

instance LE#(a,b) provisos (Add#(a,c,b));
endinstance

typedef struct {
    Integer costAccumulated;    // number of cost units since last register
    Integer costPerCycleLimit;  // number of cost units allowed per cycle
    Integer costAllBranches;    // number of cost units over all branches
    Integer delay;              // number of registers in pipeline
} PipelinePosition;

// Computes the pipeline position of a parallel combination of c1 and c2,
// given that they were each instantiated starting at position c.
function PipelinePosition combineParallelPositions(PipelinePosition c, PipelinePosition c1, PipelinePosition c2);
    if (c1.delay != c2.delay)
        return error("Pipelines of different delay combined in parallel.");
    else
    return PipelinePosition {
        costAccumulated: max(c1.costAccumulated, c2.costAccumulated),
        costPerCycleLimit: c.costPerCycleLimit,
        costAllBranches: c1.costAllBranches + c2.costAllBranches - c.costAllBranches,
        delay: c1.delay
    };
endfunction

typedef ModuleContext#(PipelinePosition) ModulePipeline;

typedef ModulePipeline#(Pipeline#(a, b)) BuriedPipeline#(type a, type b);

interface Pipeline#(type a, type b);
    method Action enq(a x);
    method Action deq;
    method b first;
    method Action clear;
    method Bool notFull;
    method Bool notEmpty;
endinterface

function Action pEnq     (Pipeline#(a, b) x, a ax) = x.enq(ax);
function Action pDeq     (Pipeline#(a, b) x)       = x.deq;
function b      pFirst   (Pipeline#(a, b) x)       = x.first;
function Action pClear   (Pipeline#(a, b) x)       = x.clear;
function Bool   pNotFull (Pipeline#(a, b) x)       = x.notFull;
function Bool   pNotEmpty(Pipeline#(a, b) x)       = x.notEmpty;

module [ModulePipeline] mkFunctionStageCondition#(function b f(a ax), Bool canProceed, Integer cost) (Pipeline#(a, b))
    provisos (Bits#(a, sa), Bits#(b, sb));

    PipelinePosition c <- getContext;
    c.costAccumulated = c.costAccumulated + cost;
    c.costAllBranches = c.costAllBranches + cost;

    if (cost > c.costPerCycleLimit)
        warningM("Impossible pipeline cost constraint.");

    Pipeline#(a, b) ifc;

    if (c.costAccumulated <= c.costPerCycleLimit) begin
        PulseWire deqw <- mkPulseWire;
        RWire#(b) w <- mkRWire;

        if (valueOf(sa) == 0)
            messageM("mkRWire instantiated with bit size 0");

        ifc = interface Pipeline
            method enq(ax) if (deqw) = w.wset(f(ax));
            method deq if (canProceed) = deqw.send;
            method first if (w.wget matches tagged Valid .x) = x;
            method clear = noAction;
            method notFull = deqw;
            method notEmpty = isValid(w.wget);
        endinterface;
    end else begin
        FIFOF#(a) fifof <- mkPipelineFIFOF;

        if (valueOf(sa) == 0)
            messageM("mkPipelineFIFOF instantiated with bit size 0");

        ifc = interface Pipeline
            method enq(ax) = fifof.enq(ax);
            method deq if (canProceed) = fifof.deq;
            method first if (canProceed) = f(fifof.first);
            method clear = fifof.clear;
            method notFull = fifof.notFull;
            method notEmpty = fifof.notEmpty && canProceed;
        endinterface;

        c.costAccumulated = cost;
        c.delay = c.delay + 1;
    end
    putContext(c);

    return ifc;
endmodule

module [ModulePipeline] mkFunctionStage#(function b f(a ax), Integer cost) (Pipeline#(a, b))
    provisos (Bits#(a, sa), Bits#(b, sb));
    let ifc <- mkFunctionStageCondition(f, True, cost);
    return ifc;
endmodule

module [ModulePipeline] mkNonDelayStage (Pipeline#(a, a))
    provisos (Bits#(a, sa));
    let p <- mkFunctionStage(id, 0);
    return p;
endmodule

module [ModulePipeline] mkDelayStage (Pipeline#(a, a))
    provisos (Bits#(a, sa));

    PipelinePosition c <- getContext;
    c.costAccumulated = 0;
    c.delay = c.delay + 1;
    putContext(c);

    FIFOF#(a) fifof <- mkPipelineFIFOF;

    if (valueOf(sa) == 0)
        messageM("mkPipelineFIFOF instantiated with bit size 0");

    method enq(ax) = fifof.enq(ax);
    method deq = fifof.deq;
    method first = fifof.first;
    method clear = fifof.clear;
    method notFull = fifof.notFull;
    method notEmpty = fifof.notEmpty;
endmodule

module [ModulePipeline] mkSeriesPipeline2#(
        BuriedPipeline#(a, b) mp1,
        BuriedPipeline#(b, c) mp2)
        (Pipeline#(a, c));
    let p1 <- mp1;
    let p2 <- mp2;

    rule passPermission (p2.notFull);
        p1.deq;
    endrule

    rule shovelData (p1.notEmpty && p2.notFull);
        p2.enq(p1.first);
    endrule

    method enq(ax) = p1.enq(ax);
    method deq = p2.deq;
    method first = p2.first;
    method clear = action p1.clear; p2.clear; endaction;
    method notFull = p1.notFull;
    method notEmpty = p2.notEmpty;
endmodule

module [ModulePipeline] mkSeriesPipeline3#(
        BuriedPipeline#(a, b) mp1,
        BuriedPipeline#(b, c) mp2,
        BuriedPipeline#(c, d) mp3)
        (Pipeline#(a, d));
    let p <- mkSeriesPipeline2(mkSeriesPipeline2(mp1, mp2), mp3);
    return p;
endmodule

module [ModulePipeline] mkDelayedPipeline#(
        BuriedPipeline#(a, b) mp,
        Integer delay)
        (Pipeline#(a, b))
    provisos (Bits#(b, sb));
    let p <- List::foldl(mkSeriesPipeline2, mp, List::replicate(delay, mkDelayStage));
    return p;
endmodule

module [m] mkIfc#(ifc i) (ifc) provisos (IsModule#(m, a));
    return i;
endmodule

module [ModulePipeline] mkFixedDelayPipeline#(
        BuriedPipeline#(a, b) mp,
        Integer delay)
        (Pipeline#(a, b))
    provisos (Bits#(b, sb));

    PipelinePosition c <- getContext;
    Pipeline#(a, b) p;
    {p, c} <- unburyPipeline(mp, c);

    let extraDelay = delay-c.delay;
    if (extraDelay < 0)
        errorM("Cannot meet delay goal (actual=" + integerToString(c.delay) + ", target=" + integerToString(delay) + ").");

    if (delay > 0) {p, c} <- unburyPipeline(mkDelayedPipeline(mkIfc(p), extraDelay), c);

    putContext(c);

    return p;
endmodule

module [ModulePipeline] mkParallelPipelineTuple#(
        BuriedPipeline#(a, b) mp1,
        BuriedPipeline#(c, d) mp2)
        (Pipeline#(Tuple2#(a, c), Tuple2#(b, d)))
    provisos (Bits#(b, sb),
              Bits#(d, sd));
    PipelinePosition c <- getContext;
    Integer initialCost = c.costAllBranches;

    // build both pipelines
    let {p1, c1} <- unburyPipeline(mp1, c);
    let {p2, c2} <- unburyPipeline(mp2, c);
    Integer delay = max(c1.delay, c2.delay);

    let delay1 = delay-c1.delay;
    let delay2 = delay-c2.delay;

    // add delay adjustment to shorter pipeline
    if (delay1 > 0) {p1, c1} <- unburyPipeline(mkDelayedPipeline(mkIfc(p1), delay1), c1);
    if (delay2 > 0) {p2, c2} <- unburyPipeline(mkDelayedPipeline(mkIfc(p2), delay2), c2);
    if (c1.delay != delay) errorM("Error delaying pipeline branch 1");
    if (c2.delay != delay) errorM("Error delaying pipeline branch 2");
    putContext(combineParallelPositions(c, c1, c2));

    method enq(x)   = action p1.enq(tpl_1(x)); p2.enq(tpl_2(x)); endaction;
    method deq      = action p1.deq; p2.deq; endaction;
    method first    = tuple2(p1.first, p2.first);
    method clear    = action p1.clear; p2.clear; endaction;
    method notFull  = p1.notFull && p2.notFull;
    method notEmpty = p1.notEmpty && p2.notEmpty;
endmodule

// when parallel components are identical
module [ModulePipeline] mkParallelPipelineVector#(
        BuriedPipeline#(a, b) mp)
        (Pipeline#(Vector#(n, a), Vector#(n, b)))
    provisos (Bits#(b, sb), LE#(1, n));
    PipelinePosition c <- getContext;

    let tp <- replicateM(unburyPipeline(mp, c));
    let {p, cn} = unzip(tp);
    putContext(foldl1(combineParallelPositions(c), cn));

    method enq(va)  = zipWithM_(pEnq, p, va);
    method deq      = mapM_(pDeq, p);
    method first    = map(pFirst, p);
    method clear    = mapM_(pClear, p);
    method notFull  = all(pNotFull, p);
    method notEmpty = all(pNotEmpty, p);
endmodule

typeclass FoldPipeline#(numeric type n, type a);
    module [ModulePipeline] mkFoldPipeline#(function a f(a x, a y), Integer cost)
            (Pipeline#(Vector#(n, a), a));
endtypeclass

instance FoldPipeline#(1, a)
    provisos (Bits#(a, sa));
    module [ModulePipeline] mkFoldPipeline#(function a f(a x, a y), Integer cost)
            (Pipeline#(Vector#(1, a), a));
        let ifc <- mkFunctionStage(head, 0);
        return ifc;
    endmodule
endinstance

instance FoldPipeline#(n, a)
    provisos (LE#(1, n), FoldPipeline#(TDiv#(n, 2), a), Bits#(a, sa));
    module [ModulePipeline] mkFoldPipeline#(function a f(a x, a y), Integer cost)
            (Pipeline#(Vector#(n, a), a));
        let head = mkFunctionStage(mapPairs(f, id), cost);
        let tail = mkFoldPipeline(f, cost);
        let ifc <- mkSeriesPipeline2(head, tail);
        return ifc;
    endmodule
endinstance

typeclass CoercePipeline#(type a, type b, type c)
    dependencies (c determines (a, b));
    function BuriedPipeline#(a, b) toPipeline(c x);
endtypeclass

instance CoercePipeline#(a, b, BuriedPipeline#(a, b));
    function toPipeline = id;
endinstance

typedef struct {
    t value;
} NoteVector#(type t);

function NoteVector#(t) vector(t value) = NoteVector { value:value };

instance CoercePipeline#(Vector#(n, a), Vector#(n, b), NoteVector#(BuriedPipeline#(a, b)))
    provisos (Bits#(a, sa), Bits#(b, sb), LE#(1, n));
    function toPipeline(x) = mkParallelPipelineVector(x.value);
endinstance

instance CoercePipeline#(Tuple2#(a, c), Tuple2#(b, d), Tuple2#(BuriedPipeline#(a, b), BuriedPipeline#(c, d)))
    provisos (Bits#(a, sa), Bits#(b, sb), Bits#(c, sc), Bits#(d, sd));
    function toPipeline(x) = mkParallelPipelineTuple(tpl_1(x), tpl_2(x));
endinstance

typeclass SeriesPipeline#(type t, type s)
    dependencies (t determines s);
    function t series(s head);
endtypeclass

// base case
instance SeriesPipeline#(BuriedPipeline#(a, b), BuriedPipeline#(a, b));
    function series(h) = h;
endinstance

// accept arguments
instance SeriesPipeline#(function r f_(d tail_), BuriedPipeline#(a, b))
    provisos (SeriesPipeline#(r, BuriedPipeline#(a, c)), CoercePipeline#(b, c, d));
    function series(head);
        function f(tail) = series(mkSeriesPipeline2(head, toPipeline(tail)));
        return f;
    endfunction
endinstance

// coerce any that that are not pipelines
instance SeriesPipeline#(t, c)
    provisos (SeriesPipeline#(t, BuriedPipeline#(a,b)),
              CoercePipeline#(a, b, c));
    function series(head);
       BuriedPipeline#(a,b) p = toPipeline(head);
       return series(p);
    endfunction
endinstance

module [m] unburyPipeline#(
        BuriedPipeline#(a, b) mp,
        PipelinePosition initialPosition)
        (Tuple2#(Pipeline#(a, b), PipelinePosition))
        provisos (IsModule#(m, i));
    let {c,p} <- liftModule(runWithCompleteContext(initialPosition, mp));
    return tuple2(p, c);
endmodule

module [m] exposePipeline#(
        BuriedPipeline#(a, b) mp,
        Integer costLimit)
        (Tuple2#(Pipeline#(a, b), PipelinePosition))
        provisos (IsModule#(m, i));
    let t <- unburyPipeline(mp, PipelinePosition {
        costAccumulated: 0,
        costPerCycleLimit: costLimit,
        costAllBranches: 0,
        delay: 0
    });
    return t;
endmodule

module [m] exposeRegisteredPipeline#(
        BuriedPipeline#(a, b) mp,
        Integer costLimit)
        (Tuple2#(Pipeline#(a, b), PipelinePosition))
        provisos (IsModule#(m, i), Bits#(b, sb));
    let t <- exposePipeline(mkSeriesPipeline2(mp, mkDelayStage), costLimit);
    return t;
endmodule

module [m] exposeFixedDelayPipeline#(
        BuriedPipeline#(a, b) mp,
        Integer costLimit, Integer delay)
        (Tuple2#(Pipeline#(a, b), PipelinePosition))
        provisos (IsModule#(m, i), Bits#(b, sb));
    let t <- unburyPipeline(mkFixedDelayPipeline(mp, delay), PipelinePosition {
        costAccumulated: 0,
        costPerCycleLimit: costLimit,
        costAllBranches: 0,
        delay: 0
    });
    return t;
endmodule
