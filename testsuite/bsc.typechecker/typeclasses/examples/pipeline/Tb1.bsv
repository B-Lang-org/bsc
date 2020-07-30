import Pipeline1::*;

typedef UInt#(32) Word;
typedef Tuple2#(Word, Word) Pair;

module mkTb ();
    BuriedPipeline#(Pair, Word) mp = series(
        tuple2(
                mkNonDelayStage,
                mkNonDelayStage),
        mkFunctionStage(tpl_2, 0));

    Pipeline#(Pair, Word) p;
    PipelinePosition pp;
    {p, pp} <- exposePipeline(mp, 2000);
    Reg#(UInt#(32)) cycle <- mkReg(0);

    rule count;
        cycle <= cycle + 1;
        $display("Cycle %1d", cycle);
        if (cycle == 8)
            $finish(0);
    endrule

    rule stuff;
        p.enq(tuple2(0, cycle));
    endrule

    rule deq;
        p.deq;
    endrule

    rule first;
        $display(p.first);
    endrule
endmodule
