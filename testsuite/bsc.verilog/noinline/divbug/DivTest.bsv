import Div::*; 

(* synthesize *)
module sysDivTest();

rule once(True);
    DWord x=14;
    DWord d=-3;

    /*Tuple2#(DWord,DWord)*/ DivResult res = divide(x,d,True);
    DWord q = res.quo; //tpl_1(res);
    DWord r = res.rem; //tpl_2(res);

    // note that failure is expected here
    // since we mostly care that the noinline doesn't blow up
    if (q == x/d && r == x-d*q)
        $display("PASSED with q=%h and r=%h",q,r);
    else
        $display("FAILED with q=%h instead of %h and r=%h instead of %h",q,x/d,r,x-d*q);
    $finish(0);
endrule

endmodule

