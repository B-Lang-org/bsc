(* synthesize *)
module sysHello();
    rule hello;
        $display("hello world");
        $finish(0);
    endrule
endmodule
