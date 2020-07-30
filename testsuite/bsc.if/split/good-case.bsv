(* synthesize *)
module sysx () ;
  Reg#(Maybe#(Bool)) myregister <- mkRegU();
  rule foobar;
       (*split*)
       case (myregister) matches
          tagged Valid .x : if (x) $display("True"); else $display("False");
          tagged Invalid : $display ("Invalid");
       endcase
  endrule
endmodule
