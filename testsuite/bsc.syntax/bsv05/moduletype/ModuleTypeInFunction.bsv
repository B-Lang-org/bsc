module sysModuleTypeInFunction();
   function module#(Empty) makerule;
               return addRules(rules
                                  rule r;
                                     $display("hello");
                                  endrule
                               endrules);
   endfunction
   makerule;
endmodule

