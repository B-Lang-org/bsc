module sysModuleTypeInFunction_MissingArg();
   function module makerule;
               return addRules(rules
                                  rule r;
                                     $display("hello");
                                  endrule
                               endrules);
   endfunction
   makerule;
endmodule

