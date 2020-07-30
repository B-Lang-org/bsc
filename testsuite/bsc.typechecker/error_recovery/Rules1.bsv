module sysRules1();
   // this one is a XFAIL (although not marked as such in
   // our DejaGNU script), because there ought to be two
   // errors, but currently we give up after just one.
   addRules(False);
   addRules(True);
endmodule
