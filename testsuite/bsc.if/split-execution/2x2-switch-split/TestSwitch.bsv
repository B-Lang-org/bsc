import Switch :: *;
import Vector :: *;

(*synthesize*)
module sysTestSwitch(Empty);
  Vector#(4,Reg#(Bool)) e <- replicateM(mkReg(False));
  Vector#(2,Reg#(Bool)) d <- replicateM(mkReg(False));
  Switch_IFC#(int) box <- switch();

  //first two conflict input ports
  rule enq0 (!e[0]);
     box.put0(Out_0,101);
     e[0]<=True;
  endrule

  rule enq1 (!e[1]);
     box.put0(Out_1,202);
     e[1]<=True;
  endrule

  //these next two should sail right through
  rule enq2 (e[0] && e[1] && !e[2]);
     box.put0(Out_0,303);
     e[2]<=True;
  endrule

  rule enq3 (e[0] && e[1] && !e[3]);
     box.put1(Out_1,404);
     e[3]<=True;
  endrule


  rule deq0 (!d[0]);
     let a<-box.get0();
     let b<-box.get1();
     $display("a=",a);
     $display("b=",b);
     d[0] <= True;
  endrule

  rule deq1 (d[0] && !d[1]);
     let a<-box.get0();
     let b<-box.get1();
     $display("c=",a);
     $display("d=",b);
     d[1] <= True;
  endrule
  
  rule all_done (d[1]);
    $finish(0);
  endrule
endmodule
