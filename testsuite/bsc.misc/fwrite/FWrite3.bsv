
String dumpFiled = "FWrite3d.dat.out";
String dumpFileb = "FWrite3b.dat.out";
String dumpFileo = "FWrite3o.dat.out";
String dumpFileh = "FWrite3h.dat.out";

(* synthesize *)
module sysFWrite3 () ;
   
   Reg#(int) cnt <- mkReg(0);
   let fhd <- mkReg(InvalidFile) ;
   let fhb <- mkReg(InvalidFile) ;
   let fho <- mkReg(InvalidFile) ;
   let fhh <- mkReg(InvalidFile) ;
   
   rule open (cnt == 0 ) ;
      $display("opening file" ) ;
      let lfhd <- $fopen(dumpFiled ) ;
      let lfhb <- $fopen(dumpFileb ) ;
      let lfho <- $fopen(dumpFileo ) ;
      let lfhh <- $fopen(dumpFileh ) ;
      cnt <= 1 ;
      fhd <= lfhd | stdout_mcd ;
      fhb <= lfhb | stdout_mcd ;
      fho <= lfho | stdout_mcd ;
      fhh <= lfhh | stdout_mcd ; 
   endrule
   
   rule dump (cnt > 0 );
      $display("writing to %s %0d", dumpFiled, cnt ) ;
      $fwrite  ( fhd , "%0d", cnt - 16 ); $fdisplay(fhd) ;
      $fwriteb ( fhb ,  cnt - 16 ); $fdisplay(fhb) ;
      $fwriteo ( fho ,  cnt - 16 ); $fdisplay(fho) ;
      $fwriteh ( fhh ,  cnt - 16 ); $fdisplay(fhh) ;
      cnt <= cnt + 1;
   endrule
   
   rule finish (cnt > 35);
      $finish(0);
   endrule
   
endmodule
