import CRC::*;
import StmtFSM::*;

(* synthesize *)
module sysCRCTest1();
   CRC#(16) crc_ccitt     <- mkCRC_CCITT;
   CRC#(16) crc_16        <- mkCRC16;
   CRC#(32) crc_32        <- mkCRC32;
   CRC#(16) crc_16_dnp    <- mkCRC('h3D65, 'h0000, 'hFFFF, True, True);
   CRC#(8)  crc_8         <- mkCRC('h07, 'h00, 'h00, False, False);
      
   Stmt test =
   seq
      delay(10);
      crc_ccitt.add('h31);
      crc_ccitt.add('h32);
      crc_ccitt.add('h33);
      crc_ccitt.add('h34);
      crc_ccitt.add('h35);
      crc_ccitt.add('h36);
      crc_ccitt.add('h37);
      crc_ccitt.add('h38);
      crc_ccitt.add('h39);
      $display("CRC-CCITT = %X", crc_ccitt.result());
      crc_16.add('h31);
      crc_16.add('h32);
      crc_16.add('h33);
      crc_16.add('h34);
      crc_16.add('h35);
      crc_16.add('h36);
      crc_16.add('h37);
      crc_16.add('h38);
      crc_16.add('h39);
      $display("CRC-16 = %X", crc_16.result());
      crc_32.add('h31);
      crc_32.add('h32);
      crc_32.add('h33);
      crc_32.add('h34);
      crc_32.add('h35);
      crc_32.add('h36);
      crc_32.add('h37);
      crc_32.add('h38);
      crc_32.add('h39);
      $display("CRC-32 = %X", crc_32.result());
      crc_16_dnp.add('h31);
      crc_16_dnp.add('h32);
      crc_16_dnp.add('h33);
      crc_16_dnp.add('h34);
      crc_16_dnp.add('h35);
      crc_16_dnp.add('h36);
      crc_16_dnp.add('h37);
      crc_16_dnp.add('h38);
      crc_16_dnp.add('h39);
      $display("CRC-16-DNP = %X", crc_16_dnp.result());
      crc_8.add('h31);
      crc_8.add('h32);
      crc_8.add('h33);
      crc_8.add('h34);
      crc_8.add('h35);
      crc_8.add('h36);
      crc_8.add('h37);
      crc_8.add('h38);
      crc_8.add('h39);
      $display("CRC-8 = %X", crc_8.result());
      delay(10);
   endseq;
   
   mkAutoFSM(test);
endmodule