import Vector::*;
import GetPut::*;
import ClientServer::*;
import StmtFSM::*;
import Types::*;
import QuickSort::*;

(* synthesize *)
module sysTb();

   Server#(VData_T#(16, Bit#(32)), VData_T#(16, Bit#(32))) dut <- mkQuickSort;

   function Action putData(Vector#(16, Bit#(32)) data) = action
      $display("%t Put data", $time);
      dut.request.put(data);
   endaction;

   function Action getData = action
      $display("%t Get data", $time);
      let result <- dut.response.get;
      for (int i=0; i<16; i=i+1)
         $display("%d", result[i]);
   endaction;

   mkAutoFSM(seq
      action
         Bit#(32) inData[16] = { 53, 101, 120,  10,  91, 250,  19,   8,
                                651,  22, 544,  87,  20, 199,  76,  33};
         putData(arrayToVector(inData));
      endaction
      while(True) noAction;
   endseq);

   mkAutoFSM(seq
      getData;
   endseq);

endmodule

