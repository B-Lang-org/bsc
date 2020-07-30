import Vector::*;
import GetPut::*;
import ClientServer::*;
import StmtFSM::*;
import Types::*;
import RadixSort::*;

(* synthesize *)
module sysTb();

   Server#(VData_T, VData_T) dut <- mkRadixSort;

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

      action
         Bit#(32) inData[16] = {321,  33,   2, 499,  43, 101,   9,  12,
                                229, 589,  88,  73, 577,   6, 149, 806};
         putData(arrayToVector(inData));
      endaction

      action
         Bit#(32) inData[16] = {402, 167, 718,  93, 317, 288,  99, 200,
                                  3,  10, 633, 345, 111,  55, 291, 777};
         putData(arrayToVector(inData));
      endaction

      action
         Bit#(32) inData[16] = {402, 167, 718,  93, 317, 288,  99, 200,
                                  3,  10, 633, 345, 111,  55, 291, 777};
         putData(arrayToVector(inData));
      endaction

      action
         Bit#(32) inData[16] = {1042, 176, 718,  9333, 33317, 55288,  7799, 8200,
                                  3,  170, 655533, 13311, 545,  3545, 2691, 77007};
         putData(arrayToVector(inData));
      endaction

      action
         Bit#(32) inData[16] = {16117, 44718, 593,  66402, 38817,2288,  99, 111200,
                                  1000003,  510, 6666633, 3334335, 123232311,  555555, 25591, 12345777};
         putData(arrayToVector(inData));
      endaction
      while(True) noAction;
   endseq);

   mkAutoFSM(seq
      getData;
      getData;
      getData;
      getData;
      getData;
      getData;
   endseq);

endmodule

