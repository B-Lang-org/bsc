import Vector::*;

// Test that the order of splitting and recombining are the same
// (the vector going in is the same as the vector read on the other side)

typedef Vector#(2,Vector#(3,(Vector#(5,int)))) VVV;

(* synthesize *)
module sysVecVecVecInt_Order ();
    int vs[2][3][5] =
          { { { 1, 2, 3, 4, 5}, { 6, 7, 8, 9,10}, {11,12,13,14,15} },
            { {16,17,18,19,20}, {21,22,23,24,25}, {26,27,28,29,30} } };
    // would need to use primArrayMap to map arrayToVector on vs to get vec
    VVV vec = ?;
    for (Integer i=0; i<2; i=i+1)
      for (Integer j=0; j<3; j=j+1)
        for (Integer k=0; k<5; k=k+1)
           vec[i][j][k] = vs[i][j][k];

    Reg#(Bool) started <- mkReg(False);

    SubIfc sub <- mkVecVecVecInt_Order_Sub(vec);

    rule top_disp_rule (!started);
      $display("Outside:");
      for (Integer i=0; i<2; i=i+1)
        for (Integer j=0; j<3; j=j+1)
          for (Integer k=0; k<5; k=k+1)
             $display("(%h,%h,%h) = %h", i, j, k, vec[i][j][k]);
      started <= True;
      sub.start();
    endrule

endmodule

interface SubIfc;
    method Action start();
endinterface

module mkVecVecVecInt_Order_Sub #(VVV vec) (SubIfc);

    Reg#(Bool) started <- mkReg(False);
    Reg#(Bool) done <- mkReg(False);

    rule sub_disp_rule (!started);
      $display("Inside:");
      for (Integer i=0; i<2; i=i+1)
        for (Integer j=0; j<3; j=j+1)
          for (Integer k=0; k<5; k=k+1)
             $display("(%h,%h,%h) = %h", i, j, k, vec[i][j][k]);
      done <= True;
      started <= False;
    endrule

    rule finish_rule (done);
      $finish(0);
    endrule

    method Action start();
       started <= True;
    endmethod
endmodule

