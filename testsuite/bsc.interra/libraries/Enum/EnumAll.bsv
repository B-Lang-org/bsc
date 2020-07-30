package EnumAll;

import Enum :: *;
import List :: *;


/////////////////////////////////////////////////////////////////
///////Enumerated DataType//////////////////////////////////////

typedef enum  {Idle , First_F6 , Second_F6 , Third_F6 , First_28 , Second_28, Detected} Datastates 
    deriving (Eq,Bits, Bounded);

//////////////////////////////////////////////////////////////////
//////////Structure //////////////////////////////////////////////

typedef struct {
    Bit#(2) red;
    Bit#(1) blue;
} RgbColor deriving (Eq, Bits, Bounded);

///////////////////////////////////////////////////////////////////

////////////Polymorphic Structure//////////////////////////////
typedef struct {
    colora red;
    colorb blue;
} RgbColorpoly #(type colora, type colorb) deriving (Eq, Bits, Bounded);
///////////////////////////////////////////////////////////////

////////////Polymorphic Tagged Union//////////////////////////////
typedef union tagged {
    void Yellow;
    b Red;
    a Blue;
} RgbColorTaggedpoly #(type a, type b) deriving (Eq, Bits, Bounded);

module mkTestbench_EnumAll ();
     List #(Bool) list1 = enumAll;
     List #(Bool) list1_exp = Cons (False, Cons (True, Nil));
     
     List #(Datastates) list2 = enumAll;
     List #(Datastates) list2_exp = Cons (Idle, Cons (First_F6, Cons (Second_F6, Cons (Third_F6, Cons (First_28, Cons (Second_28, Cons (Detected, Nil )))))));
    
     List #(RgbColor) list3 = enumAll;
     
     RgbColor list3_inst1 = RgbColor { red : 2'b00, blue : 0};
     RgbColor list3_inst2 = RgbColor { red : 2'b00, blue : 1};
     RgbColor list3_inst3 = RgbColor { red : 2'b01, blue : 0};
     RgbColor list3_inst4 = RgbColor { red : 2'b01, blue : 1};
     RgbColor list3_inst5 = RgbColor { red : 2'b10, blue : 0};
     RgbColor list3_inst6 = RgbColor { red : 2'b10, blue : 1};
     RgbColor list3_inst7 = RgbColor { red : 2'b11, blue : 0};
     RgbColor list3_inst8 = RgbColor { red : 2'b11, blue : 1};
     
     List #(RgbColor) list3_exp = Cons (list3_inst1,Cons (list3_inst2,Cons (list3_inst3,Cons (list3_inst4,Cons (list3_inst5,Cons (list3_inst6,Cons (list3_inst7,Cons (list3_inst8,Nil)))))))); 
     
     
     List #(RgbColorpoly #(Bit #(2), Bit #(1))) list4 = enumAll;
     
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst1 = RgbColorpoly { red : 2'b00, blue : 0};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst2 = RgbColorpoly { red : 2'b00, blue : 1};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst3 = RgbColorpoly { red : 2'b01, blue : 0};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst4 = RgbColorpoly { red : 2'b01, blue : 1};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst5 = RgbColorpoly { red : 2'b10, blue : 0};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst6 = RgbColorpoly { red : 2'b10, blue : 1};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst7 = RgbColorpoly { red : 2'b11, blue : 0};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst8 = RgbColorpoly { red : 2'b11, blue : 1};
     
     List #(RgbColorpoly  #(Bit #(2), Bit #(1))) list4_exp = Cons (list4_inst1,Cons (list4_inst2,Cons (list4_inst3,Cons (list4_inst4,Cons (list4_inst5,Cons (list4_inst6,Cons (list4_inst7,Cons (list4_inst8,Nil))))))));

     
 

     rule always_true (True);
         if (list1 != list1_exp || list2 != list2_exp || list3 != list3_exp || list4 != list4_exp ) 
            $display ("Simulation Fails");
         else
            $display ("Simulation Passes");
         $finish (2'b00);
     endrule
     
endmodule : mkTestbench_EnumAll

endpackage : EnumAll
    
