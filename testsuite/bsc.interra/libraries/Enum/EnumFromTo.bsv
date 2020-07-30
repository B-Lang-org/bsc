package EnumFromTo;

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


module mkTestbench_EnumFromTo ();
     List #(Bool) list1a = enumFromTo (False,True);
     List #(Bool) list1a_exp = Cons (False, Cons (True, Nil));
     
     List #(Bool) list1b = enumFromTo (True,True);
     List #(Bool) list1b_exp = Cons (True, Nil);
     
     List #(Bool) list1c = enumFromTo (False,False);
     List #(Bool) list1c_exp = Cons (False, Nil);
     
     List #(Bool) list1d = enumFromTo (True,False);
     List #(Bool) list1d_exp = Nil;
     
     List #(Datastates) list2a = enumFromTo (First_F6, Second_28);
     List #(Datastates) list2a_exp = Cons (First_F6, Cons (Second_F6, Cons (Third_F6, Cons (First_28, Cons (Second_28, Nil )))));
    
     List #(Datastates) list2b = enumFromTo (Detected, Idle);
     List #(Datastates) list2b_exp = Nil;
     
     List #(Datastates) list2c = enumFromTo (Idle, Detected);
     List #(Datastates) list2c_exp = Cons (Idle, Cons (First_F6, Cons (Second_F6, Cons (Third_F6, Cons (First_28, Cons (Second_28, Cons (Detected, Nil )))))));
     
     List #(Datastates) list2d = enumFromTo (Second_28, Second_28);
     List #(Datastates) list2d_exp = Cons (Second_28, Nil );
     
     
     RgbColor list3_inst1 = RgbColor { red : 2'b00, blue : 0};
     RgbColor list3_inst2 = RgbColor { red : 2'b00, blue : 1};
     RgbColor list3_inst3 = RgbColor { red : 2'b01, blue : 0};
     RgbColor list3_inst4 = RgbColor { red : 2'b01, blue : 1};
     RgbColor list3_inst5 = RgbColor { red : 2'b10, blue : 0};
     RgbColor list3_inst6 = RgbColor { red : 2'b10, blue : 1};
     RgbColor list3_inst7 = RgbColor { red : 2'b11, blue : 0};
     RgbColor list3_inst8 = RgbColor { red : 2'b11, blue : 1};
     
     List #(RgbColor) list3a = enumFromTo(list3_inst8, list3_inst8) ;
     List #(RgbColor) list3a_exp = Cons (list3_inst8,Nil); 
     
     List #(RgbColor) list3b = enumFromTo(list3_inst5, list3_inst8) ;
     List #(RgbColor) list3b_exp = Cons (list3_inst5,Cons (list3_inst6,Cons (list3_inst7,Cons (list3_inst8,Nil)))); 
     
     
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst1 = RgbColorpoly { red : 2'b00, blue : 0};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst2 = RgbColorpoly { red : 2'b00, blue : 1};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst3 = RgbColorpoly { red : 2'b01, blue : 0};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst4 = RgbColorpoly { red : 2'b01, blue : 1};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst5 = RgbColorpoly { red : 2'b10, blue : 0};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst6 = RgbColorpoly { red : 2'b10, blue : 1};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst7 = RgbColorpoly { red : 2'b11, blue : 0};
     RgbColorpoly #(Bit #(2), Bit #(1)) list4_inst8 = RgbColorpoly { red : 2'b11, blue : 1};
     
     List #(RgbColorpoly #(Bit #(2), Bit #(1))) list4 = enumFromTo (list4_inst2, list4_inst7);
     List #(RgbColorpoly  #(Bit #(2), Bit #(1))) list4_exp = Cons (list4_inst2,Cons (list4_inst3,Cons (list4_inst4,Cons (list4_inst5,Cons (list4_inst6,Cons (list4_inst7,Nil))))));

     

     rule always_true (True);
         if (list1a != list1a_exp  || list1b != list1b_exp || list1c != list1c_exp || list1d != list1d_exp || list2a != list2a_exp || list2b != list2b_exp || list2c != list2c_exp || list2d != list2d_exp || list3a != list3a_exp || list3b != list3b_exp || list4 != list4_exp ) 
            $display ("Simulation Fails");
         else
            $display ("Simulation Passes");
         $finish (2'b00);
     endrule
     
endmodule : mkTestbench_EnumFromTo

endpackage : EnumFromTo
    
