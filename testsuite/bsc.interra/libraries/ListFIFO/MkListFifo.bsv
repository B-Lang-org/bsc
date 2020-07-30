package MkListFifo;

import ListFIFO :: *;
import FIFO :: *;
import List :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction

function Action displayabc1 (Tuple3#(a,a,a) abc) provisos (Bits #(a, sa));
    action
      $display ("%d", tpl_1(abc));
      $display ("%d", tpl_2(abc));
      $display ("%d", tpl_3(abc));
    endaction
endfunction


function Action display_list (List #(a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction

module mkDesign_MkListFifo();
   FIFO#(List#(Int #(5))) datafifo <- mkListFIFO(3);
endmodule: mkDesign_MkListFifo

module mkTestbench_MkListFifo();
  List #(Int #(5)) my_list1 = Cons (0, Cons (1, Cons (2, Cons (3, Cons (4, Nil)))));
  List #(Int #(5)) my_list2 = Cons (5, Cons (6, Cons (7, Cons (8, Cons (9, Nil)))));
  List #(Int #(5)) my_list3 = Cons (10, Cons (11, Cons (12, Cons (13, Cons (14, Nil)))));
  //List #(List#(Int #(5))) my_list4 = Cons (my_list1, Cons (my_list2, Cons (my_list3,Nil)));

  FIFO#(List#(Int #(5))) datafifo <- mkListFIFO(5);

  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule data_write (counter < 3);
	 if (counter == 0)
       datafifo.enq(my_list1);
	 if (counter == 1)
       datafifo.enq(my_list2);
	 if (counter == 2)
       datafifo.enq(my_list3);
  endrule

  rule read_value ((counter >=3) && (counter < 6));
     List #(Int #(5)) my_list4 = datafifo.first;
	 if (counter == 3)
	    begin
	      if (datafifo.first != my_list1)
		    begin
		       $display("Mismatch ");
		       $display("Expected list");
		       display_list (my_list1);
		       $display("Actual list");
		       display_list (datafifo.first);
	           fail <= True;
		    end
	    end
	 if (counter == 4)
	    begin
	      if (datafifo.first != my_list2)
		    begin
		       $display("Mismatch ");
		       $display("Expected list");
		       display_list (my_list2);
		       $display("Actual list");
		       display_list (datafifo.first);
	           fail <= True;
		    end
	    end
	 if (counter == 5)
	    begin
	      if (datafifo.first != my_list3)
		    begin
		       $display("Mismatch ");
		       $display("Expected list");
		       display_list (my_list3);
		       $display("Actual list");
		       display_list (datafifo.first);
	           fail <= True;
		    end
	    end
	 datafifo.deq;
  endrule

  rule endofsim (counter == 6);
	if (fail)
	  $display("counter = %d Simulation Fails",counter);
	else
	  $display("Simulation Passes");
	$finish(2'b00);
  endrule


endmodule : mkTestbench_MkListFifo
endpackage : MkListFifo
