
import VendingIfc::*;

(* synthesize *)
module mkVending(Vending);

  // count of money in the vending machine
  Reg#(UInt#(7)) count();
  mkReg#(0) the_count(count);

  // state bit that controls dispensing money back
  Reg#(Bool) money_back();
  mkReg#(False) the_money_back(money_back);

  // wire to control dispense money output
  PulseWire dispense_money();
  mkPulseWire the_dispense_money(dispense_money);

  // wire to control gum dispenser output
  PulseWire gum_control();
  mkPulseWire the_gum_control(gum_control);

  // rule that controls dispensing of money
  rule do_dispense_money(money_back);
     let new_count = count - 10;
     count <= new_count;
     dispense_money.send();
     if(new_count == 0)
       money_back <= False;
  endrule

  // rule that controls dispensing of gum
  rule do_dispense_gum(!money_back && count >= 50);
     count <= count - 50;
     gum_control.send();
  endrule

  // Input-handling methods
  method Action ten_cent_in() if(!money_back);
     count <= count + 10;
  endmethod

  method Action fifty_cent_in() if(!money_back);
     count <= count + 50;
  endmethod     

  method Action money_back_button() if(!money_back);
     money_back <= True;
  endmethod

  // connect wires for money and gum outputs
  method dispense_ten_cents = dispense_money;
  method dispense_gum = gum_control;
  
endmodule
