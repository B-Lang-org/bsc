// A simple vending machine interface
// with three inputs and two outputs.

interface Vending;
  // 10-cent deposit input
  method Action ten_cent_in();
  // 50-cent deposit input
  method Action fifty_cent_in();
  // Money back button input
  method Action money_back_button();
  // dispense 10 cents output
  method Bool dispense_ten_cents();
  // dispense chewing gum output
  method Bool dispense_gum();
endinterface
