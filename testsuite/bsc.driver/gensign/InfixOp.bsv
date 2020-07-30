typeclass InfixOpTC#(type data_t);
   function data_t \~~ (data_t x, data_t y);
endtypeclass

instance InfixOpTC#(Bit#(8));
   function Bit#(8) \~~ (Bit#(8) x, Bit#(8) y);
      return (x + y);
   endfunction
endinstance

