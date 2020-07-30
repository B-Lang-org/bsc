package Bank;

import Vector::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface BankClient_IFC;
   method ActionValue#(Bool) withdraw (Bit#(16) id);
   method Action deposit (Bit#(16) id);
endinterface

interface Bank_IFC#(parameter type count);
   interface Vector#(count, BankClient_IFC) clients;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////
   
module mkBank (Bank_IFC#(count));

   let icount = valueOf(count);
   
   Vector#(count, Reg#(Bool)) avail_vector <- replicateM(mkReg(True));

   // Now create the vector of interfaces
   Vector#(count, BankClient_IFC) client_vector = newVector;

   for (Integer x = 0; x < icount; x = x + 1)

      client_vector[x] = (interface BankClient_IFC
	 
			     method ActionValue#(Bool) withdraw(Bit#(16) id);
				if (id >= fromInteger(icount))
				   return False;
				else
				   begin
				      let value = asReg(avail_vector[id]);
//				      avail_vector[id]._write(False);
				      value <= False;
//				      return value._read;
	 			      return value;
				   end
	 		     endmethod
	 
			     method Action deposit(Bit#(16) id);
	 			avail_vector[id] <= True;
			     endmethod
			  endinterface
			  );
			   
   interface clients = client_vector;
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

endpackage
