
// function to make $stime the same for Bluesim and Verilog
function ActionValue#(Bit#(32)) adj_stime(Integer p);
   actionvalue
      let adj = (p + 1) / 2;
      let t <- $stime();
      if (genVerilog)
	 return (t + fromInteger(adj));
      else
	 return t;
   endactionvalue
endfunction

function Action push_print (Integer wrp, Bit#(32) a);
    action
        $display(adj_stime(wrp), "\tPushing Data=%d", a);
    endaction
endfunction: push_print

function Action pop_print(Integer rdp);
    action
        $display(adj_stime(rdp), "\tPopping Data\n");
    endaction
endfunction: pop_print

function Action my_print (Integer rdp, Bit#(8) expected, Bit#(8) actual,
			  Bool cond, Reg#(Bool) t_pass);
    action
        case(cond)
        True:
            if (actual==expected) 
                $display(adj_stime(rdp), "\tData Match, Actual = %d",actual); 
            else begin
                t_pass <= False;
                $display(adj_stime(rdp), "\tData Mismatch, Actual = %d, Expected = %d",actual,expected);                           
            end
        False: 
            $display(adj_stime(rdp), "\tActual = %d, Expected = nothing",actual);
        endcase
    endaction
endfunction: my_print

