import List::*;

function Action displayFail(Integer i);
  $display("Fail %0d", i);
endfunction

function Action displayFailMinus(Integer i);
  $display("Fail -1 %0d", i);
endfunction

function Action displayFailPlus(Integer i);
  $display("Fail +1 %0d", i);
endfunction

function Tuple3#(List#(Integer), List#(Integer), List#(Integer)) buildLists(Integer n);

  List#(Integer) fail      = nil;
  List#(Integer) failminus = nil;
  List#(Integer) failplus  = nil;
  Integer power = 1;
 
  Bool pass = True;
 
  for(Integer i = 0; primSeq(pass,primSeq(power,i < n)); i = i + 1)
  begin
    if(log2(power) != i) begin
      fail = cons(i, fail);
    end
    if(i > 2 && log2(power - 1) != i) begin
      failminus = cons(i, failminus);
    end
    if(log2(power + 1) != i + 1) begin
      failplus = cons(i, failplus);
    end
    pass = isNull(fail) && isNull(failminus) && isNull(failplus);
    power = message(strConcat("Iteration: ", integerToString(i)), power * 2);
  end

  return(tuple3(fail, failminus, failplus));

endfunction

(* synthesize *)
module sysPureLoop();

  match {.fail, .failminus, .failplus} = buildLists(65536);
  
  rule test;
    joinActions(map(displayFail,fail));
    joinActions(map(displayFailMinus,failminus));
    joinActions(map(displayFailPlus,failplus));
    if(isNull(fail) && isNull(failminus) && isNull(failplus))
      $display("Test passed");
    $finish(0);
  endrule

endmodule