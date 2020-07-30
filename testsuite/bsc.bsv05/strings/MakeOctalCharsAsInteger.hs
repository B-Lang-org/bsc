-- the program used to generate OctalCharsAsInteger.bsv
-- should it need to be changed
-- redirect stdout to OctalCharsAsInteger.bsv

showOct num = show first ++ show middle ++ show last
  where (rest, last) = quotRem num 8
        (first, middle) = quotRem rest 8

nums = [0..255]

display_num num = putStrLn ("$display(primStringToInteger(\"\\" ++ (showOct num) ++ "\"));")

main = do
  putStrLn("(* synthesize *)")
  putStrLn("module sysOctalCharsAsInteger();")
  putStrLn("rule test;") 
  mapM_ display_num nums
  putStrLn ("$finish(0);");
  putStrLn("endrule")
  putStrLn("endmodule")
