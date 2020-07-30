-- the program used to generate OctalChars.bsv
-- should it need to be changed
-- redirect stdout to OctalChars.bsv

showOct num = show first ++ show middle ++ show last
  where (rest, last) = quotRem num 8
        (first, middle) = quotRem rest 8

nums = [0..255]

display_num num = putStrLn ("$display(\"\\" ++ (showOct num) ++ "\");")

main = do
  putStrLn("(* synthesize *)")
  putStrLn("module sysOctalChars();")
  putStrLn("rule test;") 
  mapM_ display_num nums
  putStrLn("endrule")
  putStrLn("endmodule")
