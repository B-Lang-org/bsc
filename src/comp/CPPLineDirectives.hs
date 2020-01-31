module CPPLineDirectives (cppLine_to_svLine) where
-- need "-package regex-compat
import Text.Regex
import ErrorUtil(internalError)

r2 :: Regex
r2 = mkRegex "^# *(line)? +([0-9]+) +(\".*\")"
{-

If you have weird code like

/*
  Hello, we are inside a comment
#ignore me
#line 200
*/

all bets are off.
-}
cppLine_to_svLine :: String -> String
cppLine_to_svLine s =
    case (matchRegex r2 s) of
      Just [_,line_number, file_name] ->
          ("`line " ++ line_number ++ " " ++file_name)
      Nothing -> s
      _ -> internalError "unexpected regex matching in CPPLineDirectives"
