import List::*;

(* synthesize *)
module sysStringCharFunctions();

   rule r;

    $display("#----- $display of Char");
    begin
      Char c = "y";
      $display(c);
    end

    $display("#----- stringSplit, stringHead, stringTail");
    begin
      case (stringSplit("")) matches
         tagged Invalid : $display("Null");
         default : $display("ERROR");
      endcase

      String str = "Hello World";
      case (stringSplit(str)) matches
         tagged Valid { .hd, .tl } :
            $display("'%s', '%s'", hd, tl);
         default :
            $display("ERROR");
      endcase

      let hd2 = stringHead(str);
      let tl2 = stringTail(str);
      $display("'%s', '%s'", hd2, tl2);
    end

    $display("#----- stringCons");
    begin
      String str = stringCons("H", stringCons("e", "llo World"));
      case (stringSplit(str)) matches
         tagged Valid { .hd, .tl } :
            $display("'%s', '%s'", hd, tl);
         default :
            $display("ERROR");
      endcase
    end

    $display("#----- stringToCharList, charListToString");
    begin
      List#(Char) cs = cons("H", cons("i", cons("!", nil)));
      String str = charListToString(cs);
      $display("'%s'", str);

      String str2 = "Hello World";
      List#(Char) cs2 = stringToCharList(str2);
      $display("'%s' '%s'", cs2[1], cs2[6]);
    end

    $display("#----- []-select, []-update");
    begin
      String str = "Hello World";
      $display("'%s'", str[8]);

      str[0] = "M";
      str[7] = "e";
      $display("'%s'", str);
    end

    $display("#----- charToString");
    begin
      Char c = "!";
      String str = charToString(c);
      $display("'%s'", str);
    end

    $display("#----- charToInteger, integerToChar");
    begin
      Char c1 = "a";
      Char c2 = "A";
      Char c3 = "0";
      $display("%d, %d, %d", charToInteger(c1), charToInteger(c2),
               charToInteger(c3));

      Integer i1 = 66;
      Integer i2 = 50;
      $display("'%s' '%s'", integerToChar(i1), integerToChar(i2));
    end

    $display("#----- isSpace");
    begin
      $display(isSpace(" "));
      $display(isSpace("\t"));
      $display(isSpace("\n"));
      $display(isSpace("\v"));
      $display(isSpace("\f"));
      $display(isSpace("\x0D")); // carriage return "\r"

      $display(isSpace("\xA0")); // non-breaking space in some encodings

      $display(isSpace("%"));
      $display(isSpace("A"));
      $display(isSpace("s"));
    end

    $display("#----- isLower, isUpper, isAlpha, isAlphaNum");
    begin
      $display(isLower("a"), " ", isUpper("a"));
      $display(isLower("A"), " ", isUpper("A"));
      $display(isLower("z"), " ", isUpper("z"));
      $display(isLower("Z"), " ", isUpper("A"));
      $display(isLower("0"), " ", isUpper("0"));
      $display(isLower("9"), " ", isUpper("9"));
      $display(isLower("$"), " ", isUpper("$"));
      $display(isLower(" "), " ", isUpper(" "));

      $display(isAlpha("a"), " ", isAlphaNum("a"));
      $display(isAlpha("A"), " ", isAlphaNum("A"));
      $display(isAlpha("z"), " ", isAlphaNum("z"));
      $display(isAlpha("Z"), " ", isAlphaNum("A"));
      $display(isAlpha("0"), " ", isAlphaNum("0"));
      $display(isAlpha("9"), " ", isAlphaNum("9"));
      $display(isAlpha("$"), " ", isAlphaNum("$"));
      $display(isAlpha(" "), " ", isAlphaNum(" "));
    end

    $display("#----- isDigit, isOctDigit, isHexDigit");
    begin
      $display(isDigit("0"), " ", isOctDigit("0"), " ", isHexDigit("0"));
      $display(isDigit("3"), " ", isOctDigit("3"), " ", isHexDigit("3"));
      $display(isDigit("7"), " ", isOctDigit("7"), " ", isHexDigit("7"));
      $display(isDigit("9"), " ", isOctDigit("9"), " ", isHexDigit("9"));
      $display(isDigit("a"), " ", isOctDigit("a"), " ", isHexDigit("a"));
      $display(isDigit("A"), " ", isOctDigit("A"), " ", isHexDigit("A"));
      $display(isDigit("f"), " ", isOctDigit("f"), " ", isHexDigit("f"));
      $display(isDigit("F"), " ", isOctDigit("F"), " ", isHexDigit("F"));
      $display(isDigit("g"), " ", isOctDigit("g"), " ", isHexDigit("g"));
      $display(isDigit("G"), " ", isOctDigit("G"), " ", isHexDigit("G"));
      $display("%h %h %h", isDigit("&"), isOctDigit("&"), isHexDigit("&"));
      $display("%h %h %h", isDigit(" "), isOctDigit(" "), isHexDigit(" "));
    end

    $display("#----- toUpper, toLower");
    begin
      $display("'%s' '%s'", toUpper("a"), toLower("a"));
      $display("'%s' '%s'", toUpper("A"), toLower("A"));
      $display("'%s' '%s'", toUpper("z"), toLower("z"));
      $display("'%s' '%s'", toUpper("Z"), toLower("Z"));
      $display("'%s' '%s'", toUpper("0"), toLower("0"));
      $display("'%s' '%s'", toUpper(" "), toLower(" "));
    end

    $display("#----- digitToInteger, digitToBits");
    begin
      Bit#(17) b1 = digitToBits("4");
      Bit#(65) b2 = digitToBits("9");
      $display("%d, %0h, %d", digitToInteger("0"), b1, b2);
    end

    $display("#----- integerToDigit, bitsToDigit");
    begin
      Integer i1 = 0;
      Integer i2 = 5;
      Integer i3 = 9;
      Bit#(1) b1 = 0;
      Bit#(8) b2 = 5;
      Bit#(128) b3 = 9;
      $display("'%s' '%s' '%s'",
               integerToDigit(i1), integerToDigit(i2), integerToDigit(i3));
      $display("'%s' '%s' '%s'",
               bitsToDigit(b1), bitsToDigit(b2), bitsToDigit(b3));
    end

    $display("#----- instances Eq#(Char), Ord#(Char)");
    begin
      Char c1 = "g";
      Char c2 = "h";
      Char c3 = "H";
      Char c4 = "(";
      $display("%h %h %h", (c1 == c2), (c2 == c3), (c4 == "("));
      $display("%h %h %h", (c1 < c2), (c1 < "g"), (c1 <= "g"));
    end

      $finish(0);
   endrule

endmodule

