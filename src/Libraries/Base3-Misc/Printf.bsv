package Printf;

export sprintf;
export SPrintfType, PrintfArg;

import List::*;
import Real::*;

// -----

function r sprintf(String fmt) provisos (SPrintfType#(r));
  return (spr(fmt,nil));
endfunction

// -----

typeclass SPrintfType#(type t);
  function t spr(String fmt, List#(UPrintf) args);
endtypeclass

// -----

instance SPrintfType#(String);
  function spr(fmt, args) = uprintf(fmt, reverse(args));
endinstance

instance SPrintfType#(function r fn(a arg))
provisos (PrintfArg#(a), SPrintfType#(r));
  function spr(fmt, args, a) = spr(fmt, cons(toUPrintf(a), args));
endinstance

// -----

typeclass PrintfArg#(type t);
   function UPrintf toUPrintf(t arg);
endtypeclass

instance PrintfArg#(Char);
   function toUPrintf(c) = tagged UChar c;
endinstance

instance PrintfArg#(String);
   function toUPrintf(s) = tagged UString s;
endinstance

instance PrintfArg#(Integer);
   function toUPrintf(n) = tagged UInteger tuple2(0, n);
endinstance

instance PrintfArg#(Bit#(n));
   function toUPrintf(n) =
       tagged UInteger tuple2(0, primUIntBitsToInteger(n));
endinstance

instance PrintfArg#(UInt#(n));
   function toUPrintf(n) =
       tagged UInteger tuple2(0, primUIntBitsToInteger(pack(n)));
endinstance

instance PrintfArg#(Int#(n));
   function UPrintf toUPrintf(Int#(n) n);
       Integer lo = -(2**(valueOf(n)-1));
       Integer v = primIntBitsToInteger(pack(n));
       return (tagged UInteger tuple2(lo, v));
   endfunction
endinstance

instance PrintfArg#(Real);
   function toUPrintf(r) = tagged UReal r;
endinstance

// -----

typedef union tagged {
   Char                      UChar;
   String                    UString;
   // the second value is the minbound for sized types (0 for Integer)
   Tuple2#(Integer, Integer) UInteger;
   Real                      UReal;
} UPrintf;

function String uprintf(String fmt, List#(UPrintf) args);
   case (stringSplit(fmt)) matches
     tagged Valid {"%", .cs} : begin
        if (stringSplit(cs) matches tagged Valid {"%", .cs2}) begin
           return stringCons("%", uprintf(cs2, args));
        end
        else begin
           if (isNull(args))
             return argerr;
           else
             return doFmt(cs, args);
        end
     end
     tagged Valid {.c, .cs} : begin
        return stringCons(c, uprintf(cs, args));
     end
     // otherwise, the fmt string is empty
     default : begin
        if (isNull(args))
          return "";
        else
          return fmterr;
     end
   endcase
endfunction

function String doFmt(String cs, List#(UPrintf) args);

   match { .width, .prec, .ladj, .zero, .plus, .cs2, .args2 }
      = getSpecs(False, False, False, cs, args);

   function adjust(p);
      match {.pre, .str } = p;
      let sp_len = stringLength(str) + stringLength(pre);
      let fillchar = ( zero ? "0" : " " );
      let fill = ( (sp_len < width) ?
                   charListToString(replicate(width - sp_len, fillchar)) :
                   "" );
      if (ladj)
         return (pre + str + fill);
      else if (zero)
         return (pre + fill + str);
      else
         return (fill + pre + str);
   endfunction

   function adjust2(p);
      match {.pre, .str} = p;
      if (plus && (pre == ""))
         return adjust(tuple2("+", str));
      else
         return adjust(p);
   endfunction

   case (stringSplit(cs2)) matches
      tagged Valid { .c, .cs3 } : begin
         if (isNull(args))
            return argerr;
         else begin
            let a = head(args2);
            let args3 = tail(args2);

            let char_fmt = adjust(tuple2("", charToString(tochar(a))));
            let string_fmt = adjust(tuple2("", tostr(prec, a)));
            let dec_fmt = adjust2(fmti(prec, a));
            //let unsigned_dec_fmt = adjust(tuple2("", fmtu(10, prec, a)));
            let hex_lower_fmt = adjust(tuple2("", fmtu(16, prec, a)));
            let hex_upper_fmt =
                    adjust(tuple2("", toUpperString(fmtu(16, prec, a))));
            let oct_fmt = adjust(tuple2("", fmtu(8, prec, a)));
            let bin_fmt = adjust(tuple2("", fmtu(2, prec, a)));
            let real_fmt = adjust2(dfmt2(c, prec, a));

            String s1;
            case (c) matches
               "c" : s1 = char_fmt;
	       // support capitalized form
               "C" : s1 = char_fmt;

               "s" : s1 = string_fmt;
	       // support capitalized form
               "S" : s1 = string_fmt;

               "d" : s1 = dec_fmt;
               "i" : s1 = dec_fmt;
	       // support capitalized form
               "D" : s1 = dec_fmt;
               "I" : s1 = dec_fmt;

               "x" : s1 = hex_lower_fmt;
               "X" : s1 = hex_upper_fmt;
               // support Verilog alternative
               "h" : s1 = hex_lower_fmt;
               "H" : s1 = hex_upper_fmt;

               "o" : s1 = oct_fmt;
	       // support capitalized form
               "O" : s1 = oct_fmt;

	       // support binary
               "b" : s1 = bin_fmt;
               "B" : s1 = bin_fmt;

               "e" : s1 = real_fmt;
               "E" : s1 = real_fmt;
               "f" : s1 = real_fmt;
               "F" : s1 = real_fmt;
               "g" : s1 = real_fmt;
               "G" : s1 = real_fmt;

               default:
                 s1 = error("bad formatting character: " + charToString(c));
            endcase
            return (s1 + uprintf(cs3, args3));
         end
      end
      default : return fmterr;
   endcase
endfunction

function Tuple2#(String, String) fmti(Integer prec, UPrintf arg);
  case (arg) matches
     tagged UInteger {.*, .i} :
        if (i < 0)
           return tuple2("-", integral_prec(prec, integerToString(-i)));
        else
           return tuple2("", integral_prec(prec, integerToString(i)));
     tagged UChar .c :
        return fmti(0, tagged UInteger tuple2(0, charToInteger(c)));
     default :
        return baderr;
  endcase
endfunction

function String fmtu(Integer b, Integer prec, UPrintf arg);
  case (arg) matches
     tagged UInteger {.lo, .i} :
        if (i < 0) begin
	   if (lo == 0)
              return error("printf: unsigned display of an unbounded negative number");
	   else
              return integral_prec(prec, itosb(b, (-2 * lo + i)));
        end
	else
           return integral_prec(prec, itosb(b, i));
     tagged UChar .c :
        return itosb(b, charToInteger(c));
     default :
        return baderr;
  endcase
endfunction

function String integral_prec(Integer prec, String integral);
  let n = prec - stringLength(integral);
  let s1 = charListToString(replicate(n, "0"));
  return (s1 + integral);
endfunction

function Integer toint(UPrintf arg);
  case (arg) matches
     tagged UInteger {.*, .i} : return i;
     tagged UChar .c : return charToInteger(c);
     default : return baderr;
  endcase
endfunction

function Char tochar(UPrintf arg);
  case (arg) matches
     tagged UInteger {.*, .i} : return integerToChar(i);
     tagged UChar .c : return c;
     default : return baderr;
  endcase
endfunction

function String tostr(Integer n, UPrintf arg);
  case (arg) matches
     tagged UString .s :
        if (n >= 0)
           return charListToString(take(n, stringToCharList(s)));
        else
           return s;
     default : return baderr;
  endcase
endfunction

function String itosb(Integer b, Integer n);
  function mkdigit(i) = cons(integerToHexDigit(i), nil);
  // for efficiency, loop with a Char list and convert to String at the end
  function List#(Char) fn(Integer cur_n);
     if (cur_n < b)
        return mkdigit(cur_n);
     else begin
        let r = cur_n % b;
        let q = cur_n / b;
        return append(fn(q), mkdigit(r));
     end
  endfunction
  return charListToString(fn(n));
endfunction

function Tuple2#(Integer, String) stoi(Integer a, String s);
  if (stringSplit(s) matches tagged Valid { .c, .r } &&& isDigit(c))
     return stoi(a*10 + digitToInteger(c), r);
  else
     return tuple2(a, s);
endfunction

function Tuple7#(Integer, Integer, Bool, Bool, Bool, String, List#(UPrintf))
         getSpecs(Bool l, Bool z, Bool s, String str, List#(UPrintf) args);
  case (stringSplit(str)) matches
     tagged Valid { "-", .cs } : return getSpecs(True, z, s, cs, args);
     tagged Valid { "+", .cs } : return getSpecs(l, z, True, cs, args);
     tagged Valid { "0", .cs } : return getSpecs(l, True, s, cs, args);
     tagged Valid { "*", .cs } : begin
        match { .args2, .n } = getStar(args);
        Integer        res_p    = -1;
        String         res_cs   = cs;
        List#(UPrintf) res_args = args2;
        if (stringSplit(cs) matches tagged Valid { ".", .r }) begin
           if (stringSplit(r) matches tagged Valid { "*", .r2 }) begin
              match { .args3, .p } = getStar(args2);
              res_p = p;
              res_cs = r2;
              res_args = args3;
           end
           else begin
              match { .p, .r2 } = stoi(0, r);
              res_p = p;
              res_cs = r2;
           end
        end
        return tuple7(n, res_p, l, z, s, res_cs, res_args);
     end
     tagged Valid { ".", .cs } : begin
        Integer        res_p;
        String         res_cs;
        List#(UPrintf) res_args;
        case (stringSplit(cs)) matches
           tagged Valid { "*", .r } : begin
              match { .args2, .p } = getStar(args);
              res_p = p;
              res_cs = r;
              res_args = args2;
           end
           default : begin
              match { .p, .cs2 } = stoi(0, cs);
              res_p = p;
              res_cs = cs2;
              res_args = args;
           end
        endcase
        return tuple7(0, res_p, l, z, s, res_cs, res_args);
     end
     tagged Valid { .c, .* } &&& isDigit(c) : begin
        match { .n, .cs2 } = stoi(0, str);
        Integer        res_p    = -1;
        String         res_cs   = cs2;
        List#(UPrintf) res_args = args;
        if (stringSplit(cs2) matches tagged Valid { ".", .r }) begin
           if (stringSplit(r) matches tagged Valid { "*", .r2 }) begin
              match { .args2, .p } = getStar(args);
              res_p = p;
              res_cs = r2;
              res_args = args2;
           end
           else begin
              match { .p, .r2 } = stoi(0, r);
              res_p = p;
              res_cs = r2;
           end
        end
        return tuple7(n, res_p, l, z, s, res_cs, res_args);
     end
     default :
        return tuple7(0, -1, l, z, s, str, args);
  endcase
endfunction

function Tuple2#(List#(UPrintf), Integer) getStar(List#(UPrintf) args);
   if (isNull(args))
      return argerr;
   else
      return tuple2(tail(args), toint(head(args)));
endfunction

function Tuple2#(String, String) dfmt2(Char c, Integer p, UPrintf arg);
  case (arg) matches
     tagged UReal .d : return dfmt(c, p, d);
     default : return baderr;
  endcase
endfunction

function Tuple2#(String, String) dfmt(Char c, Integer p, Real d);
  Maybe#(Integer) mp = ( (p < 0) ? tagged Invalid : tagged Valid p );
  String res;
  case (c)
     "e" : res = formatReal(RFExponent, mp, d);
     "f" : res = formatReal(RFFixed, mp, d);
     "g" : res = formatReal(RFGeneric, mp, d);
     "E" : res = toUpperString(formatReal(RFExponent, mp, d));
     "F" : res = toUpperString(formatReal(RFFixed, mp, d));
     "G" : res = toUpperString(formatReal(RFGeneric, mp, d));
     default : res = error("printf: impossible");
  endcase
  case (stringSplit(res)) matches
     tagged Valid { "-", .r } : return tuple2("-", r);
     default : return tuple2("", res);
  endcase
endfunction

function t fmterr() = error("printf: formatting string ended prematurely");
function t argerr() = error("printf: argument list ended prematurely");
function t baderr() = error("printf: bad argument");

function String toUpperString(String str);
   return charListToString(map(toUpper, stringToCharList(str)));
endfunction

// -----

typedef enum { RFGeneric, RFExponent, RFFixed } RealFormat deriving (Eq);

function String formatReal(RealFormat fmt, Maybe#(Integer) mp, Real d);
  Integer base = 10;
  // BSV Real values can not be NaN
  //if (isNaN(d))
  //   return "NaN";
  //else
  if (isInfinite(d))
     return ( (d < 0) ? "-Infinity" : "Infinity" );
  else if ((d < 0) || isNegativeZero(d))
     return stringCons("-", formatReal2(fmt, mp, realToDigits(base, -d)));
  else
     return formatReal2(fmt, mp, realToDigits(base, d));
endfunction: formatReal

function String formatReal2(RealFormat fmt,
                            Maybe#(Integer) mp,
                            Tuple2#(List#(Integer), Integer) ds);
  Integer base = 10;
  match { .is, .e } = ds;
  let cs = map(integerToDigit, is);
  case (fmt)
     RFGeneric : begin
        let new_fmt = ( ((e < 0) || (e > 7)) ? RFExponent : RFFixed );
        return formatReal2(new_fmt, mp, ds);
     end // RFGeneric

     RFExponent : begin
        case (mp) matches
           tagged Invalid : begin
              let e_str = integerToString(e - 1);
              if (isNull(cs))
                 return error("formatReal: doFmt/RFExponent: null");
              else if (length(cs) == 1) begin
                 if (head(cs) == "0")
                    return "0.0e0";
                 else
                    return (stringCons(head(cs), ".0e") + e_str);
              end
              else begin
                 return (charListToString
                             (cons(head(cs), cons(".", tail(cs))))
                         + "e" + e_str);
              end
           end
           tagged Valid .dec : begin
              let dec2 = max(dec, 1);
              if (is == cons(0, nil))
                 return ("0." + charListToString(replicate(dec2,"0")) + "e0");
              else begin
                 match { .ei, .is2 } = roundTo(base, dec2 + 1, is);
                 let cs2 = map(integerToDigit, ( (ei > 0) ? init(is2) : is2 ));
                 return (charListToString
                             (cons(head(cs2), cons(".", tail(cs2))))
                         + "e" + integerToString(e - 1 + ei));
              end
           end
        endcase
     end // RFExponent

     RFFixed : begin
        function mk0(ls) = ((length(ls) == 0) ? cons("0",nil) : ls);
        case (mp) matches
           tagged Invalid :
              if (e <= 0)
                 return ("0." + charListToString(replicate(-e, "0")) +
                         charListToString(cs));
              else begin
                 function String fn(Integer n, List#(Char) s, List#(Char) rs);
                    if (n == 0)
                       return charListToString(append(mk0(reverse(s)),
                                                      cons(".", mk0(rs))));
                    else if (length(rs) == 0)
                       return fn(n-1, cons("0", s), nil);
                    else
                       return fn(n-1, cons(head(rs), s), tail(rs));
                 endfunction
                 return fn(e, nil, cs);
              end
           tagged Valid .dec : begin
              let dec2 = max(dec, 0);
              if (e >= 0) begin
                 match { .ei, .is2 } = roundTo(base, dec2 + e, is);
                 match { .ls, .rs }
                     = splitAt(e + ei, map(integerToDigit, is2));
                 return charListToString
                            (append(mk0(ls),
                                   (isNull(rs) ? nil : cons(".", rs))));
              end
              else begin
                 match { .ei, .is2 }
                     = roundTo(base, dec2, append(replicate(-e, 0), is));
                 let cs2 = map(integerToDigit,
                               ( (ei > 0) ? is2 : cons(0, is2) ));
                 return charListToString
                            (cons(head(cs2),
                                  (isNull(cs2) ? nil : cons(".", tail(cs2)))));
              end
           end
        endcase
     end // RFFixed
  endcase
endfunction: formatReal2

function Tuple2#(Integer, List#(Integer))
         roundTo(Integer base, Integer d, List#(Integer) is);
   Integer b2 = base / 2;

   function Tuple2#(Integer, List#(Integer))
            fn(Integer n, Bool e, List#(Integer) xs);
      if (isNull(xs))
         return tuple2(0, replicate(n, 0));
      else if (n == 0) begin
         let x = head(xs);
         function isZero(i) = (i == 0);
         if ((x == b2) && e && all(isZero, tail(xs)))
            return tuple2(0, nil);
         else
            return tuple2(((x >= b2) ? 1 : 0), nil);
      end
      else begin
         let i = head(xs);
         match { .c, .ds } = fn(n-1, even(i), tail(xs));
         let i2 = c + i;
         if (i2 == base)
            return tuple2(1, cons(0, ds));
         else
            return tuple2(0, cons(i2, ds));
      end
   endfunction

   let res = fn(d, True, is);
   case (tpl_1(res))
      0 : return res;
      1 : return tuple2(1, cons(1, tpl_2(res)));
      default : return error("roundTo: bad value");
   endcase
endfunction

function Tuple2#(List#(a), List#(a)) splitAt(Integer n, List#(a) xs);
   return tuple2(take(n, xs), drop(n, xs));
endfunction

function Bool even(Integer n);
   return ((n % 2) == 0);
endfunction

// -----

endpackage
