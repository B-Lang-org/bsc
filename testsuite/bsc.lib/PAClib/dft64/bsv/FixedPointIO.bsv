// A package for reading and writing Fixedpoint valued to unix files during simulation runtime
// Uses FixedPointIO.c as the underlying import C functions

package FixedPointIO;

import FixedPoint :: *;
import Complex::*;
import Vector::*;

export openwritefile, openreadfile, openappendfile;
export fxptReadFile, fxptWriteFile, fxptWriteString, fxptWriteNewLine;
export readPoints, writeCmplx, writePoints;

import "BDPI" openreadfile            = function ActionValue#(int) openreadfile (String filename);
import "BDPI" openwritefile            = function ActionValue#(int) openwritefile (String filename);
import "BDPI" openappendfile            = function ActionValue#(int) openappendfile (String filename);

import "BDPI" readFixedPoint_i_f  = function ActionValue#(Maybe#(Bit#(31))) readFixedPoint_RAW(int isize, int fsize);

function ActionValue# (Maybe# (FixedPoint# (i,f))) fxptReadFile()
   provisos(Add#(TAdd#(i,f), _xxx, 31));
   actionvalue
      Maybe#(Bit#(31)) d <- readFixedPoint_RAW(fromInteger(valueOf(i)), fromInteger(valueOf(f)));
      Maybe# (FixedPoint# (i,f)) ret = tagged Invalid;
      if (d matches tagged Valid .b) begin
         ret = tagged Valid (unpack( truncate(b)));
      end
      return ret;
   endactionvalue
endfunction


import "BDPI" writeFixedPoint_i_f  = function Action writeFixedPoint_RAW(int isize, int fsize, Bit#(32) din);

function Action  fxptWriteFile(FixedPoint# (i,f) din)
   provisos(Add#(TAdd#(i,f), _xxx, 32));
   return
   writeFixedPoint_RAW(fromInteger(valueOf(i)), fromInteger(valueOf(f)), signExtend(pack(din)));
endfunction

import "BDPI" writeString = function Action fxptWriteString (String str);
import "BDPI" writeNewLine = function Action fxptWriteNewLine ();



// Write functions
function Action writeCmplx (Complex#( FixedPoint #(i,f)) d)
   provisos(Add#(TAdd#(i,f), _xxx, 32)
            );
   return (action
      fxptWriteString ("(");
      fxptWriteFile(d.rel);
      fxptWriteString (", ");
      fxptWriteFile(d.img);
      fxptWriteString (")");
      fxptWriteNewLine;
   endaction);
endfunction

function Action writePoints (Vector# (n, Complex#( FixedPoint #(i,f))) vin)
   provisos(Add#(TAdd#(i,f), _xxx, 32)
            );
   return joinActions(map(writeCmplx, vin));
endfunction

// Read the next data set from the file
// return invalid if there is a read error
function ActionValue# (Maybe# (Vector#(n, Complex# (FixedPoint# (i,f))))) readPoints ()
provisos ( Min#(i, 1, 1)
          ,Add#(TAdd#(i,f),_xxx,31)
          ,Alias#(fp, FixedPoint#(i,f))
          ,Alias#(mfp, Maybe#(fp))
          ,Alias#(cfp, Complex#(fp))
          ,Div#(TMul#(n,2),2,n)
          );
   actionvalue
      Maybe# (Vector#(n,cfp)) res = tagged Invalid;

      ActionValue#(mfp) reader = fxptReadFile;
      Vector#( TMul#(n,2), mfp)  mdoubles <- replicateM(reader);

      Bool valid = all (isValid, mdoubles);
      if (valid) begin
         Vector#(TMul#(n,2), fp) doubles = map (fromMaybe(0), mdoubles);
         res = tagged Valid (mapPairs (cmplx
                                      ,error("Should never occur")
                                      ,doubles)
                             );
         end
      return res;
   endactionvalue
endfunction

endpackage
