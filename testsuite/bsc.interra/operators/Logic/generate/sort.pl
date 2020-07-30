#! /usr/bin/perl

@list = `cat $ARGV[0]| grep -v x`;

@output = "";

$index = 0;

foreach $l (@list)
{
    next if ($l =~ /Error/ );

 @r = split(" ",$l);
 $output[$index] = 
 "Inputs {a: $r[0],
          b: $r[1],
         bOr: $r[2],
     bOr_127: $r[3],
     bOr_126: $r[4],
      bOr_96: $r[5],
      bOr_95: $r[6],
      bOr_94: $r[7],
      bOr_64: $r[8],
      bOr_63: $r[9],
      bOr_62: $r[10],
      bOr_32: $r[11],
      bOr_31: $r[12],
      bOr_30: $r[13],
       bOr_1: $r[14],
       bOr_0: $r[15],
        bAnd: $r[16],
    bAnd_127: $r[17],
    bAnd_126: $r[18],
     bAnd_96: $r[19],
     bAnd_95: $r[20],
     bAnd_94: $r[21],
     bAnd_64: $r[22],
     bAnd_63: $r[23],
     bAnd_62: $r[24],
     bAnd_32: $r[25],
     bAnd_31: $r[26],
     bAnd_30: $r[27],
      bAnd_1: $r[28],
      bAnd_0: $r[29],
       bInv: $r[30],
   bInv_127: $r[31],
   bInv_126: $r[32],
    bInv_96: $r[33],
    bInv_95: $r[34],
    bInv_94: $r[35],
    bInv_64: $r[36],
    bInv_63: $r[37],
    bInv_62: $r[38],
    bInv_32: $r[39],
    bInv_31: $r[40],
    bInv_30: $r[41],
     bInv_1: $r[42],
     bInv_0: $r[43],
        bXor: $r[44],
    bXor_127: $r[45],
    bXor_126: $r[46],
     bXor_96: $r[47],
     bXor_95: $r[48],
     bXor_94: $r[49],
     bXor_64: $r[50],
     bXor_63: $r[51],
     bXor_62: $r[52],
     bXor_32: $r[53],
     bXor_31: $r[54],
     bXor_30: $r[55],
      bXor_1: $r[56],
      bXor_0: $r[57],
       bXnor: $r[58],
   bXnor_127: $r[59],
   bXnor_126: $r[60],
    bXnor_96: $r[61],
    bXnor_95: $r[62],
    bXnor_94: $r[63],
    bXnor_64: $r[64],
    bXnor_63: $r[65],
    bXnor_62: $r[66],
    bXnor_32: $r[67],
    bXnor_31: $r[68],
    bXnor_30: $r[69],
     bXnor_1: $r[70],
     bXnor_0: $r[71]
	   } ";
 
 $index++;
 }


 for ($i=0;$i<$#output;$i++)
{
 $text = "$text\ncheck[$i] = $output[$i];"
}
 
print "package Vectors;\n\n"; 
print "import Input::*;\n\n"; 
print "import Vector::*;\n\n";
print "function Vector#(10,Inputs) get_vector();\n";
print "Vector#(10,Inputs) check = newVector;\n";
print "  $text\n";
print "\nreturn check;\nendfunction\n";
print "\nendpackage : Vectors\n"; 



