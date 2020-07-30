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
        sum: $r[2],
	   diff: $r[3],
	   mult: $r[4], 
	sum_127: $r[5],
    sum_126: $r[6],
     sum_96: $r[7],
     sum_95: $r[8],
     sum_94: $r[9],
     sum_64: $r[10],
     sum_63: $r[11],
     sum_62: $r[12],
     sum_32: $r[13],
     sum_31: $r[14],
     sum_30: $r[15],
      sum_1: $r[16],
      sum_0: $r[17],
   diff_127: $r[18],
   diff_126: $r[19],
    diff_96: $r[20],
    diff_95: $r[21],
    diff_94: $r[22],
    diff_64: $r[23],
    diff_63: $r[24],
    diff_62: $r[25],
    diff_32: $r[26],
    diff_31: $r[27],
    diff_30: $r[28],
     diff_1: $r[29],
     diff_0: $r[30],
   mult_127: $r[31],
   mult_126: $r[32],
    mult_96: $r[33],
    mult_95: $r[34],
    mult_94: $r[35],
    mult_64: $r[36],
    mult_63: $r[37],
    mult_62: $r[38],
    mult_32: $r[39],
    mult_31: $r[40],
    mult_30: $r[41],
     mult_1: $r[42],
     mult_0: $r[43],
    logical: $r[44]} ";
 
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
print "return check;\nendfunction\n";
print "\nendpackage : Vectors\n"; 


 
