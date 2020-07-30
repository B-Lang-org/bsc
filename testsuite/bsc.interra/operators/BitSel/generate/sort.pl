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
 ex_crs_1_1: $r[1],
 ex_crs_1_2: $r[2],
 ex_crs_1_3: $r[3],
 ex_crs_2_1: $r[4],
 ex_crs_2_2: $r[5],
   ex_crs_3: $r[6],
 ex_tch_1_1: $r[7],
 ex_tch_1_2: $r[8],
 ex_tch_1_3: $r[9],
 ex_tch_1_4: $r[10],
 ex_tch_1_5: $r[11],
 ex_tch_1_6: $r[12],
 ex_tch_2_1: $r[13],
 ex_tch_2_2: $r[14],
 ex_tch_2_3: $r[15],
 ex_tch_2_4: $r[16],
 ex_tch_2_5: $r[17],
 ex_tch_2_6: $r[18],
  con_crs_1: $r[19],
  con_crs_2: $r[20],
  con_crs_3: $r[21],
con_tch_1_1: $r[22],
con_tch_1_2: $r[23],
con_tch_1_3: $r[24],
con_tch_1_4: $r[25]}";

 
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

