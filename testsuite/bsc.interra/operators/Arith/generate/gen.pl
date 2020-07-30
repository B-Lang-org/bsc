#! /usr/bin/perl

$seed = srand ();
$seed = 224530 ;
@list_top = `cat top_code`;
@list_bot = `cat bot_code`;

print "@list_top\n";
$ran = rand()*10000000 % 300000;
print "  integer seed = $ran ;\n";
print "@list_bot\n";

