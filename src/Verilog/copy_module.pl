#!/usr/bin/perl

die "Usage: $0 <srcname> <dstname>\n" if @ARGV != 2;

$srcmod = shift(@ARGV);
$dstmod = shift(@ARGV);

open(SRCIN, "${srcmod}.v")   || die "can't read ${srcmod}.v: $!";
open(DSTOUT, ">${dstmod}.v") || die "can't write ${dstmod}.v: $!";

while ($line = <SRCIN>) {
    $line =~ s/^(\s*module\s*)$srcmod(\s*\()/$1$dstmod$2/;
    $line =~ s/^(\s*endmodule\s*\/\/\s*)$srcmod(\s*)$/$1$dstmod$2/;
    print DSTOUT $line;
}

close DSTOUT;
close SRCIN;

#print STDOUT "Module $dstmod created from $srcmod.\n"

