#!/usr/bin/perl

$i = 0;

while (<>) {
    s/\s*$//g;
    s/0x/8\'h/g;
    printf "$i: return $_;\n";
    $i++;
}
