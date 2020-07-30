#!/usr/bin/perl
################################################################################

open (KEY128, ">key.vectors") || die;
open (DAT, ">dat.vectors") || die;

$cnt++;
print KEY128 "0x2b7e1516_28aed2a6_abf71588_09cf4f3c\n";
print DAT    "0x3243f6a8_885a308d_313198a2_e0370734\n";

$cnt++;
print KEY128 "0x00112233_44556677_8899aabb_ccddeeff\n";
print DAT    "0x00010203_04050607_08090a0b_0c0d0e0f\n";

$cnt++;
print KEY128 "0x00000000000000000000000000000000\n";
print DAT    "0x00000000000000000000000000000000\n";

$num = 256;

for (;;) {
    $dx = "1"x$num;
    while (length($dx) < 256) {
        $dx .= "0"x$num;
        last if (256 <= length($dx));
        $dx .= "1"x$num;
    }
        
    if ($dx =~ /^(\d{128})(\d{128})$/) {
        $cnt++;
        print KEY128 "0x" . toHex($1) . "\n";
        print DAT "0x" . toHex($2) . "\n";
    }

    $dx2 = $dx;
    $dx2 =~ tr/01/10/; # complement it

    if ($dx2 =~ /^(\d{128})(\d{128})$/) {
        $cnt++;
        print KEY128 "0x" . toHex($1) . "\n";
        print DAT "0x" . toHex($2) . "\n";
    }

    # split it up
    $num = int($num / 2);
    last if ($num == 0);
}

while ($cnt < 256) {
    $val = "";
    while (length($val) < 64) {
        $val .= sprintf ("%04x", (rand() * 65536));
    }
    if ($val =~ /^(\w{32})(\w{32})$/) {
        $cnt++;
        print KEY128 "0x$1\n";
        print DAT "0x$2\n";
    }
}

close(KEY128);
close(DAT);

############################################################
sub toHex {
    my ($in) = @_;
    my $h;
    
    while ($in ne "") {
        if    ($in =~ s/^0000//) { $h .= "0"; }
        elsif ($in =~ s/^0001//) { $h .= "1"; }
        elsif ($in =~ s/^0010//) { $h .= "2"; }
        elsif ($in =~ s/^0011//) { $h .= "3"; }
        elsif ($in =~ s/^0100//) { $h .= "4"; }
        elsif ($in =~ s/^0101//) { $h .= "5"; }
        elsif ($in =~ s/^0110//) { $h .= "6"; }
        elsif ($in =~ s/^0111//) { $h .= "7"; }
        elsif ($in =~ s/^1000//) { $h .= "8"; }
        elsif ($in =~ s/^1001//) { $h .= "9"; }
        elsif ($in =~ s/^1010//) { $h .= "a"; }
        elsif ($in =~ s/^1011//) { $h .= "b"; }
        elsif ($in =~ s/^1100//) { $h .= "c"; }
        elsif ($in =~ s/^1101//) { $h .= "d"; }
        elsif ($in =~ s/^1110//) { $h .= "e"; }
        elsif ($in =~ s/^1111//) { $h .= "f"; }
    }

    return $h;
}
