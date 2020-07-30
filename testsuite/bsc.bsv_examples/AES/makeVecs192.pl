#!/usr/bin/perl
################################################################################

open (KEY192, ">key192.vectors") || die;
open (DAT128, ">dat192.vectors") || die;

$cnt++;
print KEY192 "0x000000000000000000000000000000000000000000000000\n";
print DAT128 "0x00000000000000000000000000000000\n";

$totalBits = 192 + 128;
$num = $totalBits;

for (;;) {
    $dx = "1"x$num;
    while (length($dx) < $totalBits) {
        $dx .= "0"x$num;
        last if ($totalBits <= length($dx));
        $dx .= "1"x$num;
    }
        
    if ($dx =~ /^(\d{192})(\d{128})$/) {
        $cnt++;
        print KEY192 "0x" . toHex($1) . "\n";
        print DAT128 "0x" . toHex($2) . "\n";
    }

    $dx2 = $dx;
    $dx2 =~ tr/01/10/; # complement it

    if ($dx2 =~ /^(\d{192})(\d{128})$/) {
        $cnt++;
        print KEY192 "0x" . toHex($1) . "\n";
        print DAT128 "0x" . toHex($2) . "\n";
    }

    # split it up
    $num = int($num / 2);
    last if ($num == 0);
}

while ($cnt < 256) {
    $val = "";
    while (length($val) < ($totalBits/4)) {
        $val .= sprintf ("%04x", (rand() * 65536));
    }
    if ($val =~ /^(\w{48})(\w{32})$/) {
        $cnt++;
        print KEY192 "0x$1\n";
        print DAT128 "0x$2\n";
    }
}

close(KEY192);
close(DAT128);

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
