#!/usr/bin/perl --
# -*-Perl-*-
# A sample -verilog-filter: shorten BSC's -keep-fires rule-signal
# prefixes (CAN_FIRE_ -> CF_, WILL_FIRE_ -> WF_) in the generated
# Verilog.  bsc invokes the filter with the generated file as its
# argument, and the filter rewrites the file in place.

foreach my $outfile (@ARGV) {
    next unless open(FILE, $outfile);
    my @lines = <FILE>;
    close(FILE);

    foreach my $line (@lines) {
        $line =~ s/\bCAN_FIRE_/CF_/g;
        $line =~ s/\bWILL_FIRE_/WF_/g;
    }

    next unless open(FILE, ">", $outfile);
    print FILE @lines;
    close(FILE);
}
