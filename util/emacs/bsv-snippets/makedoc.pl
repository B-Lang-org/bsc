#!/usr/bin/perl

foreach $file (sort <bsv-mode/*>) {
    if ($file =~ (/^bsv-mode\/(\w+)/)) {
        $cmd = $1;

        if (open(FP,$file)) {
            while (<FP>) {
                if (s/^\#name\s*:\s*//) {
                    chop($_);
                    printf "%-80s %20s =>\n", $_, $cmd;
                    # $arr{$cmd} .= "   $_";
                    last;
                }
            }
            close(FP);
        }
    }
}

#foreach $cmd (sort keys %arr) {
#    printf "%-60s %20s =>\n", $arr{$cmd}, $cmd;
    # print "\n$cmd =>\n";
    # print $arr{$cmd};
#}
