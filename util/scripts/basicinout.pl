#!/usr/bin/perl --
# -*-Perl-*-
################################################################################
################################################################################

my %RENAME_PORTS = ();
my %SIGNALS      = ();
my %PINS         = ();


foreach my $outfile (@ARGV) {
    # read the file
    next unless open(FILE, $outfile);
    my @lines = <FILE>;
    close(FILE);

    # Locate inout signals
    my $inmodule = 0;
    my $showedassigns = 0;
    my @newlines;
    foreach my $line (@lines) {
	if ($line =~ m/rename\:\s+(\S+)\=(\S+)/) {
	    $RENAME_PORTS{$1} = $2;
	} elsif ($line =~ m/^\s*module\s*[a-zA-Z0-9_\$]+\s*\(\s*\.(\S+)\(([a-zA-Z0-9_\$]+)\)/) {
	    $inmodule = 1;
	    $SIGNALS{$2} = $1;
	    $PINS{$1} = $2;
	    $line =~ s/\.(\S+)\(([a-zA-Z0-9_\$]+)\)/$1/;
	    push @newlines, $line;
	} elsif ($line =~ m/^\s*module\s+(\S+)\s*\(/) {
	    $inmodule = 1;
	    push @newlines, $line;
	} elsif ($line =~ m/^\s*\.(\S+)\(([a-zA-Z0-9_\$]+)\)/ && $inmodule) {
	    $SIGNALS{$2} = $1;
	    $PINS{$1} = $2;
	    $line =~ s/\.(\S+)\(([a-zA-Z0-9_\$]+)\)/$1/;
	    push @newlines, $line;
	} elsif ($line =~ m/\s*inout(.*?)\s*(\S+)\;/) {
	    my $signal = $2;
	    my $origsig = $2;

	    if (exists $SIGNALS{$signal}) {
		my $pin = $SIGNALS{$signal};
		$signal =~ s/\$/\\\$/g;
		$line =~ s/$signal/$pin/;
	    } else {
		print("Failed to locate signal=$signal in module port list (basicinout)!\nPlease report this error along with a verilog example to support\@bluespec.com\n\n");
		die;
	    }
	    push @newlines, $line;
	} elsif ($line =~ m/input/ && $inmodule) {
	    $inmodule = 0;
	    push @newlines, $line;
	} elsif ($line =~ m/\.(\S+)\(([a-zA-Z0-9\$_]+)\)/) {
	    my $signal = $2;
	    if (exists $SIGNALS{$signal}) {
		my $pin = $SIGNALS{$signal};
		$signal =~ s/\$/\\\$/g;
		$line =~ s/$signal/$pin/;
	    }
	    push @newlines, $line;
	} else {
	    push @newlines, $line;
	}
    }
    
    # Rename any signals that need renaming
    my @renamed_lines;
    foreach my $line (@newlines) {
	foreach my $signal (keys %RENAME_PORTS) {
	    my $replacement = $RENAME_PORTS{$signal};
	    if ($line =~ m/$signal/) {
		$line =~ s/([A-Za-z0-9_\$]*$signal)/$replacement/g;
	    }
	}
	push @renamed_lines, $line;
    }

    # write out the new version
    open(OFILE, ">${outfile}") or die("Could not create output file: $!\n");
    print OFILE @renamed_lines;
    close(OFILE);
}
1;
