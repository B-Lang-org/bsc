#!/usr/bin/perl

$usage = "$0 <tex> <sim-help>\n";

if (@ARGV != 2) {
    print $usage;
    exit 1;
}

$texfile = $ARGV[0];
$helpfile = $ARGV[1];

if (!open(TEXFILE,$texfile)) {
    print "Error opening $texfile: $!\n";
    exit 1;
}

$linecount = 0;
$insimsection = 0;
$simsectionfound = 0;
$inverbsection = 0;
$verbsectionfound = 0;

%texflags = ();
@invalidtex = ();

#
# The following loop looks for a section defined like this:
#   \subsection{Bluesim simulation flags}
# Then it looks for the first verbatim block and grabs the text,
# assuming that it is verbatim from the sim binary help output
#
while (<TEXFILE>) {
    $linecount ++;
    if ($insimsection) {
	if ($inverbsection) {
	    if (/^\\end\{centerboxverbatim\}\s+$/) {
		$inverbsection = 0;
		#print "End of verb section: $_";
		last;
	    } elsif (/^\s*((\-|\+)[^\s]+)\s+(.*)$/) {
		$flag = $1;
		$descr = $3;
		$texflags{$flag} = $descr;
	    } else {
		push @invalidtex, $_;
	    }
	} else {
	    if (/\\begin\{centerboxverbatim\}\s*$/) {
		$inverbsection = 1;
		$verbsectionfound = 1;
		#print "Start of verb section: $_";
	    } elsif (/^\\(sub)*section\{/) {
		$insimsection = 0;
		last;
	    }
	}
    } else {
	if (/^\\subsection\{Bluesim simulation flags\}/) {
	    $insimsection = 1;
	    $simsectionfound = 1;
	}
    }
}

close(TEXFILE);

# Did we find the sim flags subsection?
if (! $simsectionfound) {
    print "Simulation flag section not found\n";
    exit 1;
}

# Did we find the verbatim block?
if (! $verbsectionfound) {
    print "Verbatim block containing Simulation flags not found\n";
    exit 1;
}

# Did the verbatim block end cleanly?
if ($inverbsection) {
    print "Unexpected end-of-file\n";
    exit 1;
}

# Were there lines which didn't match the expected flag format?
if (@invalidtex > 0) {
    print "The following lines in the verbatim block did not parse:\n";
    print @invalidtex;
    exit 1;
}


if (!open(HELPFILE,$helpfile)) {
    print "Error opening $helpfile: $!\n";
    exit 1;
}

$linecount = 0;
%helpflags = ();

#
# Takes any line which starts with whitespace, then "-"
#
while (<HELPFILE>) {
    $linecount ++;
    if (/^\s+((\-|\+)[^\s]+)\s+(.*)$/) {
	$flag = $1;
	$descr = $3;
	$helpflags{$flag} = $descr;
	#print "$flag\n";
    }
}

close(HELPFILE);

# holds mismatched descriptions
%mismatches = ();

foreach $texflag (keys(%texflags)) {
    if (!exists($helpflags{$texflag})) {
	print "Missing from $helpfile: $texflag\n";
    } else {
	$hdescr = $helpflags{$texflag};
	$tdescr = $texflags{$texflag};
	if ($hdescr ne $tdescr) {
	    $mismatches{$texflag} = "  $hdescr\n  $tdescr\n";
	}
    }
}

foreach $helpflag (keys(%helpflags)) {
    if (!exists($texflags{$helpflag})) {
	print "Missing from $texfile: $helpflag\n";
    } else {
	$hdescr = $helpflags{$texflag};
	$tdescr = $texflags{$texflag};
	if ($hdescr ne $tdescr) {
	    $mismatches{$texflag} = "  $hdescr\n  $tdescr\n";
	}
    }
}

foreach $flag (keys(%mismatches)) {
    print "Descriptions differ: $flag\n" . $mismatches{$flag};
}

exit 0;
