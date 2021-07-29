#!/usr/bin/perl

$usage = "$0 <tex> <bsc-help>\n";

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
$inflagsection = 0;
$flagsectionfound = 0;
$inverbatim = 0;
$inflagdesc = 0;

%texflags = ();

#
# The following loop looks for a section defined like this:
#   \section{BSV compiler flags}
# Then it looks for any line starting with whitespace and then "-"
# and assumes that this is a flag description.  (This works.  For
# more robustness, we could check that it's in a verbatim block.)
# We stop looking when the start of the next section is reached:
#   \section
#
while (<TEXFILE>) {
    $linecount ++;
    if ($inflagsection) {
	if ($inverbatim) {
	    if (/^\s*(\-[^\s]+)\s+(.*\S)\s*$/) {
		$flag = $1;
		$descr = $2;
		if (exists $texflags{$flag}) {
		    #print "Ignoring example for flag $flag\n";
		} else {
		    $texflags{$flag} = $descr;
		    $inflagdesc = 1;
		    #print "$flag\n";
		}
	    }
	    elsif (/^\\end\{centerboxverbatim\}$/) {
		$inverbatim = 0;
	    }
	    elsif (/^\\section\{/) {
		print "Missed end of verbatim, line: ", $linecount;
		$inflagsection = 0;
		last;
	    } elsif ($inflagdesc && /^\s+(.*\S)\s*$/) {
		$addldesc = $1;
		$desc = $texflags{$flag};
		if ((substr $desc, -1) eq "-") {
		    $desc = "$desc$addldesc";
		} else {
		    $desc = "$desc $addldesc";
		}
		$texflags{$flag} = $desc;
	    } else {
		$inflagdesc = 0;
	    }
	} else {
	    if (/^\\begin\{centerboxverbatim\}$/) {
		$inverbatim = 1;
		$inflagdesc = 0;
	    }
	    elsif (/^\\end\{centerboxverbatim\}$/) {
		print "Missed begin of verbatim, line: ", $linecount;
	    }
	    elsif (/^\\section\{/) {
		$inflagsection = 0;
		last;
	    }
	}
    } else {
	if (/^\\section\{BSC flags\}/) {
	    $inflagsection = 1;
	    $flagsectionfound = 1;
	}
    }
}

close(TEXFILE);

# Did we find the flags section?
if (! $flagsectionfound) {
    print "Flag section not found\n";
    exit 1;
}

# Did the section end cleanly?
if ($inflagsection) {
    print "Unexpected end-of-file\n";
    exit 1;
}

#print "Line count: $linecount\n";
#print "Found " . keys(%texflags) . " flags\n";


if (!open(HELPFILE,$helpfile)) {
    print "Error opening $helpfile: $!\n";
    exit 1;
}

$linecount = 0;
%helpflags = ();

#
# Takes any line which starts with "-" and non-whitespace characters
#
while (<HELPFILE>) {
    $linecount ++;
    if (/^(\-[^\s]+)\s+(.*)$/) {
	$flag = $1;
	$descr = $2;
	$helpflags{$flag} = $descr;
	#print "$flag\n";
    }
}

close(HELPFILE);

print "The following are expected not to be found: -Ksize, -Hsize, -help\n";
print "\n";

# holds mismatched descriptions
%mismatches = ();

foreach $texflag (keys(%texflags)) {
    if (!exists($helpflags{$texflag})) {
	print "Missing from $helpfile: $texflag\n";
    } else {
	$hdescr = $helpflags{$texflag};
	$tdescr = $texflags{$texflag};
	#  remove extra whitespace
	$hdescr2 = $hdescr;
	$hdescr2 =~ s/\s+/ /g;
	$tdescr2 = $tdescr;
	$tdescr2 =~ s/\s+/ /g;
	if ($hdescr2 ne $tdescr2) {
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
