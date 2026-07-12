#! perl -w
unless ($ENV{"RUN_TESTCASES_IN_ORDER_OF_TIME"}) {
  &simple_output;
}

unless(defined($ARGV[0]) and $ARGV[0]) {
  # if $ARGV[0] eq "" we choose to go the simple_output path rather than
  # try to run the null tool, looking only in directories beginning with
  # a period, which is silly
  &simple_output;  #does not return
}

#this path will only work from the top level, which is where this
#script is supposed to be called
$TIME_FILE='timing.txt';
unless (open FI,$TIME_FILE) {
  print STDERR "file $TIME_FILE not found, continuing without it...\n";
  #simply echo the input if no time file
  &simple_output;  #does not return
}


#output of
#find . -name time.out -exec cat '{}' \; | perl scripts/times.by-directory.pl

#print STDERR "reading time\n";
# A bad timing file must never abort list generation: an aborted (or
# empty) list would silently run ZERO tests, so fall back to the
# unsorted list instead.
while(<FI>){
  unless (/^\s*(\S+) (.+)/) {
    print STDERR "malformed line in $TIME_FILE, ignoring: $_";
    next;
  }
  $time{$2}=$1;
  push @alltimes,$1;
}
unless (@alltimes) {
  print STDERR "nothing found in timing file, continuing without it...\n";
  &simple_output;  #does not return
}
@alltimes=sort { $a <=> $b } @alltimes;

#if we do not know the actual time, guess the median
$median_time=$alltimes[int((scalar@alltimes)/2)];

#$median_time=9999; useful for debugging


#print STDERR "median_time $median_time\n";
open FI,"find . -name '*.exp' | grep '^\\./$ARGV[0]\\.' | "
  or die "finding exp files failed";

#print STDERR "reading lines\n";
while(<FI>){
  push @lines,$_
}

# From a test subdirectory the tool prefix matches nothing (paths are
# ./<dir>/... only at the top level); list everything under the current
# directory instead of silently producing an empty schedule.
unless (@lines) {
  print STDERR "no .exp files match ./$ARGV[0].*; listing all .exp files instead\n";
  # exclude the harness's own .exp files (site.exp, config/, lib/), which
  # live at the testsuite top level and are not tests
  open FI,"find . -name '*.exp' | grep -v -e '^\\./site\\.exp\$' -e '^\\./config/' -e '^\\./lib/' |"
    or die "finding exp files failed";
  while(<FI>){
    push @lines,$_
  }
}

#print STDERR "done ",scalar@lines,"\n";

#for(@lines){  print &get_time($_)," ",$_;}

@sorted=sort {&get_time($b) <=> &get_time($a)} @lines;

$skip_slowest=($ENV{"SKIP_SLOWEST_TESTCASES"} || 0);
for$i(0..$#sorted){
  for($sorted[$i]){
    if ($i<$skip_slowest){
      print STDERR "skipping slow testcase: $_";
    } else {
      print
    }
  }}


sub get_time {
  my $a=shift;
  #File::Spec would be a more portable way of doing the following regex
  if ($a =~ m!^\./(.+)/.*\.exp$!){
    #note that the regex intentionally does not match any exp files on
    #the top level.  If the user is calling from an internal directory
    #node, then no timing information is used.
    my $dir=$1;
    if(defined($time{$dir})){
      $time{$dir}
    } else { $median_time }
  } else { $median_time } }


sub simple_output {
  if ($ARGV[0]){
    my @found = `find . -name '*.exp' | grep '^\\./$ARGV[0]\\.'`;
    # see the subdirectory note above: an empty filtered list means we
    # are not at the top level, so fall back to everything -- excluding
    # the harness's own .exp files (site.exp, config/, lib/)
    @found = `find . -name '*.exp' | grep -v -e '^\\./site\\.exp\$' -e '^\\./config/' -e '^\\./lib/'` unless @found;
    print @found;
    exit 0;
  } else {
    exec 'find','.','-name','*.exp';
  }
}
