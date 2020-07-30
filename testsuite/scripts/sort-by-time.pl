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
open FI,$TIME_FILE or die;
unless (open FI,$TIME_FILE) {
  print STDERR "file $TIME_FILE not found, continuing without it...\n";
  #simply echo the input if no time file
  &simple_output;  #does not return
}


#output of
#find . -name time.out -exec cat '{}' \; | perl scripts/times.by-directory.pl

#print STDERR "reading time\n";
while(<FI>){
  die "time file format error $_" unless /^\s*(\S+) (.+)/;
  $time{$2}=$1;
  push @alltimes,$1;
}
die "nothing found in timing file" unless @alltimes;
@alltimes=sort @alltimes;

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
    exec "find . -name '*.exp' | grep '^\\./$ARGV[0]\\.'";
  } else {
    exec 'find','.','-name','*.exp';
  }
}
