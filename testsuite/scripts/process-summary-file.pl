#! perl -nw
use File::Basename;
BEGIN {
  $me=basename($0);
}
chomp;
$fn=$_;

#according to perldoc -f close, I don't need to keep closing FI
#because it automatically closes the previous one when I reuse a
#filehandle

unless (open FI,$fn) {
  print STDERR "$me: Error cannot open $fn\n";
  $error=1;
  next;
}
$marker=0;
while(<FI>){
  if (/^Running .*\.exp \.\.\.$/) {
    print "  $fn: ";
    print;
    $marker=1;
    last;
  }
}
unless ($marker) {
  print STDERR "$me: Error could not find test results in $fn\n";
  $error=1;
  next;
}

$marker=0;
while(<FI>){
  if (/^Running .*\.exp \.\.\.$/) {
    print "  $fn: ";
    print;
    next;
  }
  next if (/^(PASS|XFAIL)/);
  if (/=+ .* Summary\s*=+/){
    $marker=1;
    last;
  }
  #print if /\S/;  #skip whitespace  #this spews lots of garbage of multi-line PASS results
  if (/^(XPASS|FAIL|UNRESOLVED|UNTESTED|UNSUPPORTED|ERROR|WARNING|NOTE)/) {
    unless (/^(NOTE)/) {
      s/^/Error /; #this makes the tinderbox regexp search insert link anchors
      #see tinderbox's source code Error_Parse.pm
    }
    print;
  }
}
unless ($marker) {
  print STDERR "$me: Error could not find summary in $fn\n";
  $error=1;
  next;
}

while(<FI>){
  if (/(.+?)\s+(\d+)$/){
    #here we collect the strings like "# of expected passes"
    $summary{$1}+=$2;
  }
}

END{
  print "\n";
  for (sort keys %summary){
    printf("%-30s %9d\n",$_,$summary{$_});
  }
  exit(1) if $error;
}
