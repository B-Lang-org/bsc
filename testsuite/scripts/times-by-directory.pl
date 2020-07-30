#! perl -nlw
next if /^Command exited with non-zero status/;
next if /^Command terminated/;
die $_ unless m!^check_.* (.*), (.*), (.*), .*testsuite/(.*)!;
$cpu{$4}+=$2;   #cpu
END{
  for (sort {$cpu{$b} <=> $cpu{$a}} (keys %cpu)) {
    printf '%8.1f %s'."\n", $cpu{$_}, $_;
  }
}
