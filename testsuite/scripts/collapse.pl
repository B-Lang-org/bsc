#! perl -nw
BEGIN{
  $total=0;
}
#global runtest time.out has a weird format
next unless ($n,$c,$b,$a) = m!^([^,]*), ([^,]*), ([^,]*), ([^,]*)!;
die "unexpected time format $_" unless $n=~s/^check_//;
$x{$n}+=(1*$a);
$m[0]+=(1*$a);
$y{$n}+=$b;
$m[1]+=$b;
$z{$n}+=$c;
$m[2]+=$c;
$count{$n}++;
$total++;
END{
#default sort by CPU
print << 'EOF';

                === Timing by Category ===

  WALLCLOCK sec        CPU sec      SYSTEM sec   #calls  CATEGORY
EOF
#   0.05 (  0.0%)     0.00 (  0.0%)     0.00 (  0.0%)    5  m4_process

for (sort {$y{$a}<=>$y{$b}} keys %y){
&printline($x{$_},$y{$_},$z{$_},$count{$_},$_);
#printf "$format $format $format %s\n",$x{$_},$y{$_},$z{$_},$_;
}
#printf "$format $format $format TOTAL\n",$ma,$mb,$mc;
&printline($m[0],$m[1],$m[2],$total,"TOTAL");
}
sub printline {
  for(0..2){
    unless ($m[$_]) {$m[$_]=0.001}  #avoid division by zero
    printf '%8.1f (%3.0f%%) ',$_[$_],$_[$_]/$m[$_]*100;
  }
  printf "  %5d  %s\n",$_[3],$_[4];
}
