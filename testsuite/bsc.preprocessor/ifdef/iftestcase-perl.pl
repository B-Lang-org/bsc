#! perl -nw
if (/====/) {
  &process;
  next;
}
if (/execution (\d+) (.*)/) {
  die unless $1==@execution;
  if($2 eq "True"){
    push @execution,1;
  } elsif ($2 eq "False"){
    push @execution,0;
  } else {
    die;
  }
}
else {
  push @lines,$_;
  if (/placeholder(\d+)/){
    die "$1 ",scalar@place unless $1==@place;
    push @place,"";
  }
}
sub process {
  $fc++;
  $fn=sprintf("%04d",$fc);
  open FO,">ifdef$fn.bsv" or die;
  #begin goes in last consecutive true
  #for($i=0;$i<@execution;$i++){
  #  last unless $execution[$i];
  #}
  #$place[$i-1]="module test();\n";

  my $lasttrue=0;
  for($i=0;$i<@execution;$i++){
    if ($execution[$i]){
      $place[$i].="Reg#(Bit#(8)) r$i<-mkReg(0);\n";
      $lasttrue=$i
    }
    else {
      $place[$i].="badcode$i\n";
    }
  }

  #end goes in last true
  $place[$lasttrue].="endmodule\n";

  print FO "module test();\n";
  for$i(0..$#lines){
    for($lines[$i]){
      if (/placeholder(\d+)/){
        print FO $place[$1];
      } else{print FO}}
  }
  print "=== $fn\n";
  undef @lines;
  undef @place;
  undef @execution;
  close FO;
}
