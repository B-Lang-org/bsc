#! perl -w

use utf8;  #for · (centerdot) in the regular expression

$seen_rules = 0;
while(<>){
  if (/imod rules/) {
    $seen_rules = 1;
    last;
  }
}
if ($seen_rules == 0) {
  die "IModule rules not found\n";
}

#first make into tokens
$seen_interface = 0;
while(<>) {
  if (/imod interface/) {
    $seen_interface = 1;
    last;
  }
  s/v(\d+)__\w+/v$1/g;
  s/PrimBNot\s*/NOT/g;
  s/PrimBAnd/ /g;
  s/[()]/ /g;
  s/·Prelude\.PrimAction/ /g;
  s/Prelude.\$display#\d+/ /g;
  s/^\s*RL_unnamed.*//;
  s/^\s*\"[_TF]+\":$//;
  @F=split;
  push @tokens,@F
}
if ($seen_interface == 0) {
  die "IModule interface not found\n";
}

$first=1;
$when_in=0;

#parse: when (clauses..) ==> statement

for(@tokens){
  if ($_ eq "when") {
    $when_in=1;
    unless ($first) {
      &process;
    }
    undef @ww;
    next;
  } elsif ($_ eq "==>") {
    $when_in=0;
    $command=" $_";
    next;
  }
  if ($when_in) {
    push @ww,$_;
  } else {
    $command .= " $_";
  }
  $first=0;
}
sub process {
  #using global variables @ww and $command

  #canonical order of clauses by sorting
  @ww=sort @ww;
  $pre="when";
  for$a(@ww){
    $pre.=" $a";
  }
  push @lines,$pre.$command."\n";
}

# canonical order of rules by sorting
print for (sort @lines);
