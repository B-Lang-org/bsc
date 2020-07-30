#! perl -nlw
die "ERROR: does not seem like a full path to a .exp file: $_"
  unless ($dir,$fn)=m!(.*)/(.*\.exp)$!;
if (defined $seen{$dir}) {
  die "ERROR: two .exp files in the same directory.  $seen{$dir} and $fn are both in $dir";
}
$seen{$dir}=$fn;
