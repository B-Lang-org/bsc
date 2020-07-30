#!/bin/csh
# script to find failures after parallel build
foreach i (`find . -name "*.sum"`)
  grep -l -e "^FAIL" $i
end
