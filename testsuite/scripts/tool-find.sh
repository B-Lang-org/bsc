#! /bin/bash

#Note that running without an argument at the top level of the testsuite will
#cause very bad things, e.g., try to run unix.exp and site.exp as testscripts.
#At the top level, you want to specify "bsc" (or "ese", etc." as an argument to
#this script

if [ -z $1 ]
then find . -name '*.exp'
else find . -name '*.exp' | grep '^\./'"$1"'\.' | perl scripts/sort-by-time.pl
fi
