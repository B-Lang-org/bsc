#!/bin/bash
set -eu -o pipefail

BSC=../../inst/bin/bsc
OUT=$PWD

for i in  \
Empty.bs \
ArrayExtra.bs \
ListExtra.bs \
Json.bs \
VerilogRepr.bs \
MaybeExtra.bs \
Rules.bs \
VectorExtra.bs \
Linkable.bs \
PreludeExtra.bs \
RegExtra.bs \
Test.bs \
Grid.bs \
GridTest.bs \
; do
    $BSC -p %/Libraries -vsearch %/Verilog -bdir $OUT -simdir $OUT -vdir $OUT -info-dir $OUT -fdir $OUT -no-show-timestamps -suppress-warnings T0127:S0080 -sim -q $i
done

# This is the slow command which gets slower as the W and H numbers in GridTest.bs increase.
time $BSC -p %/Libraries -vsearch %/Verilog -bdir $OUT -simdir $OUT -vdir $OUT -info-dir $OUT -fdir $OUT -no-show-timestamps -verilog -g mkGridTest_Big -g mkGridTest_Elem -g mkGridTest_Small -g mkGridTest -suppress-warnings G0020:S0080 -q GridTest.bs
