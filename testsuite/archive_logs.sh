#!/bin/sh

# localcheck produces bsc.log and bsc.sum in each directory; name them
# explicitly (even though '*.log' matches) so they are always captured
find . \
    -name bsc.log -o \
    -name bsc.sum -o \
    -name '*.log' -o \
    -name '*.out' -o \
    -name '*.diff-out' -o \
    -name '*.bsc-out' -o \
    -name '*.bsc-ccomp-out' -o \
    -name '*.bsc-vcomp-out' -o \
    -name '*.cxx-comp-out' -o \
    -name '*.bsc-sched-out' |
    tar zcf logs.tar.gz -T -
