#!/bin/sh

find . \
    -name bsc.log -o \
    -name bsc.sum -o \
    -name '*.diff-out' -o \
    -name '*.bsc-out' -o \
    -name '*.bsc-ccomp-out' -o \
    -name '*.bsc-vcomp-out' -o \
    -name '*.cxx-comp-out' -o \
    -name '*.bsc-sched-out' |
    tar zcf logs.tar.gz -T -

