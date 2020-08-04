#!/bin/sh

find -E . \
    -name bsc.log -o \
    -name bsc.sum -o \
    -regex '.*\.(diff|bsc|bsc-ccomp|bsc-vcomp|bsc-sched)-out' |
    tar zcf logs.tar.gz -T -

