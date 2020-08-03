#!/usr/bin/env bash

apt-get update

apt-get install -y \
    ccache \
    build-essential \
    tcsh \
    dejagnu \
    iverilog

REL=$(lsb_release -rs | tr -d .)
if [ $REL -ge 1804 ]; then
    apt-get install -y lld
fi

if [ $REL -ge 1910 ]; then
    apt-get install -y libsystemc-dev
fi
