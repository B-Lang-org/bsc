#!/usr/bin/env bash

apt-get update

# gtkwave provides fst2vcd, which enables the FST waveform tests'
# conversion checks (the tests skip those checks when it is absent).
# zlib1g-dev provides the libz.so that Bluesim test executables link
# against (the tests link with -dump-formats vcd,fst to check
# waveform dumping in both formats).
apt-get install -y \
    ccache \
    build-essential \
    lld \
    tcsh \
    dejagnu \
    gtkwave \
    iverilog \
    libsystemc-dev \
    zlib1g-dev
