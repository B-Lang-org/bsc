#!/usr/bin/env bash

apt-get update

apt-get install -y \
    ccache \
    build-essential \
    tcsh \
    dejagnu \
    iverilog

if [ `lsb_release -rs` != 16.04 ]; then
    apt-get install -y lld
fi
