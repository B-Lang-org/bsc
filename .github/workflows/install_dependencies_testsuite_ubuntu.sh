#!/usr/bin/env bash

apt-get update

apt-get install -y \
    ccache \
    build-essential \
    lld \
    tcsh \
    dejagnu \
    iverilog \
    libsystemc-dev
