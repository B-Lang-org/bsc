#!/usr/bin/env bash

apt-get update

apt-get install -y \
    ccache \
    build-essential \
    tcsh \
    dejagnu \
    iverilog
