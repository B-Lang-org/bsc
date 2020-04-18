#!/usr/bin/env bash

set -euo pipefail

apt-get update
apt-get install -y \
    autoconf \
    bison \
    build-essential \
    flex \
    ghc \
    git \
    gperf \
    iverilog \
    libghc-old-time-dev \
    libghc-regex-compat-dev \
    libghc-syb-dev \
    libghc-split-dev \
    tcl-dev
