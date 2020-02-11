#!/bin/bash

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
    libfontconfig1-dev \
    libghc-old-time-dev \
    libghc-regex-compat-dev \
    libghc-syb-dev \
    libx11-dev \
    libxft-dev
