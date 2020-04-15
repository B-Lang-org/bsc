#!/usr/bin/env bash

brew install autoconf cabal-install fontconfig gperf icarus-verilog pkg-config && \
    cabal update && \
    cabal v1-install old-time regex-compat split syb
