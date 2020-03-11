#!/usr/bin/env bash

brew install cabal-install fontconfig gperf icarus-verilog pkg-config && \
    cabal update && \
    cabal v1-install old-time regex-compat split syb
