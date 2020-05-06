#!/usr/bin/env bash

# ccache is not required to buid bsc, but we use it in build.yml to improve
# the build performance by caching C++ obj files across multiple builds.
brew install ccache autoconf cabal-install gperf icarus-verilog pkg-config && \
    cabal update && \
    cabal v1-install old-time regex-compat split syb
