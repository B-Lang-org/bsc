#!/usr/bin/env bash

# ccache is not required to build bsc, but we use it in build.yml to improve
# the build performance by caching C++ obj files across multiple builds.
brew install \
  ccache \
  autoconf \
  gperf \
  icarus-verilog \
  pkg-config
