#!/usr/bin/env bash

# ccache is not required to build bsc, but we use it in build.yml to improve
# the build performance by caching C++ obj files across multiple builds.
brew install \
  autoconf \
  gperf \
  icarus-verilog \
  pkg-config

# Hold ccache back to 4.3_1, to avoid bug introduced in 4.4
TAP=b-lang/homebrew-old
brew tap-new $TAP
brew extract --version 4.3 homebrew/core/ccache $TAP
brew install $TAP/ccache@4.3
