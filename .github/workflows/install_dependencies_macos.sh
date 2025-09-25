#!/usr/bin/env bash

if [ "${BREW_UPDATE}" != "false" ]; then
    brew update
fi

# ccache is not required to build bsc, but we use it in build.yml to improve
# the build performance by caching C++ obj files across multiple builds.
brew install \
  autoconf \
  ccache \
  gperf \
  icarus-verilog \
  pkg-config
