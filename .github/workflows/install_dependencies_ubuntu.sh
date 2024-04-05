#!/usr/bin/env bash

apt-get update

# ccache is not required to buid bsc, but we use it in build.yml to improve
# the build performance by caching C++ obj files across multiple builds.
apt-get install -y \
  ccache \
  autoconf \
  bison \
  build-essential \
  flex \
  git \
  gperf \
  iverilog \
  tcl-dev
