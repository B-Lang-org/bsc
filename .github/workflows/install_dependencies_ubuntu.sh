#!/usr/bin/env bash
sudo apt-get update

# Install the latest version of itcl/itk -- itk3-dev or tk-itk4-dev.
# NB itk depends on itcl, tk and tcl, so no need to install those separately
ITK_DEV_PKG=$(apt-cache search -n '^(tk-)?itk[0-9]-dev' | cut -f1 -d' ' | sort | tail -1)

sudo apt-get install -y \
  autoconf \
  bison \
  build-essential \
  flex \
  ghc \
  git \
  gperf \
  iverilog \
  $ITK_DEV_PKG \
  libfontconfig1-dev \
  libghc-old-time-dev \
  libghc-regex-compat-dev \
  libghc-syb-dev \
  libghc-split-dev \
  libx11-dev \
  libxft-dev \
  xvfb
