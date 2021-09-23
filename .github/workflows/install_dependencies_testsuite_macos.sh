#!/usr/bin/env bash

brew install \
  deja-gnu \
  icarus-verilog \
  systemc

# Hold ccache back to 4.3_1, to avoid bug introduced in 4.4
TAP=b-lang/homebrew-old
brew tap-new $TAP
brew extract --version 4.3 homebrew/core/ccache $TAP
brew install $TAP/ccache@4.3
