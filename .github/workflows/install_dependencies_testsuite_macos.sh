#!/usr/bin/env bash

if [ "${BREW_UPDATE}" != "false" ]; then
    brew update
fi

brew install \
  ccache \
  deja-gnu \
  icarus-verilog \
  systemc
