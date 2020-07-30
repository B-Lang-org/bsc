#!/usr/bin/env bash

curl -Os https://www.accellera.org/images/downloads/standards/systemc/systemc-2.3.3.tar.gz

tar zxf systemc-2.3.3.tar.gz
cd systemc-2.3.3
./configure --prefix=$HOME/systemc
make -j3
make install
