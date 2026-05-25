#!/usr/bin/env bash
# End-to-end driver for the wiretypemap <-> VCD correlation check.
# Runs correlation for two distinct modules:
#   1. mkWireTypes (rich types: struct/union/enum/Maybe/Vector,
#      plus polymorphic primitives: Reg, FIFOF, BRAM, SyncFIFO, CReg5)
#   2. mkSplitPortsTest (sub-interface with DeepSplit-collapsed arg)

set -euo pipefail

cd "$(dirname "$0")"

BSC=${BSC:-/home/ravi/bluespec/claude/bsc/inst/bin/bsc}
BLUETCL=${BLUETCL:-/home/ravi/bluespec/claude/bsc/inst/bin/bluetcl}

rm -rf bo veri sim build.log
mkdir -p bo veri sim

# Build both designs once
{
  echo "[wt] Compiling WireTypesSim to Verilog + Bluesim..."
  $BSC -bdir bo -verilog -vdir veri -elab -u -g sysWireTypeTest WireTypesSim.bsv
  $BSC -bdir bo -verilog -vdir veri -e sysWireTypeTest -o veri/sysWireTypeTest
  $BSC -bdir bo -sim     -simdir sim -elab -u -g sysWireTypeTest WireTypesSim.bsv
  $BSC -bdir bo -sim     -simdir sim -e sysWireTypeTest -o sim/sysWireTypeTest

  echo "[sp] Compiling SplitPortsSim to Verilog + Bluesim..."
  $BSC -bdir bo -verilog -vdir veri -elab -u -g sysSplitPortsTest SplitPortsSim.bsv
  $BSC -bdir bo -verilog -vdir veri -e sysSplitPortsTest -o veri/sysSplitPortsTest
  $BSC -bdir bo -sim     -simdir sim -elab -u -g sysSplitPortsTest SplitPortsSim.bsv
  $BSC -bdir bo -sim     -simdir sim -e sysSplitPortsTest -o sim/sysSplitPortsTest

  echo "[wt] Running WireTypes sims..."
  (cd veri && ./sysWireTypeTest +bscvcd 2>&1) > veri/wt_sim.log || true
  mv veri/dump.vcd veri/wt.vcd
  (cd sim && ./sysWireTypeTest -V wt.vcd 2>&1) > sim/wt_sim.log || true

  echo "[sp] Running SplitPorts sims..."
  (cd veri && ./sysSplitPortsTest +bscvcd 2>&1) > veri/sp_sim.log || true
  mv veri/dump.vcd veri/sp.vcd
  (cd sim && ./sysSplitPortsTest -V sp.vcd 2>&1) > sim/sp_sim.log || true
} > build.log 2>&1

# Run correlation for mkWireTypes + its leaf instances. mkPixelStash is
# separately synthesized and instantiated twice (leafA, leafB), so we
# correlate the same wiretypemap against both sub-scopes -- demonstrating
# that one wiretypemap query covers every instance of that module.
TOP_NAME=sysWireTypeTest \
  VERI_VCD="$(pwd)/veri/wt.vcd" \
  SIM_VCD="$(pwd)/sim/wt.vcd" \
  MOD_AT_LIST="mkWireTypes main.top.dut mkPixelStash main.top.dut.leafA mkPixelStash main.top.dut.leafB" \
  bash -c "cd bo && $BLUETCL ../correlate.tcl"

echo ""

# Run correlation for mkSplitPortsTest
TOP_NAME=sysSplitPortsTest \
  VERI_VCD="$(pwd)/veri/sp.vcd" \
  SIM_VCD="$(pwd)/sim/sp.vcd" \
  MOD_AT_LIST="mkSplitPortsTest main.top.dut" \
  bash -c "cd bo && $BLUETCL ../correlate.tcl"
