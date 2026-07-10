#!/usr/bin/env bash
# End-to-end driver for the wiretypemap <-> VCD correlation check.
# Runs correlation for two distinct modules:
#   1. mkWireTypes (rich types: struct/union/enum/Maybe/Vector,
#      plus polymorphic primitives: Reg, FIFOF, BRAM, SyncFIFO, CReg5,
#      RWire/BypassWire/PulseWire, and separately-synthesized leaves)
#   2. mkSplitPortsTest (sub-interface with DeepSplit-collapsed arg)
#
# Verilog is built and run twice -- once with default bsc flags and once
# with `-keep-inlined-boundaries` (which preserves <inst>$wget / $whas
# and CReg port<n>__read/write_1 wires that the optimizer would
# otherwise fold). Bluesim is built once: `simExpand` reads APackage
# directly and doesn't run aInlineWires/aInlineCReg, so the flag has
# no effect on the Bluesim VCD.

set -euo pipefail

cd "$(dirname "$0")"

BSC=${BSC:-bsc}
BLUETCL=${BLUETCL:-bluetcl}

rm -rf bo_sim bo_default bo_kib veri_default veri_kib sim \
       vcd_correlation_build.log
mkdir -p bo_sim sim

# build_verilog <variant-tag> <bsc-extra-flags>
build_verilog () {
    local variant="$1"
    local extra="$2"
    local bo="bo_${variant}"
    local veri="veri_${variant}"
    mkdir -p "$bo" "$veri"
    {
      echo "[WireTypes][$variant] Compiling to Verilog..."
      $BSC $extra -bdir "$bo" -verilog -vdir "$veri" -elab -u -g sysWireTypeTest WireTypesSim.bsv
      $BSC $extra -bdir "$bo" -verilog -vdir "$veri" -e sysWireTypeTest -o "$veri/sysWireTypeTest"
      echo "[SplitPorts][$variant] Compiling to Verilog..."
      $BSC $extra -bdir "$bo" -verilog -vdir "$veri" -elab -u -g sysSplitPortsTest SplitPortsSim.bsv
      $BSC $extra -bdir "$bo" -verilog -vdir "$veri" -e sysSplitPortsTest -o "$veri/sysSplitPortsTest"
      echo "[WireTypes][$variant] Running Verilog sim..."
      (cd "$veri" && ./sysWireTypeTest +bscvcd 2>&1) > "$veri/WireTypes_sim.log" || true
      mv "$veri/dump.vcd" "$veri/WireTypes.vcd"
      echo "[SplitPorts][$variant] Running Verilog sim..."
      (cd "$veri" && ./sysSplitPortsTest +bscvcd 2>&1) > "$veri/SplitPorts_sim.log" || true
      mv "$veri/dump.vcd" "$veri/SplitPorts.vcd"
    } >> vcd_correlation_build.log 2>&1
}

# Build Bluesim only once -- -keep-inlined-boundaries doesn't affect it
# (simExpand reads APackage directly, skipping aInlineWires/aInlineCReg).
# Use a separate bo_sim cache so it stays disjoint from the Verilog
# variants' .bo dirs.
{
  echo "[WireTypes] Compiling to Bluesim..."
  $BSC -bdir bo_sim -sim -simdir sim -elab -u -g sysWireTypeTest WireTypesSim.bsv
  $BSC -bdir bo_sim -sim -simdir sim -e sysWireTypeTest -o sim/sysWireTypeTest
  echo "[SplitPorts] Compiling to Bluesim..."
  $BSC -bdir bo_sim -sim -simdir sim -elab -u -g sysSplitPortsTest SplitPortsSim.bsv
  $BSC -bdir bo_sim -sim -simdir sim -e sysSplitPortsTest -o sim/sysSplitPortsTest
  echo "[WireTypes] Running Bluesim..."
  (cd sim && ./sysWireTypeTest -V WireTypes.vcd 2>&1) > sim/WireTypes_sim.log || true
  echo "[SplitPorts] Running Bluesim..."
  (cd sim && ./sysSplitPortsTest -V SplitPorts.vcd 2>&1) > sim/SplitPorts_sim.log || true
} > vcd_correlation_build.log 2>&1

build_verilog default ""
build_verilog kib "-keep-inlined-boundaries"

# correlate <variant-tag>
correlate_variant () {
    local variant="$1"
    local extra_desc="$2"
    local bo="bo_${variant}"
    local veri="veri_${variant}"
    echo "########## variant: $variant (Verilog $extra_desc; Bluesim is flag-agnostic) ##########"

    TOP_NAME=sysWireTypeTest \
      VERI_VCD="$(pwd)/$veri/WireTypes.vcd" \
      SIM_VCD="$(pwd)/sim/WireTypes.vcd" \
      MOD_AT_LIST="mkWireTypes main.top.dut mkPixelStash main.top.dut.leafA mkPixelStash main.top.dut.leafB" \
      bash -c "cd '$bo' && $BLUETCL ../correlate.tcl"
    echo ""

    TOP_NAME=sysSplitPortsTest \
      VERI_VCD="$(pwd)/$veri/SplitPorts.vcd" \
      SIM_VCD="$(pwd)/sim/SplitPorts.vcd" \
      MOD_AT_LIST="mkSplitPortsTest main.top.dut" \
      bash -c "cd '$bo' && $BLUETCL ../correlate.tcl"
    echo ""
}

correlate_variant default "default flags"
correlate_variant kib     "-keep-inlined-boundaries"
