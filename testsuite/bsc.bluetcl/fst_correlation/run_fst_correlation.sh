#!/usr/bin/env bash
# FST twin of ../vcd_correlation/run_correlation.sh: the same designs
# and wiretypemap correlation, but the waveforms are FST dumps --
# iverilog via `vvp -fst` + the +bscfst plusarg, Bluesim via
# -dump-formats fst + the +bscfst plusarg.  The FST hierarchies
# (including each scope's module type, which FST records and VCD has
# no place for) are extracted with the fstscopes utility, and the
# correlator additionally confirms that the expected module type is
# recorded at each correlated scope.

set -euo pipefail

cd "$(dirname "$0")"

BSC=${BSC:-bsc}
BLUETCL=${BLUETCL:-bluetcl}

# The hierarchy dumper for FST files, built and installed by
# `make install-extra` (like vcdcheck).  fst2vcd cannot be used here:
# its reader path discards the scope component (module type) field,
# which is exactly what this test checks.
FSTSCOPES=${FSTSCOPES:-fstscopes}

# This test is iverilog-specific: the FST encoding is chosen by
# running `vvp -fst`, and iverilog records each scope's module type
# (vpiDefName) in the FST, which is part of what is being checked.
export BSC_VERILOG_SIM=${BSC_VERILOG_SIM:-iverilog}

# the designs are shared with the VCD correlation test
SRC=../vcd_correlation

rm -rf bo_sim bo_default bo_kib veri_default veri_kib sim \
       fst_correlation_build.log
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
      $BSC $extra -p +:$SRC -bdir "$bo" -verilog -vdir "$veri" -elab -u -g sysWireTypeTest $SRC/WireTypesSim.bsv
      $BSC $extra -p +:$SRC -bdir "$bo" -verilog -vdir "$veri" -dump-formats fst -e sysWireTypeTest -o "$veri/sysWireTypeTest"
      echo "[SplitPorts][$variant] Compiling to Verilog..."
      $BSC $extra -p +:$SRC -bdir "$bo" -verilog -vdir "$veri" -elab -u -g sysSplitPortsTest $SRC/SplitPortsSim.bsv
      $BSC $extra -p +:$SRC -bdir "$bo" -verilog -vdir "$veri" -dump-formats fst -e sysSplitPortsTest -o "$veri/sysSplitPortsTest"
      echo "[WireTypes][$variant] Running Verilog sim (vvp ... -fst)..."
      (cd "$veri" && vvp sysWireTypeTest -fst +bscfst 2>&1) > "$veri/WireTypes_sim.log" || true
      mv "$veri/dump.fst" "$veri/WireTypes.fst"
      echo "[SplitPorts][$variant] Running Verilog sim (vvp ... -fst)..."
      (cd "$veri" && vvp sysSplitPortsTest -fst +bscfst 2>&1) > "$veri/SplitPorts_sim.log" || true
      mv "$veri/dump.fst" "$veri/SplitPorts.fst"
      echo "[$variant] Extracting FST hierarchies..."
      "$FSTSCOPES" "$veri/WireTypes.fst"  > "$veri/WireTypes.fsthier"
      "$FSTSCOPES" "$veri/SplitPorts.fst" > "$veri/SplitPorts.fsthier"
    } >> fst_correlation_build.log 2>&1
}

# Build Bluesim only once -- -keep-inlined-boundaries doesn't affect it
# (see run_correlation.sh); linked with -dump-formats fst.
{
  echo "[WireTypes] Compiling to Bluesim..."
  $BSC -p +:$SRC -bdir bo_sim -sim -simdir sim -elab -u -g sysWireTypeTest $SRC/WireTypesSim.bsv
  $BSC -p +:$SRC -bdir bo_sim -sim -simdir sim -dump-formats fst -e sysWireTypeTest -o sim/sysWireTypeTest
  echo "[SplitPorts] Compiling to Bluesim..."
  $BSC -p +:$SRC -bdir bo_sim -sim -simdir sim -elab -u -g sysSplitPortsTest $SRC/SplitPortsSim.bsv
  $BSC -p +:$SRC -bdir bo_sim -sim -simdir sim -dump-formats fst -e sysSplitPortsTest -o sim/sysSplitPortsTest
  echo "[WireTypes] Running Bluesim (+bscfst)..."
  (cd sim && ./sysWireTypeTest +bscfst=WireTypes.fst 2>&1) > sim/WireTypes_sim.log || true
  echo "[SplitPorts] Running Bluesim (+bscfst)..."
  (cd sim && ./sysSplitPortsTest +bscfst=SplitPorts.fst 2>&1) > sim/SplitPorts_sim.log || true
  echo "Extracting FST hierarchies..."
  "$FSTSCOPES" sim/WireTypes.fst  > sim/WireTypes.fsthier
  "$FSTSCOPES" sim/SplitPorts.fst > sim/SplitPorts.fsthier
} > fst_correlation_build.log 2>&1

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
      VERI_HIER="$(pwd)/$veri/WireTypes.fsthier" \
      SIM_HIER="$(pwd)/sim/WireTypes.fsthier" \
      MOD_AT_LIST="mkWireTypes main.top.dut mkPixelStash main.top.dut.leafA mkPixelStash main.top.dut.leafB" \
      bash -c "cd '$bo' && $BLUETCL ../correlate_fst.tcl"
    echo ""

    TOP_NAME=sysSplitPortsTest \
      VERI_HIER="$(pwd)/$veri/SplitPorts.fsthier" \
      SIM_HIER="$(pwd)/sim/SplitPorts.fsthier" \
      MOD_AT_LIST="mkSplitPortsTest main.top.dut" \
      bash -c "cd '$bo' && $BLUETCL ../correlate_fst.tcl"
    echo ""
}

correlate_variant default "default flags"
correlate_variant kib     "-keep-inlined-boundaries"
