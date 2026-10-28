#!/usr/bin/env bash
# Run after building the compiler, using its GHC and package environment.
# Correctness only:
#   GHC=ghc testsuite/bsc.bluetcl/wiretypemap_perf/run.sh
# Correctness plus optional scaling measurements (two entries per instance):
#   GHC=ghc testsuite/bsc.bluetcl/wiretypemap_perf/run.sh 2000 4000 8000 16000
#
# For an A/B comparison, export an older WireAnalysis.hs to a directory:
#   mkdir -p /tmp/wire-analysis-baseline
#   git show BASE_REF:src/comp/WireAnalysis.hs > /tmp/wire-analysis-baseline/WireAnalysis.hs
# Then repeat the command with WIRE_ANALYSIS_DIR=/tmp/wire-analysis-baseline.
# The optional directory overrides only the source search path; the fixture
# still calls getWireTypeMap directly. These benchmarks are not timed gates
# in the default compiler testsuite.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
ghc_cmd=${GHC:-ghc}

if [[ ! -f "$root/src/comp/BuildVersion.hs" ]]; then
    echo "Build the compiler first to generate src/comp/BuildVersion.hs." >&2
    exit 1
fi

build_dir=$(mktemp -d "${TMPDIR:-/tmp}/wiretypemap-check.XXXXXX")
trap 'rm -rf "$build_dir"' EXIT
extra_sources=()
if [[ -n ${WIRE_ANALYSIS_DIR:-} ]]; then
    extra_sources+=("-i$WIRE_ANALYSIS_DIR")
fi

"$ghc_cmd" --make -O2 "${extra_sources[@]}" \
    -i"$root/src/comp" -i"$root/src/comp/Libs" \
    -i"$root/src/comp/GHC/posix" \
    -outputdir "$build_dir" "$here/WireTypeMapCheck.hs" \
    -o "$build_dir/check"

"$build_dir/check"
for count in "$@"; do
    "$build_dir/check" "$count"
done
