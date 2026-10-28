#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
ghc_cmd=${GHC:-ghc}
task_install=${BSC_INSTALL:-$root/inst}
task_output=$(mktemp -d "${TMPDIR:-/tmp}/primitive-types.XXXXXX")
trap 'rm -rf "$task_output"' EXIT
"$ghc_cmd" --make -O0 -rtsopts -i"$root/src/comp" -i"$root/src/comp/Libs" \
    -i"$root/src/comp/GHC/posix" -outputdir "$task_output/ghc" \
    "$here/PrimitiveSourceTypesCheck.hs" -o "$task_output/check"
"$task_output/check"
for mode in default seven; do
    out="$task_output/$mode"
    mkdir "$out"
    flags=()
    if [[ $mode == seven ]]; then
        flags=(-keep-fires -keep-inlined-boundaries -no-inline-bool -no-opt-sched
               -no-opt-aggressive-inline -no-opt-join-defs -no-opt-AndOr)
    fi
    env BLUESPECDIR="$task_install/lib" "$task_install/bin/bsc" -u -verilog -elab -no-show-timestamps -no-show-version \
        "${flags[@]}" -p "+:$here" -bdir "$out" -vdir "$out" -info-dir "$out" "$here/PrimitiveTypes.bsv"
    (cd "$out"; env BLUESPECDIR="$task_install/lib" "$task_install/bin/bluetcl" "$here/check-primitives.tcl")
    if [[ -n ${BSC_BASELINE_INSTALL:-} ]]; then
        before="$task_output/baseline-$mode"
        mkdir "$before"
        env BLUESPECDIR="$BSC_BASELINE_INSTALL/lib" "$BSC_BASELINE_INSTALL/bin/bsc" -u -verilog -elab -no-show-timestamps -no-show-version \
            "${flags[@]}" -p "+:$here" -bdir "$before" -vdir "$before" -info-dir "$before" "$here/PrimitiveTypes.bsv"
        for rtl in "$out"/*.v; do cmp "$rtl" "$before/$(basename "$rtl")"; done
    fi
done
