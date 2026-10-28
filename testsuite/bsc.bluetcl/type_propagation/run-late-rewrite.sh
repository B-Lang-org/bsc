#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
ghc_cmd=${GHC:-ghc}
task_install=${BSC_INSTALL:-$root/inst}
task_output=$(mktemp -d "${TMPDIR:-/tmp}/late-rewrite-types.XXXXXX")
trap 'rm -rf "$task_output"' EXIT
export BLUESPECDIR="$task_install/lib"

"$ghc_cmd" --make -O0 -rtsopts -i"$root/src/comp" -i"$root/src/comp/Libs" \
    -i"$root/src/comp/GHC/posix" -outputdir "$task_output/ghc" \
    "$here/LateRewriteTypesCheck.hs" -o "$task_output/check"
"$task_output/check" +RTS -K100M -RTS
for mode in default seven; do
    out="$task_output/$mode"
    mkdir "$out"
    flags=()
    if [[ $mode == seven ]]; then
        flags=(-keep-fires -keep-inlined-boundaries -no-inline-bool -no-opt-sched
               -no-opt-aggressive-inline -no-opt-join-defs -no-opt-AndOr)
    fi
    "$task_install/bin/bsc" -u -verilog -elab -no-show-timestamps -no-show-version \
        "${flags[@]}" -p "+:$here" -bdir "$out" -vdir "$out" -info-dir "$out" \
        "$here/LateRewriteTypes.bsv" +RTS -K100M -RTS
    (cd "$out"; "$task_install/bin/bluetcl" "$here/check-late-rewrite.tcl")
done
