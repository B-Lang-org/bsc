#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
task_install=${BSC_INSTALL:-$root/inst}
task_output=$(mktemp -d "${TMPDIR:-/tmp}/candidate-sets.XXXXXX")
trap 'rm -rf "$task_output"' EXIT
for mode in default seven; do
    out="$task_output/$mode"
    mkdir "$out"
    flags=()
    if [[ $mode == seven ]]; then
        flags=(-keep-fires -keep-inlined-boundaries -no-inline-bool -no-opt-sched
               -no-opt-aggressive-inline -no-opt-join-defs -no-opt-AndOr)
    fi
    for source in CandidateSetFlow LateInlineTypes; do
        "$task_install/bin/bsc" -u -verilog -elab -no-show-timestamps -no-show-version \
            "${flags[@]}" -p "+:$here" -bdir "$out" -vdir "$out" -info-dir "$out" "$here/$source.bsv"
    done
    (cd "$out"; "$task_install/bin/bluetcl" "$here/check-candidate-sets.tcl")
done
