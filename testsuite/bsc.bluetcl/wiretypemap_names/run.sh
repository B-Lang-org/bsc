#!/usr/bin/env bash
# Run after building the compiler, with its GHC/package environment.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
ghc_cmd=${GHC:-ghc}
task_install=${BSC_INSTALL:-$root/inst}
task_output=$(mktemp -d "${TMPDIR:-/tmp}/declared-wire-names.XXXXXX")
trap 'rm -rf "$task_output"' EXIT

"$ghc_cmd" --make -O0 -rtsopts -i"$root/src/comp" -i"$root/src/comp/Libs" \
    -i"$root/src/comp/GHC/posix" -outputdir "$task_output/ghc" \
    "$here/CheckDeclaredOnly.hs" -o "$task_output/check"
for mode in default dollar sim ; do
    mkdir "$task_output/$mode"
    flags=(-verilog -elab)
    case "$mode" in
        dollar) flags+=(-remove-dollar) ;;
        sim) flags=(-sim -elab) ;;
        staged) flags=(-verilog -elab-only) ;;
    esac
    "$task_install/bin/bsc" -u "${flags[@]}" -no-show-timestamps -no-show-version \
        -bdir "$task_output/$mode" -vdir "$task_output/$mode" \
        -info-dir "$task_output/$mode" "$here/DeclaredOnlyTypes.bsv"
    "$task_output/check" "$mode" "$task_output/$mode"
    (cd "$task_output/$mode" && "$task_install/bin/bluetcl" "$here/check.tcl" "$mode")
done
