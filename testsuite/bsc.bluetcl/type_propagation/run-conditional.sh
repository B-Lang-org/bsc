#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
ghc_cmd=${GHC:-ghc}
task_install=${BSC_INSTALL:-$root/inst}
task_output=$(mktemp -d "${TMPDIR:-/tmp}/conditional-types.XXXXXX")
trap 'rm -rf "$task_output"' EXIT

"$ghc_cmd" --make -O0 -i"$root/src/comp" -i"$root/src/comp/Libs" \
    -i"$root/src/comp/GHC/posix" -outputdir "$task_output/ghc" \
    "$here/ConditionalSourceTypesCheck.hs" -o "$task_output/check"
"$task_output/check"
cd "$task_output"
"$task_install/bin/bsc" -u -verilog -elab -no-show-timestamps -no-show-version \
    -p "+:$here" -bdir "$task_output" -vdir "$task_output" \
    -info-dir "$task_output" "$here/ConditionalTypes.bsv"
"$task_install/bin/bluetcl" "$here/check-conditional.tcl"
