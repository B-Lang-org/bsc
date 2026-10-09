#!/usr/bin/env bash
# Gate: changes to the binary-format code must bump the format tags.
#
# The .bo and .ba readers decide compatibility solely by the header tag
# strings in src/comp/GenBin.hs and src/comp/GenABin.hs.  A format
# change without a tag bump makes a same-tag reader misparse stale
# files and crash with an internalError instead of the intended
# "recompile" error -- a mistake that has now been made independently
# by several PRs.  This check makes the tag bump hard to forget:
#
#   - a change to src/comp/GenBin.hs  requires the .bo tag to change
#   - a change to src/comp/GenABin.hs requires the .ba tag to change
#   - a change to src/comp/BinData.hs (Bin instances shared by both
#     formats) requires BOTH tags to change
#
# Not every change to these files alters serialized bytes (comments,
# the hash plumbing, dump/trace code).  For those, add a commit
# trailer to any commit in the range:
#
#   Bin-format: bo-unchanged
#   Bin-format: ba-unchanged
#
# asserting that the change provably does not alter the bytes of that
# format.  The trailer is part of the audit trail: a reviewer can hold
# the commit to its claim.
#
# Usage: check_bin_format_tags.sh <base-sha> <head-sha>

set -eu

BASE=$1
HEAD=$2

changed() {
    ! git diff --quiet "$BASE" "$HEAD" -- "$1"
}

tag_in() {
    # first bsc-bo-* / bsc-ba-* string in the file at the given commit
    git show "$1:$2" 2>/dev/null \
        | sed -n 's/.*T\.pack "\(bsc-b[oa]-[^"]*\)".*/\1/p' \
        | head -1
}

has_override() {
    git log --format=%B "$BASE..$HEAD" \
        | grep -qiE "^Bin-format: *$1-unchanged[[:space:]]*$"
}

fail=0

check() {
    # $1 = file whose change triggers the check
    # $2 = file holding the tag
    # $3 = format kind (bo | ba)
    local file=$1 tagfile=$2 kind=$3
    changed "$file" || return 0
    local t_base t_head
    t_base=$(tag_in "$BASE" "$tagfile")
    t_head=$(tag_in "$HEAD" "$tagfile")
    if [ -z "$t_head" ]; then
        echo "FAIL: could not find a .$kind format tag in $tagfile at $HEAD"
        fail=1
        return 0
    fi
    if [ "$t_base" = "$t_head" ]; then
        if has_override "$kind"; then
            echo "note: $file changed with the .$kind tag unchanged ($t_head);"
            echo "      accepted via 'Bin-format: $kind-unchanged' trailer"
        else
            echo "FAIL: $file changed but the .$kind format tag is still '$t_head'."
            echo "      If the serialized format changed, bump the tag in $tagfile."
            echo "      If it provably did not, add a commit trailer:"
            echo "          Bin-format: $kind-unchanged"
            fail=1
        fi
    else
        echo "ok: $file changed and the .$kind tag was bumped: $t_base -> $t_head"
    fi
}

check src/comp/GenBin.hs  src/comp/GenBin.hs  bo
check src/comp/GenABin.hs src/comp/GenABin.hs ba
check src/comp/BinData.hs src/comp/GenBin.hs  bo
check src/comp/BinData.hs src/comp/GenABin.hs ba

if [ "$fail" -eq 0 ]; then
    echo "bin-format tag gate: OK"
fi
exit $fail
