#!/usr/bin/env bash

set -e

RESULT=0

# -----
# Check the spelling of tool names

# The documentation spells the Tcl shell Bluetcl, and so does the tree:
# the module, its file, the Tcl package and namespace, and the prose.
# Every tracked file's contents and name are checked.  Each pattern is
# written with a bracketed letter so that this file does not match itself.

check_spelling () {
    local pattern="$1"
    local correct="$2"
    local cmd="git ls-files -z | xargs -0 grep -I -H -n -s -e '$pattern'"
    if [ $(eval "$cmd -l -- | wc -l") -ne 0 ]; then
        eval "$cmd --" || true
        echo "Spell it $correct!"
        RESULT=1
    fi
    if git ls-files | grep -n -e "$pattern"; then
        echo "Spell it $correct in the file name!"
        RESULT=1
    fi
}

check_spelling 'Blue[T]cl' Bluetcl

# -----

exit $RESULT
