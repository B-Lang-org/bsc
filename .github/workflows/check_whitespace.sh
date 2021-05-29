#!/usr/bin/env bash

set -e

SCRIPTDIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

RESULT=0

# -----
# Check for trailing whitespace

# For now, restrict to Haskell/Bluespec code as we've a lot of third party
# vendored code in the repo that we don't want to needlessly modify

# We should at least look for both trailing space (' ') and tab ('\t').
# By using '\s' in the grep pattern, we also check for CR ('\r') and
# LF ('\f').  If we wanted to allow DOS files (that end lines with \r\n)
# then the grep pattern would need to be '( |\t|\f)\r?$' so that we detect
# spaces and tabs that are followed by CR (and thus not fully trailing).

# Files can be exempted from the check by adding a pattern to the
# 'allow_whitespace.pats' file.  For example, some parser tests need to
# check BSC's behavior on files containing whitespace.

ALLOWFILE=${SCRIPTDIR}/allow_whitespace.pats
CMD="git ls-files | egrep '\.(lhs|hs|hsc|bs|bsv)$' | grep -v -f $ALLOWFILE | xargs grep -H -n -e '\s$'"
if [ $(eval "$CMD -l -- | wc -l") -ne 0 ]; then
    eval "$CMD --" || true
    echo "Trailing whitespace found!"
    RESULT=1
fi

# -----
# Check for tabs

CMD="git ls-files | egrep '\.(lhs|hs|hsc|bs)$' | xargs grep -H -n -e $'\t'"
if [ $(eval "$CMD -l -- | wc -l") -ne 0 ]; then
    eval "$CMD --" || true
    echo "Tabs found!"
    RESULT=1
fi

# -----

exit $RESULT
