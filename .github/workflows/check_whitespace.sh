#!/usr/bin/env bash

set -e

RESULT=0

# -----
# Check for trailing whitespace

# For now, restrict to Haskell/Bluespec code as we've a lot of third party
# vendored code in the repo that we don't want to needlessly modify

CMD="git ls-files | egrep '\.(lhs|hs|hsc|bs|bsv)$' | xargs grep -H -n -e ' $'"
if [ $(eval "$CMD -l -- | wc -l") -ne 0 ]; then
    eval "$CMD --" || true
    echo "Trailing whitespace found!"
    RESULT=1
fi

# -----
# Check for tabs

CMD="git ls-files | egrep '\.(lhs|hs|hsc)$' | xargs grep -H -n -e $'\t'"
if [ $(eval "$CMD -l -- | wc -l") -ne 0 ]; then
    eval "$CMD --" || true
    echo "Tabs found!"
    RESULT=1
fi

# -----

exit $RESULT
