#!/usr/bin/env bash

set -e

# For now, restrict to Haskell/Bluespec code as we've a lot of third party
# vendored code in the repo that we don't want to needlessly modify
if git ls-files | egrep '\.(lhs|hs|hsc|bs|bsv)$' | xargs grep -n ' $'; then
  echo "Trailing whitespace found!"
  exit 1
fi

if git ls-files | egrep '\.(lhs|hs|hsc)$' | xargs grep -n $'\t'; then
  echo "Tabs found!"
  exit 1
fi

exit 0
