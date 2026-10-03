#!/usr/bin/env sh
# Build the same sources from two different directories, with no
# path-related flags, and check that every output is byte-identical and
# free of both the build directories' and the installation's absolute
# paths.  (How positions read back from these files print is pinned by
# the goldens that cite library positions, e.g. bsc.interra/messages.)
set -e

BSC=${BSC:-bsc}
BSDIR=${BLUESPECDIR:-$(cd "$(dirname "$(command -v "$BSC")")/../lib" && pwd)}

rm -rf dirA dirB dirC
mkdir -p dirA dirB
for d in dirA dirB; do
    cp Foo.bsv Bar.bsv "$d"/
done

for d in dirA dirB; do
    (
        cd "$d"
        # one compile via -u (exercises the import/dependency path),
        # one elaboration to .ba
        $BSC -u Bar.bsv
        $BSC -sim -g mkFoo Foo.bsv
    ) > "$d.log" 2>&1
done

status=0
for f in Foo.bo Bar.bo mkFoo.ba; do
    if cmp -s dirA/"$f" dirB/"$f"; then
        echo "IDENTICAL $f"
    else
        echo "DIFFER $f"
        status=1
    fi
done

# neither the build directory nor the installation may survive in any
# output; byte-wise, so that a grep which skips binary files or
# non-UTF-8 lines cannot miss a match
for f in dirA/Foo.bo dirA/Bar.bo dirA/mkFoo.ba; do
    if LC_ALL=C grep -qaF "$(pwd)/dirA" "$f"; then
        echo "RESIDUAL-PATH $f"
        status=1
    elif LC_ALL=C grep -qaF "$BSDIR" "$f"; then
        echo "RESIDUAL-INSTALL-PATH $f"
        status=1
    else
        echo "CLEAN $f"
    fi
done

# repeatability on one machine: a re-run in place is byte-identical
( cd dirA && $BSC -sim -g mkFoo Foo.bsv ) > dirA-rerun.log 2>&1
if cmp -s dirA/mkFoo.ba dirB/mkFoo.ba; then
    echo "REPEATABLE mkFoo.ba"
else
    echo "NOT-REPEATABLE mkFoo.ba"
    status=1
fi

# an absolute-path invocation stores the same bytes as the relative one
mkdir -p dirC
cp Foo.bsv Bar.bsv dirC/
(
    cd dirC
    $BSC -u Bar.bsv
    $BSC -sim -g mkFoo "$PWD/Foo.bsv"
) > dirC.log 2>&1
if cmp -s dirC/mkFoo.ba dirA/mkFoo.ba; then
    echo "IDENTICAL-ABS mkFoo.ba"
else
    echo "DIFFER-ABS mkFoo.ba"
    status=1
fi

exit $status
