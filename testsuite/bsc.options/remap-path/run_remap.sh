#!/usr/bin/env sh
# Build the same sources from two different directories with
# -remap-path-prefix and check that every output is byte-identical and
# free of the build directories' absolute paths.
set -e

BSC=${BSC:-bsc}

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
        $BSC -remap-path-prefix "$PWD=." -u Bar.bsv
        $BSC -remap-path-prefix "$PWD=." -sim -g mkFoo Foo.bsv
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

# no residual build-directory path may survive in any output
for f in dirA/Foo.bo dirA/Bar.bo dirA/mkFoo.ba; do
    if grep -qF "$(pwd)/dirA" "$f"; then
        echo "RESIDUAL-PATH $f"
        status=1
    else
        echo "CLEAN $f"
    fi
done

# repeatability on one machine: a re-run in place is byte-identical
( cd dirA && $BSC -remap-path-prefix "$PWD=." -sim -g mkFoo Foo.bsv ) \
    > dirA-rerun.log 2>&1
if cmp -s dirA/mkFoo.ba dirB/mkFoo.ba; then
    echo "REPEATABLE mkFoo.ba"
else
    echo "NOT-REPEATABLE mkFoo.ba"
    status=1
fi

# absolute-path invocation: the stored source name must be remapped
# cleanly, with no invented trailing separator (a marker-free path must
# not go through the /// pwd-marker decoder)
mkdir -p dirC
cp Foo.bsv Bar.bsv dirC/
(
    cd dirC
    $BSC -remap-path-prefix "$PWD=." -u Bar.bsv
    $BSC -remap-path-prefix "$PWD=." -sim -g mkFoo "$PWD/Foo.bsv"
) > dirC.log 2>&1
if grep -qa "Foo.bsv/" dirC/mkFoo.ba; then
    echo "TRAILING-SLASH dirC/mkFoo.ba"
    status=1
else
    echo "NO-TRAILING-SLASH dirC/mkFoo.ba"
fi
if grep -qa "$(pwd)/dirC" dirC/mkFoo.ba; then
    echo "RESIDUAL-PATH dirC/mkFoo.ba"
    status=1
else
    echo "CLEAN dirC/mkFoo.ba"
fi
# the absolute invocation must produce the same bytes as the relative one
if cmp -s dirC/mkFoo.ba dirA/mkFoo.ba; then
    echo "IDENTICAL-ABS mkFoo.ba"
else
    echo "DIFFER-ABS mkFoo.ba"
    status=1
fi

exit $status
