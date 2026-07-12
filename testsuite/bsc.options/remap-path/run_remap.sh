#!/usr/bin/env sh
# Build the same sources from two different directories with
# -remap-path-prefix and check that every output is byte-identical and
# free of the build directories' absolute paths.
set -e

BSC=${BSC:-bsc}

rm -rf dirA dirB
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
    if grep -q "$(pwd)/dirA" "$f"; then
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

exit $status
