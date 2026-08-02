#!/usr/bin/env bash
# Build the self-contained bluehs distribution tarball.
#
# Produces bsc-bluehs-<os>-<arch>-<version>.tar.gz: a relocatable tree
# containing a pruned GHC runtime, a relocatable package store with the
# bsc library and its dependencies, the SAT solver shared libraries, the
# utility scripts, and a bin/bluehs launcher.  Users of the tarball can
# run Haskell scripts against the bsc library with no Haskell toolchain
# installed (a system C compiler is still required: GHC's loader probes
# it, and CPP scripts preprocess with it).
#
# This is the companion artifact to the main bsc tarball and must be
# built from the SAME source tree / commit: the packaged library embeds
# the build version string and rejects .ba files from a different bsc.
#
# Prerequisites: a completed `make install-src` (vendor solver libs) and
# ghc + cabal on PATH (the same GHC that will be shipped).
#
# Usage: util/bluehs/mk-dist.sh [output-dir]     (default: build/bluehs)

set -euo pipefail

REPO=$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)
OUT=${1:-$REPO/build/bluehs}
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)   # absolutize: later steps cd around
WORK=$OUT/work
DIST=$OUT/dist

OS=$(uname -s | tr '[:upper:]' '[:lower:]')
ARCH=$(uname -m)
VERSION=$(git -C "$REPO" describe --tags --always 2>/dev/null || echo unknown)
TARBALL=$OUT/bsc-bluehs-$OS-$ARCH-$VERSION.tar.gz

msg() { echo ">>> $*"; }

# ----------------------------------------------------------------------
# 0. Locate the GHC installation and sanity-check prerequisites

GHC_REAL_BIN=$(dirname "$(readlink -f "$(command -v ghc)")")
# ghcup layout: <root>/bin/ghc -> symlink; real binaries in <root>/lib/ghc-*/bin
# or directly <root>/bin.  Find the root containing both bin/ and lib/.
GHC_ROOT=$(cd "$GHC_REAL_BIN/.." && pwd)
while [ ! -d "$GHC_ROOT/lib" ] || [ ! -d "$GHC_ROOT/bin" ]; do
    GHC_ROOT=$(dirname "$GHC_ROOT")
    [ "$GHC_ROOT" = "/" ] && { echo "cannot locate GHC root" >&2; exit 1; }
done
GHC_VER=$(ghc --numeric-version)
msg "GHC $GHC_VER at $GHC_ROOT"

for f in "$REPO"/src/vendor/stp/lib/libstp.so "$REPO"/src/vendor/yices/lib/libyices.so; do
    [ -e "$f" ] || { echo "$f missing - run the vendor lib builds first" >&2; exit 1; }
done

# The update scripts use `set -u` and expect these from the Makefile
export NOGIT=${NOGIT:-0}
export NOUPDATEBUILDVERSION=${NOUPDATEBUILDVERSION:-0}
(cd "$REPO/src/comp" && ./update-build-version.sh && ./update-build-system.sh)

# REUSE_WORK=1 skips the (slow) store build if a previous run completed it
if [ "${REUSE_WORK:-0}" != 1 ]; then rm -rf "$WORK"; fi
rm -rf "$DIST"
mkdir -p "$WORK" "$DIST"/{bin,scripts,SAT,LICENSES} "$DIST/hs"

# ----------------------------------------------------------------------
# 1. Build the bsc library + deps into a fresh store (out-of-repo project,
#    so the repo's own dist-newstyle and env file are untouched)

msg "building bsc library into store (this compiles all modules at -O2)"
mkdir -p "$WORK/proj"
cat > "$WORK/proj/cabal.project" <<EOF
packages: $REPO

package bsc
  optimization: 2
  extra-lib-dirs: $REPO/src/vendor/stp/lib
  extra-lib-dirs: $REPO/src/vendor/yices/lib
  ghc-options: -j
EOF
if [ "${REUSE_WORK:-0}" = 1 ] && [ -f "$WORK/bsc.env" ]; then
    msg "REUSE_WORK=1: reusing existing store"
else
    (cd "$WORK/proj" && cabal --store-dir="$WORK/store" install --lib bsc \
        --package-env "$WORK/bsc.env" >"$WORK/cabal-install.log" 2>&1) \
        || { tail -30 "$WORK/cabal-install.log" >&2; exit 1; }
fi

STOREDB=$WORK/store/ghc-$GHC_VER/package.db

# ----------------------------------------------------------------------
# 2. Pruned GHC runtime

msg "copying and pruning GHC runtime"
mkdir -p "$DIST/hs/ghc"
cp -a "$GHC_ROOT/bin" "$GHC_ROOT/lib" "$DIST/hs/ghc/"

# Drop profiling and static ways (keep libCffi*.a: shipped static-only,
# and deleting it makes `ghc-pkg check` report rts as broken)
find "$DIST/hs/ghc/lib" -name '*.p_hi' -delete
find "$DIST/hs/ghc/lib" -name '*_p.a' -delete
find "$DIST/hs/ghc/lib" -name '*.a' ! -name 'libCffi*' -delete
# Drop tools scripts never need
for tool in haddock hsc2hs hpc hp2ps ghc-iserv ghc-iserv-prof; do
    find "$DIST/hs/ghc/bin" -maxdepth 1 -name "$tool*" -delete
    find "$DIST/hs/ghc/lib" -path '*/bin/*' -name "$tool*" ! -name 'ghc-iserv-dyn*' -delete
done

# Replace the outer bin/ wrappers (they hardcode the build machine's
# paths) with self-locating equivalents.  ghc/ghc-pkg/runghc have real
# binaries under lib/ghc-<ver>/bin; ghci and runhaskell are pure aliases.
GHCLIBDIR_REL="lib/ghc-$GHC_VER/lib"
[ -d "$DIST/hs/ghc/$GHCLIBDIR_REL" ] || { echo "unexpected GHC layout" >&2; exit 1; }
rm -f "$DIST/hs/ghc/bin"/*
mkwrap() {  # name, exec-line
    printf '#!/bin/sh\nhere=$(dirname "$(readlink -f "$0")")\nroot=$(dirname "$here")\nexec %s "$@"\n' "$2" \
        > "$DIST/hs/ghc/bin/$1"
    chmod 755 "$DIST/hs/ghc/bin/$1"
}
mkwrap ghc     "\"\$root/lib/ghc-$GHC_VER/bin/ghc-$GHC_VER\" -B\"\$root/$GHCLIBDIR_REL\""
mkwrap ghc-pkg "\"\$root/lib/ghc-$GHC_VER/bin/ghc-pkg-$GHC_VER\" --global-package-db \"\$root/$GHCLIBDIR_REL/package.conf.d\""
mkwrap runghc  "\"\$root/lib/ghc-$GHC_VER/bin/runghc-$GHC_VER\" -f \"\$here/ghc\""
mkwrap runhaskell "\"\$here/runghc\""
mkwrap ghci    "\"\$here/ghc\" --interactive"

# ----------------------------------------------------------------------
# 3. Relocatable store

msg "relocating package store"
cp -a "$WORK/store/ghc-$GHC_VER" "$DIST/hs/store-tmp"
mkdir -p "$DIST/hs/store"
mv "$DIST/hs/store-tmp" "$DIST/hs/store/ghc-$GHC_VER"
STORE=$DIST/hs/store/ghc-$GHC_VER

find "$STORE" -name '*.a' -delete
rm -rf "$STORE/incoming"
find "$STORE" -name 'cabal-hash.txt' -delete

# ${pkgroot} = the directory containing package.db
sed -i \
    -e "s|$WORK/store/ghc-$GHC_VER|\${pkgroot}|g" \
    -e "s|$REPO/src/vendor/stp/lib|\${pkgroot}/../../../SAT|g" \
    -e "s|$REPO/src/vendor/yices/lib|\${pkgroot}/../../../SAT|g" \
    "$STORE"/package.db/*.conf
# Drop haddock-* fields INCLUDING their continuation lines (they point at
# never-shipped docs; a bare sed of the header line would orphan the
# indented value lines and break ghc-pkg's parser)
for conf in "$STORE"/package.db/*.conf; do
    awk 'BEGIN{skip=0} /^[^ \t]/{skip = /^haddock-(interfaces|html):/ ? 1 : 0} !skip' \
        "$conf" > "$conf.tmp" && mv "$conf.tmp" "$conf"
done
"$DIST/hs/ghc/bin/ghc-pkg" --package-db="$STORE/package.db" recache

strip "$STORE"/*/lib/libHSbsc*.so 2>/dev/null || true
if command -v patchelf >/dev/null; then
    find "$STORE" -name 'libHS*.so' -exec patchelf --remove-rpath {} \; 2>/dev/null || true
fi

# ----------------------------------------------------------------------
# 4. Package environment: expose the store packages plus every boot package

msg "writing package environment"
GLOBALDB=$(ls -d "$DIST/hs/ghc/lib/ghc-$GHC_VER/lib/package.conf.d")
{
    echo "clear-package-db"
    echo "global-package-db"
    echo "package-db store/ghc-$GHC_VER/package.db"
    # NB: `dump` wraps long ids onto continuation lines; `field ... --simple-output` does not
    "$DIST/hs/ghc/bin/ghc-pkg" --package-db="$GLOBALDB" field '*' id --simple-output | awk 'NF{print "package-id " $1}'
    "$DIST/hs/ghc/bin/ghc-pkg" --package-db="$STORE/package.db" field '*' id --simple-output | awk 'NF{print "package-id " $1}'
} > "$DIST/hs/bsc.env"

# ----------------------------------------------------------------------
# 5. SAT libs, scripts, launcher

msg "copying SAT libs and scripts"
cp -a "$REPO"/src/vendor/stp/lib/libstp.so* "$DIST/SAT/"
cp -a "$REPO"/src/vendor/yices/lib/libyices.so* "$DIST/SAT/"
cp "$REPO"/util/bluehs/*.hs "$DIST/scripts/"

cat > "$DIST/bin/bluehs" <<'EOF'
#!/bin/sh
# bluehs: run a Haskell script against the packaged bsc library.
#   bluehs <tool> [args...]        tool from the scripts/ directory
#   bluehs <path/to/script.hs> [args...]
DIST=$(dirname "$(dirname "$(readlink -f "$0")")")
TOOL=${1:?usage: bluehs <tool|script.hs> [args...]}; shift
case "$TOOL" in
    *.hs) SCRIPT=$TOOL ;;
    *)    SCRIPT=$DIST/scripts/$TOOL.hs ;;
esac
[ -f "$SCRIPT" ] || { echo "bluehs: no such tool or script: $TOOL" >&2; exit 1; }
GHC_ENVIRONMENT=$DIST/hs/bsc.env export GHC_ENVIRONMENT
LD_LIBRARY_PATH=$DIST/SAT${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH} export LD_LIBRARY_PATH
# showrules/vcdcheck consult BLUESPECDIR; prefer the caller's, else a
# side-by-side bsc install (tarballs unpacked next to each other)
if [ -z "${BLUESPECDIR:-}" ] && [ -d "$DIST/../lib/Libraries" ]; then
    BLUESPECDIR=$(cd "$DIST/../lib" && pwd) export BLUESPECDIR
fi
exec "$DIST/hs/ghc/bin/runghc" "$SCRIPT" "$@"
EOF
chmod 755 "$DIST/bin/bluehs"

# ----------------------------------------------------------------------
# 6. Licensing: everything redistributed in this tarball

msg "generating LICENSES"
cp "$REPO"/LICENSES/LICENSE.ghc "$DIST/LICENSES/"
cp "$REPO"/LICENSES/LICENSE.stp "$REPO"/LICENSES/LICENSE.stp_components \
   "$REPO"/LICENSES/LICENSE.yices "$DIST/LICENSES/"
# Per-package name/version/license/copyright for every Haskell package in
# the tarball (boot libraries + store deps + bsc), via the transitive
# closure walker already used for the main tarball's LICENSE.ghc_pkgs
PATH="$DIST/hs/ghc/bin:$PATH" \
GHC_PACKAGE_PATH="$STORE/package.db:$GLOBALDB" \
    "$REPO/src/comp/make-ghc-pkg-info.sh" bsc \
    > "$DIST/LICENSES/LICENSE.ghc_pkgs"

cat > "$DIST/LICENSES/COPYING" <<EOF
The bluehs distribution redistributes the following components:

  * The Glasgow Haskell Compiler runtime and tools (ghc, runghc,
    ghc-pkg, boot libraries, RTS, bundled libffi)
      - See LICENSES/LICENSE.ghc
  * Haskell library packages (GHC boot libraries, packages from
    Hackage, and the bsc compiler library itself), enumerated with
    their licenses and copyrights in:
      - See LICENSES/LICENSE.ghc_pkgs
  * The STP SAT solver shared library (SAT/libstp.so*)
      - See LICENSES/LICENSE.stp and LICENSES/LICENSE.stp_components
  * The Yices SMT solver shared library (SAT/libyices.so*)
      - See LICENSES/LICENSE.yices

Not included, required from the host system at runtime: glibc, libgmp,
libtcl8.6, and a C compiler (used by GHC for library probing and CPP).
EOF

if [ ! -f "$GHC_ROOT/LICENSE" ]; then
    msg "NOTE: GHC installation carries no LICENSE file (ghcup layout);"
    msg "      shipped LICENSE.ghc is the repo's copy - release CI should"
    msg "      verify it matches the shipped GHC version's license text."
else
    cp "$GHC_ROOT/LICENSE" "$DIST/LICENSES/LICENSE.ghc"
fi

# ----------------------------------------------------------------------
# 7. Smoke test (isolated env) and tarball

msg "smoke testing"
SMOKEBO=$(ls "$REPO"/inst/lib/Libraries/*.bo 2>/dev/null | head -1)
if [ -n "$SMOKEBO" ]; then
    env -i PATH=/usr/bin:/bin HOME=/nonexistent \
        "$DIST/bin/bluehs" dumpbo "$SMOKEBO" > "$WORK/smoke.out"
    head -1 "$WORK/smoke.out" | grep -q "Internal Symbols" \
        || { echo "smoke test output unexpected" >&2; exit 1; }
    msg "smoke test passed ($(basename "$SMOKEBO"))"
else
    msg "WARNING: no inst/lib/Libraries/*.bo found - smoke test skipped"
fi

msg "creating $TARBALL"
tar -C "$OUT" --transform 's,^dist,bluehs,' -czf "$TARBALL" dist
msg "done: $TARBALL ($(du -h "$TARBALL" | cut -f1))"
