#!/usr/bin/env bash
# Install the bluehs distribution: a relocatable tree holding a pruned GHC
# runtime, a package store with the compiled bsc library and its
# dependencies, the SAT solver libraries, the tool entry scripts
# (src/comp/app), and the bluehs launcher.  Scripts run against the library
# with no Haskell toolchain installed; a C compiler is needed only by
# scripts that use CPP.
#
# The install directory sits inside a bsc installation (<prefix>/bluehs),
# and must be built from the same tree as that bsc: the library embeds the
# build version and rejects .ba files written by any other bsc.
#
# Prerequisites: a completed `make install-src` into <prefix>, ghc and cabal
# on PATH (the GHC that will be shipped), python3, and patchelf on Linux.
#
# Usage: util/bluehs/mk-dist.sh <prefix>/bluehs [work-dir]
#        (`make install-bluehs` runs it with inst/bluehs and build/bluehs)
# REUSE_WORK=1 keeps a previous run's library build, which cabal then updates.

set -euo pipefail

REPO=$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd)
[ $# -ge 1 ] || { echo "usage: $0 <prefix>/bluehs [work-dir]" >&2; exit 1; }
mkdir -p "$1"
DEST=$(cd "$1" && pwd)
PREFIX=$(dirname "$DEST")
WORK=${2:-$REPO/build/bluehs}
mkdir -p "$WORK"
WORK=$(cd "$WORK" && pwd)
DIST=$WORK/dist

# The Hackage index the dependencies resolve against, so that the commit,
# not the build date, fixes them
INDEX_STATE=2026-09-26T00:00:00Z

msg() { echo ">>> $*"; }
die() { echo "mk-dist.sh: $*" >&2; exit 1; }
# GNU and BSD sed disagree on -i
sed_inplace() { local f=$1; shift; sed "$@" "$f" > "$f.tmp" && mv "$f.tmp" "$f"; }
relpath() { python3 -c 'import os, sys; print(os.path.relpath(*sys.argv[1:]))' "$1" "$2"; }

case "$(uname -s)" in
    Linux)  DLL=so ;;
    Darwin) DLL=dylib ;;
    *) die "unsupported OS $(uname -s)" ;;
esac
command -v python3 >/dev/null || die "python3 is required"
[ $DLL = dylib ] || command -v patchelf >/dev/null || die "patchelf is required"
[ -x "$PREFIX/bin/bsc" ] || die "no bsc at $PREFIX/bin; run make install-src first"

# ----------------------------------------------------------------------
# 0. The GHC installation

GHC_REAL_BIN=$(dirname "$(readlink -f "$(command -v ghc)")")
# ghcup layout: <root>/bin/ghc -> symlink; real binaries in <root>/lib/ghc-*/bin
# or directly <root>/bin.  Find the root containing both bin/ and lib/.
GHC_ROOT=$(cd "$GHC_REAL_BIN/.." && pwd)
while [ ! -d "$GHC_ROOT/lib" ] || [ ! -d "$GHC_ROOT/bin" ]; do
    GHC_ROOT=$(dirname "$GHC_ROOT")
    [ "$GHC_ROOT" = "/" ] && die "cannot locate the GHC root"
done
GHC_VER=$(ghc --numeric-version)
msg "GHC $GHC_VER at $GHC_ROOT"

# The update scripts use `set -u` and expect these from the Makefile
export NOGIT=${NOGIT:-0}
export NOUPDATEBUILDVERSION=${NOUPDATEBUILDVERSION:-0}
(cd "$REPO/src/comp" && ./update-build-version.sh && ./update-build-system.sh)

if [ "${REUSE_WORK:-0}" != 1 ]; then rm -rf "$WORK/proj" "$WORK/store"; fi
rm -rf "$DIST"
mkdir -p "$DIST"/{bin,scripts,SAT,LICENSES,hs}

# ----------------------------------------------------------------------
# 1. Build the bsc library, and its dependencies into a fresh store
#    (out-of-repo project, so the repo's own dist-newstyle and env file are
#    untouched).  The library itself is built in place, not installed:
#    installing a local package goes through a source distribution, which
#    lacks the vendored solver sources the cabal hooks build.

msg "building bsc library (this compiles all modules at -O2)"
mkdir -p "$WORK/proj"
cat > "$WORK/proj/cabal.project" <<EOF
packages: $REPO
index-state: $INDEX_STATE

package bsc
  optimization: 2
  ghc-options: -j
EOF
(cd "$WORK/proj" && cabal --store-dir="$WORK/store" build bsc:lib:bsc \
    >"$WORK/cabal-build.log" 2>&1) \
    || { tail -30 "$WORK/cabal-build.log" >&2; exit 1; }

# cabal names the store's directory ghc-<version>, or in newer releases
# ghc-<version>-<abi hash>
STORE_SRC=
for d in "$WORK/store/ghc-$GHC_VER" "$WORK/store/ghc-$GHC_VER"-*; do
    [ -d "$d/package.db" ] && { STORE_SRC=$d; break; }
done
[ -n "$STORE_SRC" ] || die "no ghc-$GHC_VER store in $WORK/store"
STORE_NAME=$(basename "$STORE_SRC")

SOLVER_DIRS=("$REPO/src/vendor/stp/lib" "$REPO/src/vendor/yices/lib")
for d in "${SOLVER_DIRS[@]}"; do
    ls "$d"/*."$DLL"* >/dev/null 2>&1 || die "no solver library in $d"
done

# the in-place library's registration and build directory
INPLACE_CONF=$(ls "$WORK/proj/dist-newstyle/packagedb/ghc-$GHC_VER"/bsc-*-inplace.conf)
INPLACE_ID=$(sed -n 's/^id: *//p' "$INPLACE_CONF")
INPLACE_BUILD=$(awk '/^import-dirs:/{getline; print $1}' "$INPLACE_CONF")
[ -d "$INPLACE_BUILD" ] || die "cannot locate the in-place build ($INPLACE_BUILD)"

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
[ -d "$DIST/hs/ghc/$GHCLIBDIR_REL" ] || die "unexpected GHC layout"
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
mkdir -p "$DIST/hs/store"
cp -a "$STORE_SRC" "$DIST/hs/store/"
STORE=$DIST/hs/store/$STORE_NAME

find "$STORE" -name '*.a' -delete
rm -rf "$STORE/incoming"
find "$STORE" -name 'cabal-hash.txt' -delete

# The in-place library joins the store as one more package: its interface
# files and shared object, registered where the dependencies are
msg "adding the bsc library to the store"
mkdir -p "$STORE/$INPLACE_ID/lib"
(cd "$INPLACE_BUILD" && find . \( -name '*.hi' -o -name '*.dyn_hi' -o -name "libHS*.$DLL" \) -print0 \
    | cpio -0 -pdm --quiet "$STORE/$INPLACE_ID/lib")
# keep the fields the packaged library needs; the include and link
# settings of the build tree only served compiling it.  Of the C
# libraries, only the solvers are named: they are in the distribution,
# where GHC finds them by path.  The system libraries the library also
# uses (zlib, Tcl, the C++ runtime) load as dependencies of its shared
# object and of the solvers'; naming them would have GHC look each one up
# by its development-package name, and ask the C compiler when that fails.
awk 'BEGIN{skip=0} /^[^ \t]/{skip = /^(include-dirs|ld-options|library-dirs-static|data-dir):/ ? 1 : 0} !skip' \
    "$INPLACE_CONF" \
    | sed -e "s|$INPLACE_BUILD|\${pkgroot}/$INPLACE_ID/lib|g" \
          -e "s|^extra-libraries:.*|extra-libraries: stp yices|" \
    > "$STORE/package.db/$INPLACE_ID.conf"

# ${pkgroot} = the directory containing package.db
for conf in "$STORE"/package.db/*.conf; do
    sed_inplace "$conf" \
        -e "s|$STORE_SRC|\${pkgroot}|g" \
        -e "s|${SOLVER_DIRS[0]}|\${pkgroot}/../../../SAT|g" \
        -e "s|${SOLVER_DIRS[1]}|\${pkgroot}/../../../SAT|g"
    # Drop haddock-* fields INCLUDING their continuation lines (they point
    # at never-shipped docs; a bare sed of the header line would orphan the
    # indented value lines and break ghc-pkg's parser)
    awk 'BEGIN{skip=0} /^[^ \t]/{skip = /^haddock-(interfaces|html):/ ? 1 : 0} !skip' \
        "$conf" > "$conf.tmp" && mv "$conf.tmp" "$conf"
done
"$DIST/hs/ghc/bin/ghc-pkg" --package-db="$STORE/package.db" recache

# ----------------------------------------------------------------------
# 4. Package environment: the bsc library and everything it depends on,
#    boot packages included, and nothing else.  The store also holds the
#    build's setup dependencies (Cabal among them); exposed beside their
#    boot versions they would make every CPP script's version macros
#    ambiguous.

msg "writing package environment"
GLOBALDB=$(ls -d "$DIST/hs/ghc/lib/ghc-$GHC_VER/lib/package.conf.d")
{
    echo "clear-package-db"
    echo "global-package-db"
    echo "package-db store/$STORE_NAME/package.db"
    "$DIST/hs/ghc/bin/ghc-pkg" --package-db="$STORE/package.db" dump \
        | awk -v root="$INPLACE_ID" '
            /^id:/ { id = $2; next }
            /^depends:/ { field = "depends"; sub(/^depends:/, ""); addDeps(); next }
            /^[^ \t]/ { field = "" ; next }
            field == "depends" { addDeps() }
            function addDeps(   i) { for (i = 1; i <= NF; i++) deps[id] = deps[id] " " $i }
            END {
                queue[1] = root; n = 1; seen[root] = 1
                for (i = 1; i <= n; i++) {
                    print "package-id " queue[i]
                    split(deps[queue[i]], ds, " ")
                    for (j in ds) if (ds[j] != "" && !(ds[j] in seen)) { seen[ds[j]] = 1; queue[++n] = ds[j] }
                }
            }'
} > "$DIST/hs/bsc.env"

# ----------------------------------------------------------------------
# 5. SAT libs, scripts, launcher

msg "copying SAT libs, scripts and launcher"
for d in "${SOLVER_DIRS[@]}"; do cp -a "$d"/*."$DLL"* "$DIST/SAT/"; done
# every tool entry file runs as a script except bluetcl, whose main is C
for f in "$REPO"/src/comp/app/*.hs; do
    case "$(basename "$f")" in
        BlueTcl.hs|bluetcl_Main.hs) ;;
        *) cp "$f" "$DIST/scripts/" ;;
    esac
done
cp "$REPO/util/bluehs/bluehs" "$DIST/bin/bluehs"
chmod 755 "$DIST/bin/bluehs"

# ----------------------------------------------------------------------
# 6. Library paths: every search path and dependency that names the build
#    machine is rewritten relative to the file, or dropped

# The shipped counterpart of a build-machine directory; fails for one
# that has none.  Directories elsewhere (the system's) are kept as they are.
shipped_dir() {
    case "$1" in
        "$STORE_SRC" | "$STORE_SRC"/*) echo "$STORE${1#"$STORE_SRC"}" ;;
        "$INPLACE_BUILD"*) echo "$STORE/$INPLACE_ID/lib${1#"$INPLACE_BUILD"}" ;;
        "$GHC_ROOT"/*) echo "$DIST/hs/ghc${1#"$GHC_ROOT"}" ;;
        "${SOLVER_DIRS[0]}" | "${SOLVER_DIRS[1]}") echo "$DIST/SAT" ;;
        "$WORK"/* | "$REPO"/*) return 1 ;;
        *) echo "$1" ;;
    esac
}

# A search path as the file should record it
search_entry() {  # file, directory, origin token
    local d
    d=$(shipped_dir "$2") || return 1
    case "$d" in
        "$DIST"/*) echo "$3/$(relpath "$d" "$(dirname "$1")")" ;;
        *) echo "$d" ;;
    esac
}

relocate_elf() {
    local f=$1 r e new=()
    local IFS=:
    for r in $(patchelf --print-rpath "$f"); do
        e=$(search_entry "$f" "$r" '$ORIGIN') && new+=("$e")
    done
    patchelf --set-rpath "${new[*]}" "$f"
}

relocate_macho() {
    local f=$1 r e dep id
    for r in $(otool -l "$f" | awk '$1 == "cmd" { rp = ($2 == "LC_RPATH") } rp && $1 == "path" { print $2 }'); do
        install_name_tool -delete_rpath "$r" "$f"
        if e=$(search_entry "$f" "$r" @loader_path); then
            install_name_tool -add_rpath "$e" "$f" 2>/dev/null || true
        fi
    done
    id=$(otool -D "$f" | sed -n 2p)
    case "$id" in
        /*) shipped_dir "$(dirname "$id")" >/dev/null || install_name_tool -id "@rpath/$(basename "$id")" "$f" ;;
    esac
    for dep in $(otool -L "$f" | awk 'NR > 1 { print $1 }'); do
        [ "$dep" = "$id" ] && continue
        case "$(shipped_dir "$(dirname "$dep")" 2>/dev/null || echo dropped)" in
            "$DIST"/* | dropped)
                install_name_tool -change "$dep" "@rpath/$(basename "$dep")" "$f" ;;
        esac
    done
    codesign -f -s - "$f" 2>/dev/null
}

# Search paths and dependencies of a file that still name the build machine
leaks() {
    local f=$1
    if [ $DLL = so ]; then
        patchelf --print-rpath "$f"; patchelf --print-needed "$f"
    else
        otool -l "$f" | awk '$1 == "path" || $1 == "name" { print $2 }'
    fi | grep -F -e "$WORK" -e "$REPO" -e "$GHC_ROOT" || true
}

msg "rewriting library paths"
LIBS=()
while IFS= read -r -d '' f; do LIBS+=("$f"); done \
    < <(find "$STORE" "$DIST/SAT" -type f -name "*.$DLL*" -print0)
for f in "${LIBS[@]}"; do
    chmod u+w "$f"
    case "$f" in
        */libHSbsc-*) if [ $DLL = so ]; then strip "$f"; else strip -x "$f"; fi ;;
    esac
    if [ $DLL = so ]; then relocate_elf "$f"; else relocate_macho "$f"; fi
done
for f in "${LIBS[@]}"; do
    l=$(leaks "$f")
    [ -z "$l" ] || die "$f still names the build machine: $l"
done

# ----------------------------------------------------------------------
# 7. Licensing: everything redistributed in the distribution

msg "generating LICENSES"
cp "$REPO"/LICENSES/LICENSE.ghc "$DIST/LICENSES/"
cp "$REPO"/LICENSES/LICENSE.stp "$REPO"/LICENSES/LICENSE.stp_components \
   "$REPO"/LICENSES/LICENSE.yices "$DIST/LICENSES/"
# Per-package name/version/license/copyright for every Haskell package in
# the distribution (boot libraries + store deps + bsc), via the transitive
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
  * The STP SAT solver shared library (SAT/libstp.*)
      - See LICENSES/LICENSE.stp and LICENSES/LICENSE.stp_components
  * The Yices SMT solver shared library (SAT/libyices.*)
      - See LICENSES/LICENSE.yices

Not included, required from the host system at runtime: the C and C++
runtimes, libgmp, zlib, Tcl, and, for scripts that use CPP, a C compiler.
EOF

if [ ! -f "$GHC_ROOT/LICENSE" ]; then
    msg "NOTE: GHC installation carries no LICENSE file (ghcup layout);"
    msg "      shipped LICENSE.ghc is the repo's copy - release CI should"
    msg "      verify it matches the shipped GHC version's license text."
else
    cp "$GHC_ROOT/LICENSE" "$DIST/LICENSES/LICENSE.ghc"
fi

# ----------------------------------------------------------------------
# 8. Install, then smoke test a copy in another directory with the build
#    tree out of reach, under an empty environment

msg "installing into $DEST"
rm -rf "$DEST"
mv "$DIST" "$DEST"

msg "smoke testing"
SMOKE=$(mktemp -d)
cp -a "$DEST" "$SMOKE/bluehs"
cat > "$SMOKE/probe.hs" <<'EOF'
import Control.Monad (unless)
import qualified STP
import System.Exit (die)
import Version (bscVersionStr)
import qualified Yices
main :: IO ()
main = do
    _ <- Yices.checkVersion
    STP.checkVersion >>= flip unless (die "STP: version check failed")
    putStrLn (bscVersionStr True)
EOF
mv "$WORK" "$WORK.hidden"
trap 'mv "$WORK.hidden" "$WORK"; rm -rf "$SMOKE"' EXIT
run() { env -i PATH=/usr/bin:/bin HOME=/nonexistent "$SMOKE/bluehs/bin/bluehs" "$@"; }
run dumpbo "$PREFIX/lib/Libraries/Prelude.bo" > "$SMOKE/dumpbo.out"
head -1 "$SMOKE/dumpbo.out" | grep -q "Internal Symbols" \
    || die "smoke test: dumpbo output unexpected"
LIBRARY=$(run "$SMOKE/probe.hs")
COMPILER=$("$PREFIX/bin/bsc" -v | head -1)
[ "$LIBRARY" = "$COMPILER" ] \
    || die "the library and $PREFIX/bin/bsc differ: '$LIBRARY' vs '$COMPILER'"
msg "done: $DEST ($(du -sh "$DEST" | cut -f1)), $LIBRARY"
