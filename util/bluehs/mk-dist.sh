#!/usr/bin/env bash
# Install the bluehs distribution: a relocatable tree holding a pruned GHC
# runtime, a package store with the compiled bsc libraries and their
# dependencies, the SAT solver libraries, the tool entry scripts (every
# program of bsc.cabal but bluetcl), and the bluehs launcher.  Scripts run
# against the libraries with no Haskell toolchain installed; a C compiler is
# needed only by scripts that use CPP.
#
# The tree is meant to be the same bytes whatever the checkout directory
# and the build's parallelism, as the compiler build is (doc/cabal.md
# section 1), given a work directory at the same place in the checkout (as
# make's is) or at the same path.  The dependencies come from the cabal
# store, whose path the files built there record (a Paths_ module's
# directories, a shared object's search paths and build id), so that path
# must not be the checkout's.  The solvers are the installed tree's, built
# by make from the vendored sources, which the library links by name with
# no directory recorded (doc/cabal.md section 3); they are stripped of the
# debug information that names their build directory and, on Linux, of the
# build ID hashed from it.  Only libraries are shipped, no build tool.
#
# The programs are those the library's post-build hook lists (SetupHooks.hs),
# so a step that adds one changes nothing here.
#
# The install directory sits inside a bsc installation (<prefix>/bluehs),
# and must be built from the same tree as that bsc: the library embeds the
# build version and rejects .ba files written by any other bsc.
#
# Prerequisites: a completed `make install-src` into <prefix>, ghc (or the
# compiler GHC names, which is the one shipped) and cabal (or what CABAL
# names) on PATH, python3, cpio, and patchelf on Linux.
#
# Usage: util/bluehs/mk-dist.sh <prefix>/bluehs [work-dir]
#        (`make install-bluehs` runs it with inst/bluehs and build/bluehs)
# REUSE_WORK=1 keeps a previous run's library build, which cabal then updates.
# GHC, CABAL, GHCJOBS, GHCRTSFLAGS and BSC_BUILD mean what they do to make
# (doc/cabal.md), which passes them on; the checkout's cabal.project.local
# and .freeze apply as they do to its own build.

set -euo pipefail

# canonical, as the in-place registrations record the build directories under it
REPO=$(cd "$(dirname "$(readlink -f "$0")")/../.." && pwd -P)
[ $# -ge 1 ] || { echo "usage: $0 <prefix>/bluehs [work-dir]" >&2; exit 1; }
# it is replaced at the end, so it must be empty or a previous installation
[ ! -d "$1" ] || [ -z "$(ls -A "$1")" ] || [ -f "$1/hs/bsc.env" ] \
    || { echo "$0: $1 is neither empty nor a bluehs installation" >&2; exit 1; }
mkdir -p "$1"
DEST=$(cd "$1" && pwd)
PREFIX=$(dirname "$DEST")
# The solvers the installed compiler carries, built by make from the vendored
# sources: the library links them by name and records no directory
# (doc/cabal.md section 3), so the build below is pointed at them the way the
# make build's is, and the distribution's copies are these.
SOLVER_DIR=$PREFIX/lib/SAT
WORK=${2:-$REPO/build/bluehs}
mkdir -p "$WORK"
WORK=$(cd "$WORK" && pwd -P)
DIST=$WORK/dist

msg() { echo ">>> $*"; }
die() { echo "mk-dist.sh: $*" >&2; exit 1; }
# GNU and BSD sed disagree on -i
sed_inplace() { local f=$1; shift; sed "$@" "$f" > "$f.tmp" && mv "$f.tmp" "$f"; }
relpath() { python3 -c 'import os, sys; print(os.path.relpath(*sys.argv[1:]))' "$1" "$2"; }

# ghc-pkg writes a database's package.cache in the directory's listing
# order, which on ext4 follows a per-filesystem hash, so one set of packages
# gives different bytes on different machines. Rebuild it from a fresh
# database the packages are registered into in a fixed order: the entries
# are those a recache would read, ${pkgroot} stays symbolic, and the .conf
# files stay as they are, so the bytes depend on the packages alone.
sorted_cache() {  # package database directory
    local db=$1 scratch=$WORK/db.sorted conf
    local ghcpkg=$DIST/hs/ghc/lib/ghc-$GHC_VER/bin/ghc-pkg-$GHC_VER
    rm -rf "$scratch"
    "$ghcpkg" init "$scratch"
    # registered newest first: the reverse of the sorted names lists them sorted
    for conf in $(cd "$db" && ls *.conf | LC_ALL=C sort -r); do
        "$ghcpkg" --global-package-db="$scratch" --no-user-package-db \
            register --force --no-expand-pkgroot "$db/$conf" > /dev/null 2>&1 \
            || die "sorted_cache: registering $conf"
    done
    cp "$scratch/package.cache" "$db/package.cache"
    rm -rf "$scratch"
}

case "$(uname -s)" in
    Linux)  DLL=so ;;
    Darwin) DLL=dylib ;;
    *) die "unsupported OS $(uname -s)" ;;
esac
# CABAL may carry options, as make's does
read -r -a CABAL_CMD <<< "${CABAL:-cabal}"
command -v "${CABAL_CMD[0]}" >/dev/null || die "no ${CABAL_CMD[0]} on PATH"
command -v python3 >/dev/null || die "python3 is required"
command -v cpio >/dev/null || die "cpio is required"
[ $DLL = dylib ] || command -v patchelf >/dev/null || die "patchelf is required"
[ -x "$PREFIX/bin/bsc" ] || die "no bsc at $PREFIX/bin; run make install-src first"

# ----------------------------------------------------------------------
# 0. The GHC installation: the directory of its libdir, which in a bindist
#    or ghcup layout is <prefix>/lib/ghc-<version>, holding lib/ and the
#    real programs in bin/.  That directory is what ships, not the prefix,
#    which may be /usr/local.

GHC_BIN=$(command -v "${GHC:-ghc}") || die "no ${GHC:-ghc} on PATH"
GHC_VER=$("$GHC_BIN" --numeric-version)
GHC_TOP=$(dirname "$("$GHC_BIN" --print-libdir)")
[ -x "$GHC_TOP/bin/ghc-$GHC_VER" ] && [ -d "$GHC_TOP/lib/package.conf.d" ] \
    || die "unexpected GHC layout: no bin/ghc-$GHC_VER and lib/package.conf.d in $GHC_TOP"
# Files may record the directory as GHC names it or as it resolves
GHC_TOP_REAL=$(cd "$GHC_TOP" && pwd -P)
msg "GHC $GHC_VER at $GHC_TOP"

if [ "${REUSE_WORK:-0}" != 1 ]; then rm -rf "$WORK/proj"; fi
rm -rf "$DIST"
mkdir -p "$DIST"/{bin,scripts,SAT,LICENSES,hs}

# ----------------------------------------------------------------------
# 1. Build the libraries, and their dependencies into the cabal store.  The
#    project is the repository's own, copied with its package paths made
#    absolute and without its environment-file setting, and built from
#    another directory: the checkout's dist-newstyle and .ghc.environment.*
#    (what the launcher uses in a checkout) are untouched.  The libraries
#    themselves are built in place, not installed.  The build version is the
#    checkout's src/comp/BuildVersion.hs, which make refreshed for
#    install-src, so the library and the bsc installed from this tree carry
#    the same stamp; the smoke test checks that they do.
#    The dependencies go into the store cabal uses for everything else, not
#    one under the checkout: what a package records of the store it was
#    built in would otherwise name the checkout.

msg "building the bsc libraries (this compiles every module at -O2)"
mkdir -p "$WORK/proj"
{
    echo "-- Generated by util/bluehs/mk-dist.sh from $REPO/cabal.project."
    # packages: either on one line or one package per indented line under it
    awk -v repo="$REPO" '
        function absolute(p) { sub(/^[ \t]+/, "", p); sub(/[ \t]+$/, "", p); return (p == "." ? repo : repo "/" p) }
        /^packages:/ {
            inpk = 1; rest = $0; sub(/^packages:[ \t]*/, "", rest)
            if (rest == "") { print; next }
            n = split(rest, ps, /[ \t,]+/); print "packages:"
            for (i = 1; i <= n; i++) if (ps[i] != "") print "  " absolute(ps[i])
            next
        }
        inpk && /^[ \t]+[^ \t]/ { print "  " absolute($0); next }
        inpk { inpk = 0 }
        /^write-ghc-environment-files:/ { next }
        { print }' "$REPO/cabal.project"
} > "$WORK/proj/cabal.project"
# The project pins the Hackage index its dependencies resolve against, so
# this build and the installed compiler's take the same versions
grep -qi '^index-state[[:space:]]*:' "$WORK/proj/cabal.project" || die "$REPO/cabal.project pins no index-state"
CABAL_ARGS=(-w "$GHC_BIN")
PROJECT=cabal.project
rm -f "$WORK/proj"/cabal.project.*
if [ -n "${BSC_BUILD:-}" ]; then
    # a variant imports cabal.project, which it finds beside it here too
    PROJECT=cabal.project.$(echo "$BSC_BUILD" | tr A-Z a-z)
    [ -f "$REPO/$PROJECT" ] || die "BSC_BUILD=$BSC_BUILD: no $PROJECT"
    cp "$REPO/$PROJECT" "$WORK/proj/"
    CABAL_ARGS+=("--project-file=$PROJECT")
fi
for f in "$PROJECT.local" "$PROJECT.freeze"; do
    [ ! -f "$REPO/$f" ] || cp "$REPO/$f" "$WORK/proj/"
done
[ -z "${GHCJOBS:-}" ] || CABAL_ARGS+=("-j$GHCJOBS")
[ -z "${GHCRTSFLAGS:-}" ] || CABAL_ARGS+=("--ghc-options=$GHCRTSFLAGS")
(cd "$WORK/proj" && LIBRARY_PATH="$SOLVER_DIR${LIBRARY_PATH:+:$LIBRARY_PATH}" \
    "${CABAL_CMD[@]}" build "${CABAL_ARGS[@]}" bsc:lib:bsc >"$WORK/cabal-build.log" 2>&1) \
    || { tail -30 "$WORK/cabal-build.log" >&2; exit 1; }
PLAN=$WORK/proj/dist-newstyle/cache/plan.json
[ -f "$PLAN" ] || die "no build plan at $PLAN"

# The libraries the bsc library is built from, through to the boot
# packages: what a script can import, so what bsc.env exposes and what the
# store copy ships.  A unit built per package lists its components; only
# its library's dependencies link into the library.
CLOSURE=$(python3 -c '
import json, sys
units = {u["id"]: u for u in json.load(open(sys.argv[1]))["install-plan"]}
def depends(u):
    if "components" in u:
        return u["components"].get("lib", {}).get("depends", [])
    return u.get("depends", [])
todo = [i for i, u in units.items()
        if u["pkg-name"] == "bsc" and u.get("component-name", "lib") == "lib"]
seen = set(todo)
while todo:
    for d in depends(units[todo.pop()]):
        if d not in seen:
            seen.add(d)
            todo.append(d)
for i in sorted(seen):
    print(units[i].get("style", "pre-existing"), i)
' "$PLAN")
[ -n "$CLOSURE" ] || die "no bsc library in the plan $PLAN"

# cabal names the store's directory after the compiler's unit id
# (ghc-<version>-<hash>), or ghc-<version> for a GHC that reports none
STORE_ROOT=$(cd "$WORK/proj" && "${CABAL_CMD[@]}" path -w "$GHC_BIN" --store-dir)
STORE_NAME=$("$GHC_BIN" --info | sed -n 's/.*("Project Unit Id","\([^"]*\)").*/\1/p')
STORE_SRC=$STORE_ROOT/${STORE_NAME:=ghc-$GHC_VER}
[ -d "$STORE_SRC/package.db" ] || die "no store for GHC $GHC_VER at $STORE_SRC"

# The in-place libraries: registration, id and build directory of every
# package of the project.  A package without modules of its own has no
# build directory to copy from.
INPLACE_CONFS=() INPLACE_IDS=() INPLACE_BUILDS=()
BSC_ID= BSC_DIR=
for conf in "$WORK/proj/dist-newstyle/packagedb/ghc-$GHC_VER"/*-inplace.conf; do
    name=$(sed -n 's/^name: *//p' "$conf")
    id=$(sed -n 's/^id: *//p' "$conf")
    build=$(awk '/^import-dirs:/ { getline; if ($0 ~ /^[ \t]/) print $1 }' "$conf")
    [ -z "$build" ] || [ -d "$build" ] || die "cannot locate the in-place build of $name ($build)"
    INPLACE_CONFS+=("$conf"); INPLACE_IDS+=("$id"); INPLACE_BUILDS+=("$build")
    [ "$name" != bsc ] || { BSC_ID=$id; BSC_DIR=$build; }
done
[ -n "$BSC_ID" ] || die "no in-place bsc package in the project"

# ----------------------------------------------------------------------
# 2. Pruned GHC runtime

msg "copying and pruning GHC runtime"
mkdir -p "$DIST/hs/ghc/bin" "$DIST/hs/ghc/lib/ghc-$GHC_VER"
cp -a "$GHC_TOP/." "$DIST/hs/ghc/lib/ghc-$GHC_VER/"
# writable, as the pruning and a later run's rm need, whatever the install's
# modes (read-only in a Nix store)
chmod -R u+w "$DIST/hs/ghc"
# A link out of the installation (Debian's lib/package.conf.d points into
# /var/lib/ghc) would make the rewrites below write into the system's files
# and leave the tree dependent on the build machine: replace it by its target
find "$DIST/hs/ghc" -type l -print0 | while IFS= read -r -d '' link; do
    target=$(readlink -f "$link")
    [ -e "$target" ] || die "dangling link $link"
    case "$target" in
        "$DIST/hs/ghc"/*) ;;
        *) rm "$link"; cp -a "$target" "$link"; chmod -R u+w "$link" ;;
    esac
done

# Drop the profiling, debugging and static ways, interface files included
# (keep libCffi*.a: shipped static-only, and deleting it makes `ghc-pkg
# check` report rts as broken)
find "$DIST/hs/ghc/lib" \( -name '*.p_hi' -o -name '*.p_dyn_hi' -o -name '*_p.a' \
    -o -name "libHS*_p-ghc*.$DLL" -o -name "libHS*_debug-ghc*.$DLL" \) -delete
find "$DIST/hs/ghc/lib" -name '*.a' ! -name 'libCffi*' -delete
# Drop tools scripts never need, and haddock's page templates
for tool in haddock hsc2hs hpc hp2ps ghc-iserv ghc-iserv-prof; do
    find "$DIST/hs/ghc/lib" -path '*/bin/*' -name "$tool*" ! -name 'ghc-iserv-dyn*' -delete
done
rm -rf "$DIST/hs/ghc/lib/ghc-$GHC_VER/lib/html" "$DIST/hs/ghc/lib/ghc-$GHC_VER/lib/latex"

# Self-locating bin/ wrappers in place of GHC's, which name the build
# machine's paths.  ghc/ghc-pkg/runghc have real binaries under
# lib/ghc-<ver>/bin; ghci and runhaskell are pure aliases.
GHCLIBDIR_REL="lib/ghc-$GHC_VER/lib"
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

# GHC's loader looks up each library a package names by asking the C
# compiler (--print-file-name).  The system libraries the boot packages name
# (libc, libm, libgmp, ...) already load as dependencies of GHC and of the
# packages' shared objects, so dropping the names lets scripts run where no
# C compiler is reachable.
for conf in "$DIST/hs/ghc/$GHCLIBDIR_REL"/package.conf.d/*.conf; do
    awk 'BEGIN{skip=0} /^[^ \t]/{skip = /^extra-libraries:/ ? 1 : 0} !skip' \
        "$conf" > "$conf.tmp" && mv "$conf.tmp" "$conf"
done
sorted_cache "$DIST/hs/ghc/$GHCLIBDIR_REL/package.conf.d"

# ----------------------------------------------------------------------
# 3. Relocatable store

# The closure's units that live in the store, as built for this project.
# The store holds whatever else was ever built on this machine, and the
# plan's build tools (hsc2hs) and setup dependencies (Cabal), none of which
# a script needs.
msg "relocating package store"
STORE=$DIST/hs/store/$STORE_NAME
mkdir -p "$STORE/package.db"
echo "$CLOSURE" | awk '$1 == "global" { print $2 }' | while read -r id; do
    [ -d "$STORE_SRC/$id" ] || die "the plan's $id is not in the store $STORE_SRC"
    cp -a "$STORE_SRC/$id" "$STORE/"
    cp "$STORE_SRC/package.db/$id.conf" "$STORE/package.db/"
    # On macOS cabal-install keeps every unit's dynamic library in the
    # store's one lib directory, to stay under the Mach-O load command size
    # limit (cabal-install's ProjectPlanning, dynlibdir), and the unit's
    # registration and the rpaths of what links it name that directory.
    for dl in "$STORE_SRC/lib/libHS$id-ghc"*."$DLL"; do
        [ -e "$dl" ] || continue
        mkdir -p "$STORE/lib" && cp -a "$dl" "$STORE/lib/"
    done
done
[ -n "$(ls "$STORE/package.db")" ] || die "no dependency of bsc found in $STORE_SRC"

find "$STORE" -name '*.a' -delete
find "$STORE" -name 'cabal-hash.txt' -delete

# The in-place libraries join the store as more packages: their interface
# files and shared objects, registered where the dependencies are
msg "adding the bsc libraries to the store"
for i in "${!INPLACE_IDS[@]}"; do
    id=${INPLACE_IDS[$i]} build=${INPLACE_BUILDS[$i]}
    mkdir -p "$STORE/$id/lib"
    if [ -n "$build" ]; then
        (cd "$build" && find . \( -name '*.hi' -o -name '*.dyn_hi' -o -name "libHS*.$DLL" \) -print0 \
            | cpio -0 -pdm --quiet "$STORE/$id/lib")
    fi
    # Keep the fields the packaged library needs; the include and link
    # settings of the build tree only served compiling it.  Of the C
    # libraries, only the solvers are named, by the package whose build
    # named them: they are in the distribution, where GHC finds them by
    # path.  The system library the library also names, the C++ runtime,
    # loads as a dependency of the shared objects and of the solvers';
    # naming it would have GHC look it up by its
    # development-package name, and ask the C compiler when that fails.
    # A field is its header line and the indented lines after it.
    awk '
        function flush() {
            if (block == "") return
            if (field ~ /^(include-dirs|ld-options|library-dirs-static|data-dir)$/) ;
            else if (field == "extra-libraries") {
                if (block ~ /[ \t\n](stp|yices)([ \t\n]|$)/) print "extra-libraries: stp yices"
            } else print block
            block = ""
        }
        /^[^ \t]/ { flush(); field = $0; sub(/:.*/, "", field); block = $0; next }
        { block = block "\n" $0 }
        END { flush() }' "${INPLACE_CONFS[$i]}" \
        > "$STORE/package.db/$id.conf"
    [ -z "$build" ] || sed_inplace "$STORE/package.db/$id.conf" -e "s|$build|\${pkgroot}/$id/lib|g"
done

# ${pkgroot} = the directory containing package.db
for conf in "$STORE"/package.db/*.conf; do
    sed_inplace "$conf" -e "s|$STORE_SRC|\${pkgroot}|g"
    # The solvers for GHC's loader, which opens a package's extra-libraries
    # by their link names from the package's library directories: the
    # registration names none (doc/cabal.md section 3), so the shipped one
    # gets SAT.
    if [ "$conf" = "$STORE/package.db/$BSC_ID.conf" ]; then
        awk '{ print } /^(library-dirs|dynamic-library-dirs):/ { print "    ${pkgroot}/../../../SAT" }' \
            "$conf" > "$conf.tmp" && mv "$conf.tmp" "$conf"
    fi
    # Drop haddock-* fields INCLUDING their continuation lines (they point
    # at never-shipped docs; a bare sed of the header line would orphan the
    # indented value lines and break ghc-pkg's parser)
    awk 'BEGIN{skip=0} /^[^ \t]/{skip = /^haddock-(interfaces|html):/ ? 1 : 0} !skip' \
        "$conf" > "$conf.tmp" && mv "$conf.tmp" "$conf"
done
sorted_cache "$STORE/package.db"

# ----------------------------------------------------------------------
# 4. Package environment: the bsc package and everything it depends on,
#    boot packages included, and nothing else.  The other boot packages
#    stay hidden, as they are to the bsc package itself.

msg "writing package environment"
GLOBALDB=$(ls -d "$DIST/hs/ghc/lib/ghc-$GHC_VER/lib/package.conf.d")
{
    echo "clear-package-db"
    echo "global-package-db"
    echo "package-db store/$STORE_NAME/package.db"
    echo "$CLOSURE" | awk '{ print "package-id " $2 }'
} > "$DIST/hs/bsc.env"

# ----------------------------------------------------------------------
# 5. SAT libs, scripts, launcher

msg "copying SAT libs, scripts and launcher"
cp -a "$SOLVER_DIR"/*."$DLL"* "$DIST/SAT/"
# Every program of bsc.cabal runs as a script except bluetcl, whose
# executable compiles in a C shim (bluetcl_shim.c) that hands control to
# Tcl, which an interpreted run cannot supply.  The programs and their entry
# files are the list the library's post-build hook writes beside the build
# directory (SetupHooks.hs): one "<name> <path>" line each, the path relative
# to the checkout.  The launcher finds a script by the program's name.
PROGRAMS=$(dirname "$BSC_DIR")/programs
[ -f "$PROGRAMS" ] || die "no $PROGRAMS (the post-build hook of SetupHooks.hs writes it)"
while read -r name path; do
    [ "$name" != bluetcl ] || continue
    cp "$REPO/$path" "$DIST/scripts/$name.hs"
done < "$PROGRAMS"
[ -n "$(ls "$DIST/scripts")" ] || die "no programs listed in $PROGRAMS"
cp "$REPO/util/bluehs/bluehs" "$DIST/bin/bluehs"
chmod 755 "$DIST/bin/bluehs"

# ----------------------------------------------------------------------
# 6. Library paths: every search path and dependency that names the build
#    machine is rewritten relative to the file, or dropped

# The shipped counterpart of a build-machine directory; fails for one
# that has none.  Directories elsewhere (the system's) are kept as they are.
shipped_dir() {
    local i d
    case "$1" in
        "$STORE_SRC" | "$STORE_SRC"/*) echo "$STORE${1#"$STORE_SRC"}"; return ;;
        "$GHC_TOP" | "$GHC_TOP"/*) echo "$DIST/hs/ghc/lib/ghc-$GHC_VER${1#"$GHC_TOP"}"; return ;;
        "$GHC_TOP_REAL" | "$GHC_TOP_REAL"/*)
            echo "$DIST/hs/ghc/lib/ghc-$GHC_VER${1#"$GHC_TOP_REAL"}"; return ;;
    esac
    for i in "${!INPLACE_IDS[@]}"; do
        [ -n "${INPLACE_BUILDS[$i]}" ] || continue
        case "$1" in
            "${INPLACE_BUILDS[$i]}"*)
                echo "$STORE/${INPLACE_IDS[$i]}/lib${1#"${INPLACE_BUILDS[$i]}"}"; return ;;
        esac
    done
    case "$1" in
        # the library's own rpath for the solvers (cabal.project): SAT here
        '$ORIGIN/../lib/SAT' | '@loader_path/../lib/SAT') echo "$DIST/SAT"; return ;;
        "$WORK"/* | "$REPO"/*) return 1 ;;
        /*) echo "$1" ;;
        *) return 1 ;;
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
    # the solvers record no rpath, and bash 3 rejects an empty array under set -u
    patchelf --set-rpath "${new[*]-}" "$f"
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
    codesign -f -s - "$f" 2>"$WORK/codesign.err" || die "codesign $f: $(cat "$WORK/codesign.err")"
}

# Search paths and dependencies of a file that still name the build machine
leaks() {
    local f=$1 entries
    if [ $DLL = so ]; then
        entries=$(patchelf --print-rpath "$f" | tr : '\n'; patchelf --print-needed "$f")
    else
        entries=$(otool -l "$f" | awk '$1 == "path" || $1 == "name" { print $2 }')
    fi
    # an entry under a build-machine directory, or that directory itself
    { printf '%s\n' "$entries" | grep -F -e "$WORK/" -e "$REPO/" -e "$GHC_TOP/" -e "$GHC_TOP_REAL/" -e "$STORE_SRC/"
      printf '%s\n' "$entries" | grep -xF -e "$WORK" -e "$REPO" -e "$GHC_TOP" -e "$GHC_TOP_REAL" -e "$STORE_SRC"; } || true
}

msg "rewriting library paths"
LIBS=()
while IFS= read -r -d '' f; do LIBS+=("$f"); done \
    < <(find "$STORE" "$DIST/SAT" -type f -name "*.$DLL*" -print0)
for f in "${LIBS[@]}"; do
    chmod u+w "$f"
    # The bsc library and the solvers carry symbols and debug information
    # no script needs; the solvers' names their build directory (stp's
    # minisat core is compiled with -g), and so does the build ID the linker
    # hashed from it, which identifies debug information not shipped.
    case "$f" in
        */SAT/*) if [ $DLL = so ]; then strip --remove-section=.note.gnu.build-id "$f"; else strip -S -x "$f"; fi ;;
        */libHSbsc-*) if [ $DLL = so ]; then strip "$f"; else strip -S -x "$f"; fi ;;
    esac
    if [ $DLL = so ]; then relocate_elf "$f"; else relocate_macho "$f"; fi
done
for f in "${LIBS[@]}"; do
    l=$(leaks "$f")
    [ -z "$l" ] || die "$f still names the build machine: $l"
done
# Nor may any other file name the checkout, the work directory or the GHC
# installation.  The store's path stays in what was built there (a Paths_
# module's directories), unused, and so do the work directory's and GHC's in
# the interface files of modules that use CPP, which list the headers it
# read (cabal_macros.h, ghcversion.h) for GHC to check when recompiling
# them.  cabal names the work directory's relative to the checkout when it
# is inside it, and in full otherwise, where only the checkout's own path
# followed by / is one of its files.  Each path is matched with its /, so a
# short checkout path (/build) does not match unrelated strings.
l=$( (LC_ALL=C grep -rlaF --exclude='*.hi' --exclude='*.dyn_hi' \
          -e "$WORK/" -e "$REPO/" -e "$GHC_TOP/" -e "$GHC_TOP_REAL/" "$DIST"
      LC_ALL=C grep -rlaF --include='*.hi' --include='*.dyn_hi' -e "$REPO/" "$DIST") || true)
[ -z "$l" ] || die "these files still name the build machine: $l"

# ----------------------------------------------------------------------
# 7. Licensing: everything redistributed in the distribution

msg "generating LICENSES"
# the release's texts (release/Makefile), for the same compiler sources and
# solvers, and the terms of BSC's own sources
for f in LICENSE.ghc LICENSE.hbc LICENSE.parsec LICENSE.stp LICENSE.stp_components \
         LICENSE.yices LICENSE.yices-painless; do
    cp "$REPO/LICENSES/$f" "$DIST/LICENSES/"
done
cp "$REPO/COPYING" "$DIST/LICENSES/COPYING.bsc"
# GHC's own text, where its installation keeps it beside its packages'
for f in "$GHC_TOP"/../../share/doc/*/ghc-"$GHC_VER"/LICENSE; do
    [ ! -f "$f" ] || { cp "$f" "$DIST/LICENSES/LICENSE.ghc"; break; }
done
# The libffi a GHC bindist carries for its runtime system: a shared library,
# and the static libCffi kept above
LIBFFI=
if ls "$DIST/hs/ghc/$GHCLIBDIR_REL"/*/libffi* > /dev/null 2>&1 \
    || ls "$DIST/hs/ghc/$GHCLIBDIR_REL"/*/rts-*/libCffi* > /dev/null 2>&1; then
    cp "$REPO/LICENSES/LICENSE.libffi" "$DIST/LICENSES/"
    LIBFFI="
  * The libffi library bundled with GHC
      - See LICENSES/LICENSE.libffi"
fi
# Name, version, license and copyright of every Haskell package of both
# databases, as GHC's programs link packages bsc does not use, via the
# walker that writes the release's LICENSE.ghc_pkgs.  Those of GHC's own
# packages that declare no license are GHC's (LICENSE.ghc).
export GHC_PACKAGE_PATH="$STORE/package.db:$GLOBALDB"
NAMES=$("$DIST/hs/ghc/bin/ghc-pkg" field '*' name,license \
    | paste - - | awk '$4 != "NONE" { print $2 }' | LC_ALL=C sort -u)
# shellcheck disable=SC2086  # one argument per package name
PATH="$DIST/hs/ghc/bin:$PATH" "$REPO/src/comp/make-ghc-pkg-info.sh" $NAMES \
    > "$DIST/LICENSES/LICENSE.ghc_pkgs" \
    || die "make-ghc-pkg-info.sh: $(tail -1 "$DIST/LICENSES/LICENSE.ghc_pkgs")"
unset GHC_PACKAGE_PATH

cat > "$DIST/LICENSES/COPYING" <<EOT
The bluehs distribution redistributes the following components:

  * The bsc compiler libraries (hs/store) and tool scripts (scripts/),
    built from the BSC sources
      - See LICENSES/COPYING.bsc, and for code adapted from other
        projects LICENSES/LICENSE.hbc, LICENSES/LICENSE.parsec and
        LICENSES/LICENSE.yices-painless
  * The Glasgow Haskell Compiler runtime and tools (ghc, runghc,
    ghc-pkg, boot libraries, RTS)
      - See LICENSES/LICENSE.ghc$LIBFFI
  * Haskell library packages (GHC boot libraries, packages from
    Hackage, and the bsc compiler libraries themselves), enumerated with
    their licenses and copyrights in:
      - See LICENSES/LICENSE.ghc_pkgs
  * The STP SAT solver shared library (SAT/libstp.*)
      - See LICENSES/LICENSE.stp and LICENSES/LICENSE.stp_components
  * The Yices SMT solver shared library (SAT/libyices.*)
      - See LICENSES/LICENSE.yices

Not included, required from the host system at runtime: the C and C++
runtimes, libgmp (on Linux; the macOS libraries carry their own), libtinfo
(ncurses), and, for scripts that use CPP, the C compiler the shipped GHC's
settings name.
EOT

# ----------------------------------------------------------------------
# 8. Smoke test a copy in another directory with the build tree out of
#    reach, under an empty environment and, for the scripts that do not use
#    CPP, with no C compiler on PATH; and with nothing but the probe
#    interpreted, so the compiler's modules come from the library.  Only a
#    tree that passes replaces the installed one.

msg "smoke testing"
# beside the work directory: a copy of the tree is too large for a tmpfs /tmp
SMOKE=$(mktemp -d "$(dirname "$WORK")/bluehs-smoke.XXXXXX")
# left by a run killed while its build tree was hidden
rm -rf "$WORK.hidden"
trap 'rm -rf "$SMOKE"; [ ! -d "$WORK.hidden" ] || mv "$WORK.hidden" "$WORK"' EXIT
cp -a "$DIST" "$SMOKE/bluehs"
cat > "$SMOKE/probe.hs" <<'EOT'
import Control.Exception (SomeException, try)
import Control.Monad (unless)
-- a dependency of a dependency (mtl's), exposed as in a checkout
import Control.Monad.Trans.Class ()
import qualified STP
import System.Exit (die)
import Version (bscVersionStr)
import qualified Yices
main :: IO ()
main = do
    -- either solver may be the stub (INSTALL.md); bsc needs one that works
    yices <- either (const False) (const True)
        <$> (try Yices.checkVersion :: IO (Either SomeException String))
    stp <- STP.checkVersion
    unless (yices || stp) (die "neither solver library works")
    putStrLn (bscVersionStr True)
EOT
mv "$WORK" "$WORK.hidden"
# only what the launcher and the GHC wrappers use
mkdir "$SMOKE/bin"
for t in sh readlink dirname basename; do ln -s "$(command -v $t)" "$SMOKE/bin/$t"; done
run() { env -i PATH="$1" HOME=/nonexistent "$SMOKE/bluehs/bin/bluehs" "${@:2}"; }
# dumpbo uses CPP, which needs the C compiler GHC's settings name, found
# where the build found it
CC=$("$GHC_BIN" --info | sed -n 's/.*("C compiler command","\([^"]*\)").*/\1/p')
CC_DIR=$(dirname "$(command -v "${CC:-cc}" || echo /usr/bin/cc)")
run "$CC_DIR:/usr/bin:/bin" dumpbo "$PREFIX/lib/Libraries/Prelude.bo" > "$SMOKE/dumpbo.out"
head -1 "$SMOKE/dumpbo.out" | grep -q "Internal Symbols" \
    || die "smoke test: dumpbo output unexpected"
LIBRARY=$(run "$SMOKE/bin" "$SMOKE/probe.hs")
COMPILER=$("$PREFIX/bin/bsc" -v | head -1)
[ "$LIBRARY" = "$COMPILER" ] \
    || die "the library and $PREFIX/bin/bsc differ: '$LIBRARY' vs '$COMPILER'"
# At -v1 GHC counts the modules it interprets, so a compiler module reached
# as a source through the launcher's search path or the environment would be
# a second one; run from the smoke directory, so the working directory holds
# nothing but the probe
( cd "$SMOKE" && run "$SMOKE/bin" -v1 probe.hs > "$SMOKE/probe-v1.out" 2>&1 ) || true
grep -q '^Ok, one module loaded\.$' "$SMOKE/probe-v1.out" \
    || { cat "$SMOKE/probe-v1.out" >&2; die "smoke test: more than the probe was interpreted"; }
mv "$WORK.hidden" "$WORK"

msg "installing into $DEST"
# the previous tree stays until the new one is in place
rm -rf "$DEST.old"
[ ! -d "$DEST" ] || mv "$DEST" "$DEST.old"
mv "$DIST" "$DEST"
rm -rf "$DEST.old"
msg "done: $DEST ($(du -sh "$DEST" | cut -f1)), $LIBRARY"
