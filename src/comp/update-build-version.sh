#! /usr/bin/env bash
set -euo pipefail

export TMOUT=1

# Inputs from the environment, exported by src/comp/Makefile (SetupHooks.hs
# and src/bluesim/Makefile call this script with that environment).
NOGIT=${NOGIT:-0}
NOUPDATEBUILDVERSION=${NOUPDATEBUILDVERSION:-0}

# -------------------------
# GIT

# Always inspect this source tree, even when called from another directory or
# with GIT_* environment variables set by a parent Git hook.
root=$(cd "$(dirname "$0")/../.." && pwd)
versionFile="$root/src/comp/BuildVersion.hs"
repoGit () (
    unset $(git rev-parse --local-env-vars)
    git --git-dir="$root/.git" --work-tree="$root" "$@"
)

writeIfChanged () {
    mkdir -p "$(dirname "$1")"
    cat > "$1.tmp"
    if cmp -s "$1.tmp" "$1"; then
        rm -f "$1.tmp"
    else
        mv "$1.tmp" "$1"
    fi
}

# Arguments: 1=output directory, 2=commit hash, 3=describe string
genGITBuildVersion () {
    writeIfChanged "$1/BuildVersion.hs" <<EOF
module BuildVersion(buildVersion, buildVersionNum, buildVersionName) where

import Warmup ()

buildVersion :: String
buildVersion = "$2"

buildVersionNum :: Integer
buildVersionNum = 0x$2

buildVersionName :: String
buildVersionName = "$3"
EOF
}

# Refresh one canonical snapshot per invocation; frozen files are kept verbatim.
updateVersion () {
    if [ "$versionUpdated" = 0 ]; then
        if [ "$NOUPDATEBUILDVERSION" != 1 ] || [ ! -f "$versionFile" ]; then
            getGITVersion
            genGITBuildVersion "$(dirname "$versionFile")" "$GITCOMMIT" "$GITDESCR"
        fi
        versionUpdated=1
    fi
}

writeModule () {
    updateVersion
    writeIfChanged "$1/BuildVersion.hs" < "$versionFile"
}

printVersionName () {
    if [ -f "$versionFile" ]; then
        if ! version=$(grep -E '^buildVersionName = ' "$versionFile"); then
            echo "Failed to find version information in $versionFile" >&2
            exit 1
        fi
        printf '%s\n' "$version" | cut -d'"' -f2
    else
        getGITVersion
        echo "$GITDESCR"
    fi
}

# Set GITCOMMIT and GITDESCR from NOGIT=1, git-archive export-subst
# (.gitattributes), or the Git repository.
getGITVersion () {
    if [ "$NOGIT" = 1 ] ; then
	GITCOMMIT="0000000"
	GITDESCR="no-git"
    else

	# If the source was exported (via 'git archive')
	if [[ '$Format:%%$' == "%" ]]; then
	    GITCOMMIT='$Format:%h$'
	    if [[ '$Format:%D$' =~ tag:\ ([^ ]+) ]]; then
		GITDESCR="${BASH_REMATCH[1]}"
	    else
		GITDESCR="archive-g${GITCOMMIT}"
	    fi
	elif [ ! -e "$root/.git" ]; then

	    # A tree without a repository, such as an unpacked sdist
	    GITCOMMIT="0000000"
	    GITDESCR="no-git"
	else

	    # Get the current commit hash
	    GITCOMMIT=`repoGit show -s --format=%h HEAD`
	    if ! GITDESCR=`repoGit describe --tags`; then
		GITDESCR="untagged-g${GITCOMMIT}"
	    fi

	fi
    fi
}

# -------------------------

[ $# -gt 0 ] || { echo "usage: $0 [--module DIR] [--name]" >&2; exit 2; }
versionUpdated=0
while [ $# -gt 0 ]; do
    case "$1" in
        --module) writeModule "$2"; shift 2 ;;
        --name) printVersionName; shift ;;
        *) echo "usage: $0 [--module DIR] [--name]" >&2; exit 2 ;;
    esac
done

# -------------------------
