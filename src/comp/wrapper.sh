#! /usr/bin/env bash

# Find the absolute name and location of this script
#
ABSNAME="$(cd "${0%/*}"; echo $PWD)/${0##*/}"
SCRIPTNAME="${ABSNAME##*/}"
BINDIR="${ABSNAME%/*}"

# Set BLUESPECDIR based on the location
BLUESPECDIR="$(cd ${BINDIR}/../lib; echo $PWD)"
export BLUESPECDIR

# Add the dynamically-linked SAT libraries to the load path
if [ -n "$BLUESPEC_LD_LIBRARY_PATH" ] ; then
    LD_LIBRARY_PATH=${BLUESPEC_LD_LIBRARY_PATH}:${LD_LIBRARY_PATH}
    DYLD_LIBRARY_PATH=${BLUESPEC_LD_LIBRARY_PATH}:${DYLD_LIBRARY_PATH}
fi
LD_LIBRARY_PATH=${LD_LIBRARY_PATH}:${BLUESPECDIR}/SAT
DYLD_LIBRARY_PATH=${DYLD_LIBRARY_PATH}:${BLUESPECDIR}/SAT
export LD_LIBRARY_PATH
export DYLD_LIBRARY_PATH

# Determine the actual executable to run
BLUESPECEXEC=${BINDIR}/core/${SCRIPTNAME}

if [ ! -x "$BLUESPECEXEC" ] ; then
    echo "Error Bluespec executable not found: ${BLUESPECEXEC}"
    exit 1;
fi

exec $BLUESPECEXEC "$@"
