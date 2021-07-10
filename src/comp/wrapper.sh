#! /usr/bin/env bash

# Find the absolute name and location of this script
#
ABSNAME="$(cd "${0%/*}"; echo $PWD)/${0##*/}"
SCRIPTNAME="${ABSNAME##*/}"
BINDIR="${ABSNAME%/*}"

# Set BLUESPECDIR based on the location
BLUESPECDIR="$(cd ${BINDIR}/../lib; echo $PWD)"
export BLUESPECDIR

# Determine the actual executable to run
BLUESPECEXEC=${BINDIR}/core/${SCRIPTNAME}

if [ ! -x "$BLUESPECEXEC" ] ; then
    echo "Error Bluespec executable not found: ${BLUESPECEXEC}"
    exit 1;
fi

exec $BLUESPECEXEC "$@"
