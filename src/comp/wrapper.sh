#! /usr/bin/env bash

# Find the absolute name and location of this script
#
ABSNAME="$(cd "$(dirname "$0")"; pwd -P)/$(basename "$0")"
SCRIPTNAME=`basename "${ABSNAME}"`
BINDIR=`dirname "${ABSNAME}"`

# Set BLUESPECDIR based on the location
BLUESPECDIR="$(cd ${BINDIR}/../lib; pwd -P)"
export BLUESPECDIR

# Determine the actual executable to run
BLUESPECEXEC=${BINDIR}/core/${SCRIPTNAME}

if [ -z "$BLUESPECEXEC" ] || [ ! -x $BLUESPECEXEC ] ; then
    echo "Error Bluespec executable not found: ${BLUESPECEXEC}"
    exit 1;
fi

exec $BLUESPECEXEC "$@"
