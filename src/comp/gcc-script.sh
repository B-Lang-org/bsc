#!/bin/sh

PARAMS=""

## Get the gcc version string
VERSION=`$CC --version | head -1 | egrep -o "[0-9]+\.[0-9]+" | head -1`

## Extract the major and minor numbers
MAJOR=`echo $VERSION | cut -d. -f1`
MINOR=`echo $VERSION | cut -d. -f2`

if [ ${MAJOR} -lt 3 -o ${MAJOR} -lt 4 -a ${MINOR} -lt 4 ]
then
    echo "dropping -fno-unit-at-a-time and -fwrapv if present"
    while [ $# -gt 0 ]
    do
	if [ "${1}" != "-fno-unit-at-a-time" -a "${1}" != "-fwrapv" ] 
	then
	    PARAMS=${PARAMS}" ${1}" 
	fi
	shift
    done
else
    PARAMS=$@
fi

echo "Using flags: " $PARAMS

$CC $PARAMS


