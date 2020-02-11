#!/bin/sh

PARAMS=""

## Get the compiler and version string
COMPILER=`$CC --version | awk 'NR==1 {print $1}'`
VERSION=`$CC --version | head -1 | egrep -o "[0-9]+\.[0-9]+" | head -1`
## Extract the major and minor numbers
MAJOR=`echo $VERSION | cut -d. -f1`
MINOR=`echo $VERSION | cut -d. -f2`

if [ "${COMPILER}" = "gcc" ]
then
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
else
    PARAMS=$@
fi

echo "Using flags: " $PARAMS

exec $CC $PARAMS
