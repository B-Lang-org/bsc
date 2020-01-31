#!/bin/sh

usage()
{
    echo "Usage: $0 <option>"
    echo ""
    echo "Display canonical platform information"
    echo "Valid options are:"
    echo "   ostype   "
    echo "   machtype "
    echo "   c++_shared_flags"
}

if [ $# -ne 1 ] ; then
    usage
    exit 1;
fi

## =========================
## OSTYPE

if [ -z "${OSTYPE}" ] ; then
    OSTYPE=`uname -s`
fi
## Account for values like "linux-gnu" by removing extra fields
OSTYPE=$(echo ${OSTYPE} | cut -d'-' -f1)
## Account for values like "Darwin10.0" by removing the version number
OSTYPE=$(echo ${OSTYPE} | egrep -o "^[A-Za-z]+")
## Account for lowercase values like "linux" when we want "Linux"
OSTYPE=$(echo ${OSTYPE} | cut -c1 | tr a-z A-Z)$(echo $OSTYPE | cut -c2- | tr A-Z a-z)

if [ "$1" = "ostype" ] ; then
    echo ${OSTYPE}
    exit 0
fi

## =========================
## MACHTYPE

if [ -z "${MACHTYPE}" ] ; then
    MACHTYPE=`uname -m`
fi
## Account for values like "x86_64-pc-linux-gnu" when all we want is
## "x86_64", "i386", etc
MACHTYPE=$(echo ${MACHTYPE} | cut -d'-' -f1)

if [ "$1" = "machtype" ] ; then
    echo ${MACHTYPE}
    exit 0
fi

## =========================
## C++ SHARED FLAGS

if [ "$1" = "c++_shared_flags" ] ; then
    if [ "${OSTYPE}" = "Darwin" ]
    then
	echo "-dynamiclib -Wl,-undefined,dynamic_lookup"
    else
	echo "-shared"
    fi
    exit 0
fi

## =========================

usage
exit 1
