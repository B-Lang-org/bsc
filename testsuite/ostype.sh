#!/bin/sh

if [ -z "${OSTYPE}" ] ; then
    OSTYPE=`uname -s`
fi
## Account for values like "linux-gnu" by removing extra fields
OSTYPE=$(echo ${OSTYPE} | cut -d'-' -f1)
## Account for values like "Darwin10.0" by removing the version number
OSTYPE=$(echo ${OSTYPE} | egrep -o "^[A-Za-z]+")
## Account for lowercase values like "linux" when we want "Linux"
OSTYPE=$(echo ${OSTYPE} | cut -c1 | tr a-z A-Z)$(echo $OSTYPE | cut -c2- | tr A-Z a-z)

echo ${OSTYPE}
exit 0
