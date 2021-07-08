#!/bin/sh

usage()
{
    echo "Usage: $0 <option>"
    echo ""
    echo "Display canonical platform information"
    echo "Valid options are:"
    echo "   ostype   "
    echo "   machtype "
    echo "   tclsh "
    echo "   tclinc "
    echo "   tcllibs "
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

# If we see a BSD-style amd64 instead of x86_64, rewrite it to the more generic
# version.
if [ ${MACHTYPE} = "amd64" ] ; then
    MACHTYPE=x86_64
fi

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
## Find the TCL shell command
TCL_SUFFIX=
if [ ${OSTYPE} = "Darwin" ] ; then
    # Have Makefile avoid Homebrew's install of tcl on Mac
    TCLSH=/usr/bin/tclsh
elif [ ${OSTYPE} = Freebsd ] ; then
    # The FreeBSD tcl packages are versioned.  Find the right one.
    if [ -n "`which tclsh8.7`" ] ; then
        TCL_SUFFIX=8.7
        TCL_ALT_SUFFIX=87
    elif [ -n "`which tclsh8.6`" ] ; then
        TCL_SUFFIX=8.6
        TCL_ALT_SUFFIX=86
    elif [ -n "`which tclsh8.5`" ] ; then
        TCL_SUFFIX=8.5
        TCL_ALT_SUFFIX=85
    fi
    TCLSH=`which tclsh${TCL_SUFFIX}`
else
    TCLSH=`which tclsh`
fi

if [ "$1" = "tclsh" ] ; then
    echo ${TCLSH}
    exit 0
fi

PKG_CONFIG=`which pkg-config`
if [ -z "${PKG_CONFIG}" ] ; then
	PKG_CONFIG='false'
fi


if [ "$1" = "tclinc" ] ; then
    # Try pkg-config
    TCL_INC_FLAGS=`${PKG_CONFIG} --silence-errors --cflags-only-I tcl${TCL_SUFFIX}`
    # If pkg-config didn't work with the first prefix, try the alternative version.
    # For example, on FreeBSD, the tcl87 package installs tclsh8.7, but tcl87.pc
    if [ -z "${TCL_INC_FLAGS}" ] ; then
        TCL_INC_FLAGS=`${PKG_CONFIG} --silence-errors --cflags-only-I tcl${TCL_ALT_SUFFIX}`
    fi
    # If pkg-config doesn't work, try some well-known locations
    if [ -z "${TCL_INC_FLAGS}" ] ; then
        if [ -f "/usr/local/include/tcl${TCL_SUFFIX}/tcl.h" ] ; then
            TCL_INC_FLAGS="-I/usr/local/include/tcl${TCL_SUFFIX}"
        elif [ -f "/usr/include/tcl${TCL_SUFFIX}/tcl.h" ] ; then
            TCL_INC_FLAGS="-I/usr/include/tcl${TCL_SUFFIX}"
        else
            exit 1
        fi
    fi
    echo ${TCL_INC_FLAGS}
    exit 0
fi

if [ "${OSTYPE}" = "Darwin" ] ; then
    LIB_SUFFIX=dylib
else
    LIB_SUFFIX=so
fi

if [ "$1" = "tcllibs" ] ; then
    # Try pkg-config
    TCL_LIB_FLAGS=`${PKG_CONFIG} --silence-errors --libs tcl${TCL_SUFFIX}`
    # If pkg-config didn't work with the first prefix, try the alternative version.
    # For example, on FreeBSD, the tcl87 package installs tclsh8.7, but tcl87.pc
    if [ -z "${TCL_LIB_FLAGS}" ] ; then
        TCL_LIB_FLAGS=`${PKG_CONFIG} --silence-errors --libs tcl${TCL_ALT_SUFFIX}`
    fi

    if [ -n "${TCL_LIB_FLAGS}" ] ; then
        echo ${TCL_LIB_FLAGS}
        exit 0
    fi

    # If pkg-config doesn't work, try some well-known locations
    TCL_VER=`echo 'catch { puts [info tclversion]; exit 0}; exit 1' | ${TCLSH}`
    for L in /usr/lib /usr/local/lib ; do
        for V in ${TCL_VER} ${TCL_SUFFIX} ${TCL_ALT_SUFFIX} ; do
            if [ -f "${L}/libtcl${V}.${LIB_SUFFIX}" ] ; then
                echo -L${L} -ltcl${V}
                exit 0
            fi
        done
    done
    # If we're Linux, look for multiarch things
    if [ "${OSTYPE}" = "Linux" ] ; then
        for V in ${TCL_VER} ${TCL_SUFFIX} ${TCL_ALT_SUFFIX} ; do
            if [ -f "/usr/lib/${MACHTYPE}-linux-gnu/libtcl${V}.${LIB_SUFFIX}" ] ; then
                echo -ltcl${V}
                exit 0
            fi
        done
    fi
    exit 1
fi


usage
exit 1
