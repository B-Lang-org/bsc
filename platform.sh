#!/bin/sh

set -u

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

## Account for values like "linux-gnu" by removing extra fields
OSTYPE=$(echo ${OSTYPE:=$(uname -s)} | cut -d'-' -f1)
## Account for values like "Darwin10.0" by removing the version number
OSTYPE=$(echo ${OSTYPE} | grep -Eo "^[A-Za-z]+")
## Account for lowercase values like "linux" when we want "Linux"
OSTYPE=$(echo ${OSTYPE} | cut -c1 | tr a-z A-Z)$(echo $OSTYPE | cut -c2- | tr A-Z a-z)

if [ "$1" = "ostype" ] ; then
    echo ${OSTYPE}
    exit 0
fi

## =========================
## MACHTYPE

## Account for values like "x86_64-pc-linux-gnu" when all we want is
## "x86_64", "i386", etc
MACHTYPE=$(echo ${MACHTYPE:=$(uname -m)} | cut -d'-' -f1)

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
	# macOS 12 (or XCode 14) requires an additional flag
	SWVER=`sw_vers -productVersion`
	SWVERMAJOR=$(echo ${SWVER} | cut -d'.' -f1)
	if [ "$SWVERMAJOR" -ge 12 ] ; then
	    echo "-dynamiclib -Wl,-undefined,dynamic_lookup -Wl,-no_fixup_chains"
	else
	    echo "-dynamiclib -Wl,-undefined,dynamic_lookup"
	fi
    else
	echo "-shared"
    fi
    exit 0
fi

## =========================
## Find the TCL shell command

if [ ${OSTYPE} = "Darwin" ] ; then
    # Have Makefile avoid Homebrew's install of tcl on Mac
    TCLSH=/usr/bin/tclsh
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

TCL_SUFFIX=$(echo 'catch { puts [info tclversion]; exit 0}; exit 1' | ${TCLSH})
TCL_ALT_SUFFIX=$(echo ${TCL_SUFFIX} | sed 's/\.//')

if [ "$1" = "tclinc" ] ; then
    # Avoid Homebrew's install of Tcl on Mac
    if [ ${OSTYPE} = "Darwin" ] ; then
	# no flags needed
	exit 0
    fi

    # Try pkg-config
    TCL_INC_FLAGS=$(${PKG_CONFIG} --silence-errors --cflags-only-I tcl${TCL_SUFFIX})
    # If pkg-config didn't work with the first prefix, try the alternative version.
    # For example, on FreeBSD, the tcl87 package installs tclsh8.7, but tcl87.pc
    if [ $? -ne 0 ] ; then
        TCL_INC_FLAGS=$(${PKG_CONFIG} --silence-errors --cflags-only-I tcl${TCL_ALT_SUFFIX})
    fi
    # The tcl package may also not have a suffix at all, e.g. on Arch Linux.
    if [ $? -ne 0 ] ; then
        TCL_INC_FLAGS=$(${PKG_CONFIG} --silence-errors --cflags-only-I tcl)
    fi
    # If pkg-config doesn't work, try some well-known locations
    if [ $? -ne 0 ] ; then
        if [ -f "/usr/local/include/tcl${TCL_SUFFIX}/tcl.h" ] ; then
	    TCL_INC_FLAGS="-I/usr/local/include/tcl${TCL_SUFFIX}"
        elif [ -f "/usr/include/tcl${TCL_SUFFIX}/tcl.h" ] ; then
	    TCL_INC_FLAGS="-I/usr/include/tcl${TCL_SUFFIX}"
	elif [ -f "/usr/include/tcl.h" ] ; then
	    TCL_INC_FLAGS=""
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
    # Avoid Homebrew's install of Tcl on Mac
    if [ ${OSTYPE} = "Darwin" ] ; then
	echo -ltcl${TCL_SUFFIX}
	exit 0
    fi

    # Try pkg-config
    TCL_LIB_FLAGS=`${PKG_CONFIG} --silence-errors --libs tcl${TCL_SUFFIX}`
    # If pkg-config didn't work with the first prefix, try the alternative version.
    # For example, on FreeBSD, the tcl87 package installs tclsh8.7, but tcl87.pc
    if [ $? -ne 0 ] ; then
        TCL_LIB_FLAGS=`${PKG_CONFIG} --silence-errors --libs tcl${TCL_ALT_SUFFIX}`
    fi
    # The tcl package may also not have a suffix at all, e.g. on Arch Linux.
    if [ $? -ne 0 ] ; then
        TCL_LIB_FLAGS=`${PKG_CONFIG} --silence-errors --libs tcl`
    fi

    if [ $? -eq 0 ] ; then
        echo ${TCL_LIB_FLAGS}
        exit 0
    fi

    # If pkg-config doesn't work, try some well-known locations
    for L in /usr/lib /usr/lib64 /usr/local/lib ; do
        for V in ${TCL_SUFFIX} ${TCL_ALT_SUFFIX} ; do
            if [ -f "${L}/libtcl${V}.${LIB_SUFFIX}" ] ; then
                echo -L${L} -ltcl${V}
                exit 0
            fi
        done
    done
    # If we're Linux, look for multiarch things
    if [ "${OSTYPE}" = "Linux" ] ; then
        for V in ${TCL_SUFFIX} ${TCL_ALT_SUFFIX} ; do
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
