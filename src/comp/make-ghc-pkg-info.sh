#! /usr/bin/env bash
set -euo pipefail

PACKAGES=$@

declare -A arr_id=()
declare -A arr_ver=()
declare -A arr_lic=()
declare -A arr_copyr=()
declare -A arr_deps=()

# Horizontal delimiter between packages in the output
#
DELIM='-------------------------'

# Regex for removing the hash from names like
#   syb-0.7.2.4-FBa2dfZrzzu7owkvhCx23j
#
STRIP_HASH_REGEX='^([-[:lower:]]+[[:digit:]]+.[[:digit:]][.[:digit:]]*)-[[:alnum:]][[:alnum:]][[:alnum:]][[:alnum:]]+$'

# Function to add a package to the database and follow its dependencies
#
add_pkg() {
    local PKG_ID
    local PKG_NAME
    local PKG_VER
    local PKG_LIC
    local PKG_COPYR
    local PKG_DEPS

    #echo "Looking up $1"

    PKG_ID=`ghc-pkg field $1 id --simple-output`

    if [[ ${PKG_ID} =~ ${STRIP_HASH_REGEX} ]] ; then
	#echo "stripping ${PKG_ID} => ${BASH_REMATCH[1]}"
	PKG_NAME=${BASH_REMATCH[1]}
    else
	PKG_NAME=${PKG_ID}
    fi

    if [[ ! -v arr_id[${PKG_NAME}] ]] ; then
	PKG_VER=`ghc-pkg field $1 version --simple-output`
	PKG_LIC=`ghc-pkg field $1 license --simple-output`
	PKG_COPYR=`ghc-pkg field $1 copyright --simple-output`
	PKG_DEPS=`ghc-pkg field $1 depends --simple-output`

	if [ "${PKG_LIC}" != "BSD-3-Clause" ] ; then
	    if [ "${PKG_LIC}" != "BSD-2-Clause" ] ; then
		echo "Unexpected license for ${PKG_ID}: ${PKG_LIC}"
		exit 1
	    fi
	fi

	arr_id[${PKG_NAME}]="${PKG_ID}"
	arr_ver[${PKG_NAME}]="${PKG_VER}"
	arr_lic[${PKG_NAME}]="${PKG_LIC}"
	arr_copyr[${PKG_NAME}]="${PKG_COPYR}"
	arr_deps[${PKG_NAME}]="${PKG_DEPS}"

	for dep in ${PKG_DEPS}
	do
	    #echo "Following dep: $dep"
	    if [[ ${dep} =~ ${STRIP_HASH_REGEX} ]] ; then
		#echo "stripping ${dep} => ${BASH_REMATCH[1]}"
		dep=${BASH_REMATCH[1]}
	    fi
	    add_pkg "${dep}"
	done
    fi
}

# Add the packages from the command line (and their dependencies)
for i in ${PACKAGES}
do
    add_pkg "$i"
done

# Generate the output, starting with a delimiter
echo $DELIM

# For each package in the database
sorted_keys=`echo ${!arr_id[@]} | tr ' ' '\012' | sort | tr '\012' ' '`
for i in ${sorted_keys}
do
    STRIP_VER_REGEX="^([-[:lower:]]+)-${arr_ver[$i]}"
    if [[ $i =~ ${STRIP_VER_REGEX} ]] ; then
	pkg=${BASH_REMATCH[1]}
    else
	pkg=$i
    fi

    echo
    echo "package: $pkg"
    #echo "id: ${arr_id[$i]}"
    echo "version: ${arr_ver[$i]}"
    echo "license: ${arr_lic[$i]}"
    if [[ -n "${arr_copyr[$i]}" ]]; then
	echo "copyright: ${arr_copyr[$i]}"
    fi
    echo
    echo $DELIM
done

# Done
exit 0
