#! /usr/bin/env bash
set -euo pipefail

PACKAGES=$@

# ===========================================================================

# Implement associative arrays, in case the shell is not bash 4+

## ainit STEM
## Declare an empty associative array named STEM.
ainit () {
  eval "__aa__${1}=' '"
}

## akeys STEM
## List the keys in the associatve array named STEM.
akeys () {
  eval "echo \"\$__aa__${1}\""
}

## aget STEM KEY VAR
## Set VAR to the value of KEY in the associative array named STEM.
## If KEY is not present, unset VAR.
aget () {
  eval "unset $3
        case \$__aa__${1} in
          *\" $2 \"*) $3=\$__aa__${1}__$2;;
        esac"
}

## aset STEM KEY VALUE
## Set KEY to VALUE in the associative array named STEM.
aset () {
  eval "__aa__${1}__${2}=\$3
        case \$__aa__${1} in
          *\" $2 \"*) :;;
          *) __aa__${1}=\"\${__aa__${1}}$2 \";;
        esac"
}

## aunset STEM KEY
## Remove KEY from the associative array named STEM.
aunset () {
  eval "unset __aa__${1}__${2}
        case \$__aa__${1} in
          *\" $2 \"*) __aa__${1}=\"\${__aa__${1}%% $2 *} \${__aa__${1}#* $2 }\";;
        esac"
}

# ===========================================================================

ainit arr_id
ainit arr_name
ainit arr_ver
ainit arr_lic
ainit arr_copyr
ainit arr_deps

# Horizontal delimiter between packages in the output
#
DELIM='-------------------------'

# Function to add a package to the database and follow its dependencies.
# The argument is an installed package id, as listed in 'depends'.  Every
# field is looked up by id rather than by name-version, because the id is
# not always derived from the name: on macOS, cabal-install drops the
# vowels from the package name when it forms a store id (old-locale is
# ld-lcl-1.0.0.7-1ff3ddac), so the name has to come from the 'name' field.
#
add_pkg() {
    local PKG_ID=$1
    local PKG_NAME
    local PKG_KEY
    local PKG_VER
    local PKG_LIC
    local PKG_COPYR
    local PKG_DEPS

    #echo "Looking up $1"

    PKG_NAME=`ghc-pkg field --ipid ${PKG_ID} name --simple-output`
    PKG_KEY=`echo "${PKG_NAME}" | tr .- _`

    aget arr_id "${PKG_KEY}" i_id
    if [ -z ${i_id+x} ] ; then
	PKG_VER=`ghc-pkg field --ipid ${PKG_ID} version --simple-output`
	PKG_LIC=`ghc-pkg field --ipid ${PKG_ID} license --simple-output`
	PKG_COPYR=`ghc-pkg field --ipid ${PKG_ID} copyright --simple-output`
	PKG_DEPS=`ghc-pkg field --ipid ${PKG_ID} depends --simple-output`

	if [ "${PKG_LIC}" != "BSD-3-Clause" ] ; then
	    if [ "${PKG_LIC}" != "BSD-2-Clause" ] ; then
		echo "Unexpected license for ${PKG_ID}: ${PKG_LIC}"
		exit 1
	    fi
	fi

	aset arr_id ${PKG_KEY} "${PKG_ID}"
	aset arr_name ${PKG_KEY} "${PKG_NAME}"
	aset arr_ver ${PKG_KEY} "${PKG_VER}"
	aset arr_lic ${PKG_KEY} "${PKG_LIC}"
	aset arr_copyr ${PKG_KEY} "${PKG_COPYR}"
	aset arr_deps ${PKG_KEY} "${PKG_DEPS}"

	for dep in ${PKG_DEPS}
	do
	    #echo "Following dep: $dep"
	    add_pkg "${dep}"
	done
    fi
}

# Add the packages from the command line (and their dependencies).
# These are package names, so resolve each to its id first.
for i in ${PACKAGES}
do
    for id in `ghc-pkg field $i id --simple-output`
    do
	add_pkg "$id"
    done
done

# Generate the output, starting with a delimiter
echo $DELIM

# For each package in the database
keys=$(akeys arr_id)
sorted_keys=`echo ${keys} | tr ' ' '\012' | sort | tr '\012' ' '`
for i in ${sorted_keys}
do
    aget arr_name $i pkg
    aget arr_ver $i i_ver
    aget arr_lic $i i_lic
    aget arr_copyr $i i_copyr

    echo
    echo "package: $pkg"
    #echo "id: ${i_id}"
    echo "version: ${i_ver}"
    echo "license: ${i_lic}"
    if [[ -n "${i_copyr}" ]]; then
	echo "copyright: ${i_copyr}"
    fi
    echo
    echo $DELIM
done

# Done
exit 0
