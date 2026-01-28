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
ainit arr_ver
ainit arr_lic
ainit arr_copyr
ainit arr_deps

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

    PKG_NAME=`echo "${PKG_NAME}" | tr .- _`

    aget arr_id "${PKG_NAME}" i_id
    if [ -z ${i_id+x} ] ; then
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

	aset arr_id ${PKG_NAME} "${PKG_ID}"
	aset arr_ver ${PKG_NAME} "${PKG_VER}"
	aset arr_lic ${PKG_NAME} "${PKG_LIC}"
	aset arr_copyr ${PKG_NAME} "${PKG_COPYR}"
	aset arr_deps ${PKG_NAME} "${PKG_DEPS}"

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
keys=$(akeys arr_id)
sorted_keys=`echo ${keys} | tr ' ' '\012' | sort | tr '\012' ' '`
for i in ${sorted_keys}
do
    aget arr_id $i i_id
    aget arr_ver $i i_ver
    aget arr_lic $i i_lic
    aget arr_copyr $i i_copyr

    # Because the package name was mangled to make the assoc array key
    # re-construct it from the ID

    if [[ ${i_id} =~ ${STRIP_HASH_REGEX} ]] ; then
	pkg=${BASH_REMATCH[1]}
    else
	pkg=${i_id}
    fi

    # And then strip the version number

    STRIP_VER_REGEX="^([-[:lower:]]+)-${i_ver}"
    if [[ $pkg =~ ${STRIP_VER_REGEX} ]] ; then
	pkg=${BASH_REMATCH[1]}
    fi

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
