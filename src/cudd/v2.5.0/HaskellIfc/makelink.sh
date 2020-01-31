#!/bin/sh
CREATE="ln -s "
FORCECREATE="ln -sf "

CUDDDIR=../..
cwd="${PWD##*/cudd/}"

## Link the haskell interface to the cudd-version directory
(
cd ${CUDDDIR}
if (! test -d include) 
 then
   mkdir include
fi
cd include
${FORCECREATE} ../${cwd}/cudd_interface.h
)

## Link the library file to the cudd interface.
(
cd ${CUDDDIR}

if ( ! test -d lib )
    then
        mkdir lib 
fi
cd lib
$FORCECREATE ../${cwd}/libhcudd.a libhcudd.a
)

# Now link the source code out to include_hs directory
(
cd ${CUDDDIR}
if ( ! test -d include_hs )
    then
        mkdir include_hs
fi
cd include_hs
$FORCECREATE ../${cwd}/CuddBdd.hs
)

