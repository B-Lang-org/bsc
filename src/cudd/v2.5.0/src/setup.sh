#! /bin/sh
CREATE="ln -s"
FORCECREATE="ln -fs"

if (test -d include)
  then
    :
  else
    mkdir include
    ( cd include
    $CREATE ../cudd/cudd.h .
    $CREATE ../cudd/cuddInt.h .
    $CREATE ../epd/epd.h .
    $CREATE ../dddmp/dddmp.h .
    $CREATE ../mtr/mtr.h .
    $CREATE ../obj/cuddObj.hh .
    $CREATE ../st/st.h .
    $CREATE ../util/util.h .
    $CREATE ../mnemosyne/mnemosyne.h .
    )
fi

## make a lib directory and link the expected .a files
## so all cudd libraries are in one common place

if (test -d lib )
    then
      :
    else
      mkdir lib
      ( cd lib

      $CREATE ../cudd/libcudd.a  .
      $CREATE ../dddmp/libdddmp.a libdcudd_dddmp.a
      $CREATE ../epd/libepd.a libcudd_epd.a
      $CREATE ../mtr/libmtr.a libcudd_mtr.a
      $CREATE ../st/libst.a libcudd_st.a
      $CREATE ../util/libutil.a libcudd_util.a
      )

fi

CUDDDIR=../..
cwd="${PWD##*/cudd/}"

(
    cd ${CUDDDIR}

    if (! test -e include ) ; then
	mkdir include
    fi
    cd include
    for f in ../${cwd}/include/* ; do
	$FORCECREATE $f .
    done
    cd ..

    if (! test -e lib ) ; then
	mkdir lib
    fi
    cd lib
    for f in ../${cwd}/lib/* ; do
	$FORCECREATE $f .
    done
    cd ..
)

