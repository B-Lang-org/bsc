#! /usr/bin/env bash

TOP=../..
PLATFORM_SH=${TOP}/platform.sh

OSTYPE=`${PLATFORM_SH} ostype`

# There is room to add the MACHTYPE if necessary
echo "module BuildSystem (BinFmtType(..), binFmtToString, getBinFmtType) where" > BuildSystem.hs.new;
echo "" >> BuildSystem.hs.new;

echo "data BinFmtType = ELF | MachO" >> BuildSystem.hs.new;
echo "" >> BuildSystem.hs.new;

echo "binFmtToString :: BinFmtType -> String" >> BuildSystem.hs.new;
echo "binFmtToString ELF  = \"ELF\"" >> BuildSystem.hs.new;
echo "binFmtToString MachO = \"Mach-O\"" >> BuildSystem.hs.new;
echo "" >> BuildSystem.hs.new;

echo "getBinFmtType :: BinFmtType" >> BuildSystem.hs.new;
if [ ${OSTYPE} = "Darwin" ] ; then
	echo "getBinFmtType = MachO" >> BuildSystem.hs.new;
else
	echo "getBinFmtType = ELF" >> BuildSystem.hs.new;
fi
echo "" >> BuildSystem.hs.new;

if test -e BuildSystem.hs; then
  diff -q BuildSystem.hs.new BuildSystem.hs > /dev/null
  if [ $? -eq 0 ]; then
    echo "BuildSystem.hs up-to-date";
    rm BuildSystem.hs.new;
  else
    mv BuildSystem.hs.new BuildSystem.hs;
  fi;
else
  mv BuildSystem.hs.new BuildSystem.hs;
fi;

