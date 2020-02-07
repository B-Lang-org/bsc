#! /usr/bin/env bash

TOP=../..
PLATFORM_SH=${TOP}/platform.sh

OSTYPE=`${PLATFORM_SH} ostype`

# There is room to add the MACHTYPE if necessary
echo "module BuildSystem (OSType(..), osToString, getOSType) where" > BuildSystem.hs.new;
echo "" >> BuildSystem.hs.new;

echo "data OSType = Linux | Darwin" >> BuildSystem.hs.new;
echo "" >> BuildSystem.hs.new;

echo "osToString :: OSType -> String" >> BuildSystem.hs.new;
echo "osToString Linux  = \"Linux\"" >> BuildSystem.hs.new;
echo "osToString Darwin = \"Darwin\"" >> BuildSystem.hs.new;
echo "" >> BuildSystem.hs.new;

echo "getOSType :: OSType" >> BuildSystem.hs.new;
echo "getOSType = ${OSTYPE}" >> BuildSystem.hs.new;
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

