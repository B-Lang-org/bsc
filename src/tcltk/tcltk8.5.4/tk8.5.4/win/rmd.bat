@echo off
rem RCS: @(#) $Id: rmd.bat,v 1.5 2001/11/13 02:46:23 davygrvy Exp $

if not exist %1\nul goto end

echo Removing directory %1

if "%OS%" == "Windows_NT" goto winnt

deltree /y %1
if errorlevel 1 goto end
goto success

:winnt
rmdir /s /q %1
if errorlevel 1 goto end

:success
echo Deleted directory %1

:end

