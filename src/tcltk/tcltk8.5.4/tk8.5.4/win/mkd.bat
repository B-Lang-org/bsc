@echo off
rem RCS: @(#) $Id: mkd.bat,v 1.5 2001/11/13 02:46:23 davygrvy Exp $

if exist %1\nul goto end

md %1
if errorlevel 1 goto end

echo Created directory %1

:end



