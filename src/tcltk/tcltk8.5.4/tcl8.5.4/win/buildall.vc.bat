@echo off
::  This is an example batchfile for building everything. Please
::  edit this (or make your own) for your needs and wants using
::  the instructions for calling makefile.vc found in makefile.vc
::
::  RCS: @(#) $Id: buildall.vc.bat,v 1.9 2005/10/14 12:31:39 patthoyts Exp $

set SYMBOLS=

:OPTIONS
if "%1" == "/?" goto help
if /i "%1" == "/help" goto help
if %1.==symbols. goto SYMBOLS
if %1.==debug. goto SYMBOLS
goto OPTIONS_DONE

:SYMBOLS
   set SYMBOLS=symbols
   shift
   goto OPTIONS

:OPTIONS_DONE

:: reset errorlevel
cd > nul

:: We need to run the development environment batch script that comes
:: with developer studio (v4,5,6,7,etc...)  All have it.  These paths
:: might not be correct.  You may need to edit these.
::
if not defined MSDevDir (
    call "C:\Program Files\Microsoft Developer Studio\vc98\bin\vcvars32.bat"
    ::call "C:\Program Files\Microsoft Developer Studio\vc\bin\vcvars32.bat"
    ::call c:\dev\devstudio60\vc98\bin\vcvars32.bat
    if errorlevel 1 goto no_vcvars
)


echo.
echo Sit back and have a cup of coffee while this grinds through ;)
echo You asked for *everything*, remember?
echo.
title Building Tcl, please wait...


:: makefile.vc uses this for its default anyways, but show its use here
:: just to be explicit and convey understanding to the user.  Setting
:: the INSTALLDIR envar prior to running this batchfile affects all builds.
::
if "%INSTALLDIR%" == "" set INSTALLDIR=C:\Program Files\Tcl


:: Build the normal stuff along with the help file.
::
set OPTS=none
if not %SYMBOLS%.==. set OPTS=symbols
nmake -nologo -f makefile.vc release winhelp OPTS=%OPTS% %1
if errorlevel 1 goto error

:: Build the static core, dlls and shell.
::
set OPTS=static
if not %SYMBOLS%.==. set OPTS=symbols,static
nmake -nologo -f makefile.vc release OPTS=%OPTS% %1
if errorlevel 1 goto error

:: Build the special static libraries that use the dynamic runtime.
::
set OPTS=static,msvcrt
if not %SYMBOLS%.==. set OPTS=symbols,static,msvcrt
nmake -nologo -f makefile.vc core dlls OPTS=%OPTS% %1
if errorlevel 1 goto error

:: Build the core and shell for thread support.
::
set OPTS=threads
if not %SYMBOLS%.==. set OPTS=symbols,threads
nmake -nologo -f makefile.vc shell OPTS=%OPTS% %1
if errorlevel 1 goto error

:: Build a static, thread support core library with a shell.
::
set OPTS=static,threads
if not %SYMBOLS%.==. set OPTS=symbols,static,threads
nmake -nologo -f makefile.vc shell OPTS=%OPTS% %1
if errorlevel 1 goto error

:: Build the special static libraries that use the dynamic runtime,
:: but now with thread support.
::
set OPTS=static,msvcrt,threads
if not %SYMBOLS%.==. set OPTS=symbols,static,msvcrt,threads
nmake -nologo -f makefile.vc core dlls OPTS=%OPTS% %1
if errorlevel 1 goto error

set OPTS=
set SYMBOLS=
goto end

:error
echo *** BOOM! ***
goto end

:no_vcvars
echo vcvars32.bat not found.  You'll need to edit this batch script.
goto out

:help
title buildall.vc.bat help message
echo usage:
echo   %0           : builds Tcl for all build types (do this first)
echo   %0 install   : installs all the release builds (do this second)
echo   %0 symbols   : builds Tcl for all debugging build types
echo   %0 symbols install : install all the debug builds.
echo.
goto out

:end
title Building Tcl, please wait... DONE!
echo DONE!
goto out

:out
pause
title Command Prompt

