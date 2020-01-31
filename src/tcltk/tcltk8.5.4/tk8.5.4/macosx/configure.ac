#! /bin/bash -norc
dnl	This file is an input file used by the GNU "autoconf" program to
dnl	generate the file "configure", which is run during Tk installation
dnl	to configure the system for the local environment.
#
# RCS: @(#) $Id: configure.ac,v 1.1 2005/11/27 02:36:14 das Exp $

dnl	Ensure that the config (auto)headers support is used, then just 
dnl	include the configure sources from ../unix:

m4_include(../unix/aclocal.m4)
m4_define(SC_USE_CONFIG_HEADERS)
m4_include(../unix/configure.in)
