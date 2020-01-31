# tclTomMath.decls --
#
#	This file contains the declarations for the functions in
#	'libtommath' that are contained within the Tcl library.
#	This file is used to generate the 'tclTomMathDecls.h' and
#	'tclTomMathStub.c' files.
#
# If you edit this file, advance the revision number (and the epoch
# if the new stubs are not backward compatible) in tclTomMathDecls.h
#
# Copyright (c) 2005 by Kevin B. Kenny.  All rights reserved.
#
# See the file "license.terms" for information on usage and redistribution
# of this file, and for a DISCLAIMER OF ALL WARRANTIES.
# 
# RCS: @(#) $Id: tclTomMath.decls,v 1.3 2007/12/13 15:23:20 dgp Exp $

library tcl

# Define the unsupported generic interfaces.

interface tclTomMath
# hooks {tclTomMathInt}

# Declare each of the functions in the Tcl tommath interface

declare 0 generic {
    int TclBN_epoch(void)
}
declare 1 generic {
    int TclBN_revision(void)
}

declare 2 generic {
    int TclBN_mp_add(mp_int* a, mp_int* b, mp_int* c)
}
declare 3 generic {
    int TclBN_mp_add_d(mp_int* a, mp_digit b, mp_int* c)
}
declare 4 generic {
    int TclBN_mp_and(mp_int* a, mp_int* b, mp_int* c)
}
declare 5 generic {
    void TclBN_mp_clamp(mp_int* a)
}
declare 6 generic {
    void TclBN_mp_clear(mp_int* a)
}
declare 7 generic {
    void TclBN_mp_clear_multi(mp_int* a, ...)
}
declare 8 generic {
    int TclBN_mp_cmp(mp_int* a, mp_int* b)
}
declare 9 generic {
    int TclBN_mp_cmp_d(mp_int* a, mp_digit b)
}
declare 10 generic {
    int TclBN_mp_cmp_mag(mp_int* a, mp_int* b)
}
declare 11 generic {
    int TclBN_mp_copy(mp_int* a, mp_int* b)
}
declare 12 generic {
    int TclBN_mp_count_bits(mp_int* a)
}
declare 13 generic {
    int TclBN_mp_div(mp_int* a, mp_int* b, mp_int* q, mp_int* r)
}
declare 14 generic {
    int TclBN_mp_div_d(mp_int* a, mp_digit b, mp_int* q, mp_digit* r)
}
declare 15 generic {
    int TclBN_mp_div_2(mp_int* a, mp_int* q)
}
declare 16 generic {
    int TclBN_mp_div_2d(mp_int* a, int b, mp_int* q, mp_int* r)
}
declare 17 generic {
    int TclBN_mp_div_3(mp_int* a, mp_int* q, mp_digit* r)
}
declare 18 generic {
    void TclBN_mp_exch(mp_int* a, mp_int* b)
}
declare 19 generic {
    int TclBN_mp_expt_d(mp_int* a, mp_digit b, mp_int* c)
}
declare 20 generic {
    int TclBN_mp_grow(mp_int* a, int size)
}
declare 21 generic {
    int TclBN_mp_init(mp_int* a)
}
declare 22 generic {
    int TclBN_mp_init_copy(mp_int * a, mp_int* b)
}
declare 23 generic {
    int TclBN_mp_init_multi(mp_int* a, ...)
}
declare 24 generic {
    int TclBN_mp_init_set(mp_int* a, mp_digit b)
}
declare 25 generic {
    int TclBN_mp_init_size(mp_int* a, int size)
}
declare 26 generic {
    int TclBN_mp_lshd(mp_int* a, int shift)
}
declare 27 generic {
    int TclBN_mp_mod(mp_int* a, mp_int* b, mp_int* r)
}
declare 28 generic {
    int TclBN_mp_mod_2d(mp_int* a, int b, mp_int* r)
}
declare 29 generic {
    int TclBN_mp_mul(mp_int* a, mp_int* b, mp_int* p)
}
declare 30 generic {
    int TclBN_mp_mul_d(mp_int* a, mp_digit b, mp_int* p)
}
declare 31 generic {
    int TclBN_mp_mul_2(mp_int* a, mp_int* p)
}
declare 32 generic {
    int TclBN_mp_mul_2d(mp_int* a, int d, mp_int* p)
}
declare 33 generic {
    int TclBN_mp_neg(mp_int* a, mp_int* b)
}
declare 34 generic {
    int TclBN_mp_or(mp_int* a, mp_int* b, mp_int* c)
}
declare 35 generic {
    int TclBN_mp_radix_size(mp_int* a, int radix, int* size)
}
declare 36 generic {
    int TclBN_mp_read_radix(mp_int* a, const char* str, int radix)
}
declare 37 generic {
    void TclBN_mp_rshd(mp_int * a, int shift)
}
declare 38 generic {
    int TclBN_mp_shrink(mp_int* a)
}
declare 39 generic {
    void TclBN_mp_set(mp_int* a, mp_digit b)
}
declare 40 generic {
    int TclBN_mp_sqr(mp_int* a, mp_int* b)
}
declare 41 generic {
    int TclBN_mp_sqrt(mp_int* a, mp_int* b)
}
declare 42 generic {
    int TclBN_mp_sub(mp_int* a, mp_int* b, mp_int* c)
}
declare 43 generic {
    int TclBN_mp_sub_d(mp_int* a, mp_digit b, mp_int* c)
}
declare 44 generic {
    int TclBN_mp_to_unsigned_bin(mp_int* a, unsigned char* b)
}
declare 45 generic {
    int TclBN_mp_to_unsigned_bin_n(mp_int* a, unsigned char* b,
	    unsigned long* outlen)
}
declare 46 generic {
    int TclBN_mp_toradix_n(mp_int* a, char* str, int radix, int maxlen)
}
declare 47 generic {
    int TclBN_mp_unsigned_bin_size(mp_int* a)
}
declare 48 generic {
    int TclBN_mp_xor(mp_int* a, mp_int* b, mp_int* c)
}
declare 49 generic {
    void TclBN_mp_zero(mp_int* a)
}

# internal routines to libtommath - should not be called but must be
# exported to accommodate the "tommath" extension

declare 50 generic {
    void TclBN_reverse(unsigned char* s, int len)
}
declare 51 generic {
    int TclBN_fast_s_mp_mul_digs(mp_int *a, mp_int *b, mp_int *c, int digs)
}
declare 52 generic {
    int TclBN_fast_s_mp_sqr(mp_int* a, mp_int* b)
}
declare 53 generic {
    int TclBN_mp_karatsuba_mul(mp_int* a, mp_int* b, mp_int* c)
}
declare 54 generic {
    int TclBN_mp_karatsuba_sqr(mp_int* a, mp_int* b)
}
declare 55 generic {
    int TclBN_mp_toom_mul(mp_int* a, mp_int* b, mp_int* c)
}
declare 56 generic {
    int TclBN_mp_toom_sqr(mp_int* a, mp_int* b)
}
declare 57 generic {
    int TclBN_s_mp_add(mp_int* a, mp_int* b, mp_int* c)
}
declare 58 generic {
    int TclBN_s_mp_mul_digs(mp_int* a, mp_int* b, mp_int* c, int digs)
}
declare 59 generic {
    int TclBN_s_mp_sqr(mp_int* a, mp_int* b)
}
declare 60 generic {
    int TclBN_s_mp_sub(mp_int* a, mp_int* b, mp_int* c)
}
