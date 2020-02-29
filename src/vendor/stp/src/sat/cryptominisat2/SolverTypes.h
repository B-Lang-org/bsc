/***********************************************************************************[SolverTypes.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/


#ifndef SOLVERTYPES_H
#define SOLVERTYPES_H

#include <cassert>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "Alg.h"
#include <stdio.h>

namespace MINISAT
{
using namespace MINISAT;

//=================================================================================================
// Variables, literals, lifted booleans, clauses:


// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

typedef uint32_t Var;
#define var_Undef (0xffffffffU >>1)
enum RestartType {dynamic_restart, static_restart, auto_restart};

class Lit
{
    uint32_t     x;
    explicit Lit(uint32_t i) : x(i) { };
public:
    Lit() : x(2*var_Undef) {}   // (lit_Undef)
    explicit Lit(Var var, bool sign) : x((var+var) + (int)sign) { }

    const uint32_t& toInt() const { // Guarantees small, positive integers suitable for array indexing.
        return x;
    }
    Lit  operator~() const {
        return Lit(x ^ 1);
    }
    Lit  operator^(const bool b) const {
        return Lit(x ^ (uint32_t)b);
    }
    Lit& operator^=(const bool b) {
        x ^= (uint32_t)b;
        return *this;
    }
    bool sign() const {
        return x & 1;
    }
    Var  var() const {
        return x >> 1;
    }
    Lit  unsign() const {
        return Lit(x & ~1);
    }
    bool operator==(const Lit& p) const {
        return x == p.x;
    }
    bool operator!= (const Lit& p) const {
        return x != p.x;
    }
    bool operator <  (const Lit& p) const {
        return x < p.x;     // '<' guarantees that p, ~p are adjacent in the ordering.
    }
    inline void print(FILE* outfile = stdout) const
    {
        fprintf(outfile,"%s%d", sign() ? "-" : "", var()+1);
    }
    inline void printFull(FILE* outfile = stdout) const
    {
        fprintf(outfile,"%s%d 0\n", sign() ? "-" : "", var()+1);
    }
    static Lit toLit(uint32_t data)
    {
        return Lit(data);
    }
};

const Lit lit_Undef(var_Undef, false);  // Useful special constants.
const Lit lit_Error(var_Undef, true );  //

//=================================================================================================
// Lifted booleans:

class llbool;

class lbool
{
    char     value;
    explicit lbool(char v) : value(v) { }

public:
    lbool()       : value(0) { };
    inline char getchar() const {
        return value;
    }
    inline lbool(llbool b);

    inline const bool isUndef() const {
        return !value;
    }
    inline const bool isDef() const {
        return value;
    }
    inline const bool getBool() const {
        return value == 1;
    }
    inline const bool operator==(lbool b) const {
        return value == b.value;
    }
    inline const bool operator!=(lbool b) const {
        return value != b.value;
    }
    lbool operator^(const bool b) const {
        return b ? lbool(-value) : lbool(value);
    }
    //lbool operator ^ (const bool b) const { return b ? lbool(-value) : lbool(value); }

    friend lbool toLbool(const char v);
    friend lbool boolToLBool(const bool b);
    friend class llbool;
};
inline lbool toLbool(const char   v)
{
    return lbool(v);
}
inline lbool boolToLBool(const bool b)
{
    return lbool(2*b-1);
}

const lbool l_True  = toLbool( 1);
const lbool l_False = toLbool(-1);
const lbool l_Undef = toLbool( 0);


class llbool
{
    char value;

public:
    llbool(): value(0) {};
    llbool(lbool v) :
            value(v.value) {};
    llbool(char a) :
            value(a) {}

    inline const bool operator!=(const llbool& v) const {
        return (v.value != value);
    }

    inline const bool operator==(const llbool& v) const {
        return (v.value == value);
    }

    friend class lbool;
};
const llbool l_Nothing  = toLbool(2);
const llbool l_Continue = toLbool(3);

lbool::lbool(llbool b) : value(b.value) {};

}; //NAMESPACE MINISAT

#endif //SOLVERTYPES_H
