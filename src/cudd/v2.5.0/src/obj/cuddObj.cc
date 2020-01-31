/**CFile***********************************************************************

  FileName    [cuddObj.cc]

  PackageName [cuddObj]

  Synopsis    [Functions for the C++ object-oriented encapsulation of CUDD.]

  Description []

  SeeAlso     []

  Author      [Fabio Somenzi]

  Copyright   [Copyright (c) 1995-2012, Regents of the University of Colorado

  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

  Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

  Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

  Neither the name of the University of Colorado nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
  POSSIBILITY OF SUCH DAMAGE.]

******************************************************************************/
#include <iostream>
#include <sstream>
#include <cassert>
#include <cstdlib>
#include <algorithm>
#include "cuddObj.hh"

using std::cout;
using std::cerr;
using std::endl;
using std::hex;
using std::string;
using std::vector;
using std::sort;

// ---------------------------------------------------------------------------
// Variable declarations
// ---------------------------------------------------------------------------

#ifndef lint
static char rcsid[] UNUSED = "$Id: cuddObj.cc,v 1.15 2012/02/05 01:06:40 fabio Exp fabio $";
#endif

// ---------------------------------------------------------------------------
// Members of class DD
// ---------------------------------------------------------------------------


DD::DD() : p(0), node(0) {}


DD::DD(Capsule *cap, DdNode *ddNode) : p(cap), node(ddNode) {
    if (node != 0) Cudd_Ref(node);
    if (p->verbose) {
	cout << "Standard DD constructor for node " << hex << long(node) <<
	    " ref = " << Cudd_Regular(node)->ref << "\n";
    }

} // DD::DD


DD::DD(Cudd const & manager, DdNode *ddNode) : p(manager.p), node(ddNode) {
    checkReturnValue(ddNode);
    if (node != 0) Cudd_Ref(node);
    if (p->verbose) {
	cout << "Standard DD constructor for node " << hex << long(node) <<
	    " ref = " << Cudd_Regular(node)->ref << "\n";
    }

} // DD::DD


DD::DD(const DD &from) {
    p = from.p;
    node = from.node;
    if (node != 0) {
	Cudd_Ref(node);
	if (p->verbose) {
	    cout << "Copy DD constructor for node " << hex << long(node) <<
		" ref = " << Cudd_Regular(node)->ref << "\n";
	}
    }

} // DD::DD


DD::~DD() {}


inline DdManager *
DD::checkSameManager(
  const DD &other) const
{
    DdManager *mgr = p->manager;
    if (mgr != other.p->manager) {
	p->errorHandler("Operands come from different manager.");
    }
    return mgr;

} // DD::checkSameManager


inline void
DD::checkReturnValue(
  const DdNode *result) const
{
    if (result == 0) {
	DdManager *mgr = p->manager;
	Cudd_ErrorType errType = Cudd_ReadErrorCode(mgr);
	switch (errType) {
	case CUDD_MEMORY_OUT:
	    p->errorHandler("Out of memory.");
	    break;
	case CUDD_TOO_MANY_NODES:
	    break;
	case CUDD_MAX_MEM_EXCEEDED:
	    p->errorHandler("Maximum memory exceeded.");
	    break;
        case CUDD_TIMEOUT_EXPIRED: 
            {
                std::ostringstream msg;
                unsigned long lag = 
                    Cudd_ReadElapsedTime(mgr) - Cudd_ReadTimeLimit(mgr);
                msg << "Timeout expired.  Lag = " << lag << " ms.\n";
                p->timeoutHandler(msg.str());
            }
	    break;
	case CUDD_INVALID_ARG:
	    p->errorHandler("Invalid argument.");
	    break;
	case CUDD_INTERNAL_ERROR:
	    p->errorHandler("Internal error.");
	    break;
	case CUDD_NO_ERROR:
	default:
	    p->errorHandler("Unexpected error.");
	    break;
	}
    }

} // DD::checkReturnValue


inline void
DD::checkReturnValue(
  const int result,
  const int expected) const
{
    if (result != expected) {
	DdManager *mgr = p->manager;
	Cudd_ErrorType errType = Cudd_ReadErrorCode(mgr);
	switch (errType) {
	case CUDD_MEMORY_OUT:
	    p->errorHandler("Out of memory.");
	    break;
	case CUDD_TOO_MANY_NODES:
	    break;
	case CUDD_MAX_MEM_EXCEEDED:
	    p->errorHandler("Maximum memory exceeded.");
	    break;
        case CUDD_TIMEOUT_EXPIRED:
            {
                std::ostringstream msg;
                unsigned long lag = 
                    Cudd_ReadElapsedTime(mgr) - Cudd_ReadTimeLimit(mgr);
                msg << "Timeout expired.  Lag = " << lag << " ms.\n";
                p->timeoutHandler(msg.str());
            }
	    break;
	case CUDD_INVALID_ARG:
	    p->errorHandler("Invalid argument.");
	    break;
	case CUDD_INTERNAL_ERROR:
	    p->errorHandler("Internal error.");
	    break;
	case CUDD_NO_ERROR:
	default:
	    p->errorHandler("Unexpected error.");
	    break;
	}
    }

} // DD::checkReturnValue


DdManager *
DD::manager() const
{
    return p->manager;

} // DD::manager


DdNode *
DD::getNode() const
{
    return node;

} // DD::getNode


DdNode *
DD::getRegularNode() const
{
    return Cudd_Regular(node);

} // DD::getRegularNode


int
DD::nodeCount() const
{
    return Cudd_DagSize(node);

} // DD::nodeCount


unsigned int
DD::NodeReadIndex() const
{
    return Cudd_NodeReadIndex(node);

} // DD::NodeReadIndex


// ---------------------------------------------------------------------------
// Members of class ABDD
// ---------------------------------------------------------------------------


ABDD::ABDD() : DD() {}
ABDD::ABDD(Capsule *cap, DdNode *bddNode) : DD(cap,bddNode) {}
ABDD::ABDD(Cudd const & manager, DdNode *bddNode) : DD(manager,bddNode) {}
ABDD::ABDD(const ABDD &from) : DD(from) {}


ABDD::~ABDD() {
    if (node != 0) {
	Cudd_RecursiveDeref(p->manager,node);
	if (p->verbose) {
	    cout << "ADD/BDD destructor called for node " << hex <<
		long(node) << " ref = " << Cudd_Regular(node)->ref << "\n";
	}
    }

} // ABDD::~ABDD


bool
ABDD::operator==(
  const ABDD& other) const
{
    checkSameManager(other);
    return node == other.node;

} // ABDD::operator==


bool
ABDD::operator!=(
  const ABDD& other) const
{
    checkSameManager(other);
    return node != other.node;

} // ABDD::operator!=


bool
ABDD::IsOne() const
{
    return node == Cudd_ReadOne(p->manager);

} // ABDD::IsOne


void
ABDD::print(
  int nvars,
  int verbosity) const
{
    cout.flush();
    int retval = Cudd_PrintDebug(p->manager,node,nvars,verbosity);
    if (retval == 0) p->errorHandler("print failed");

} // ABDD::print


// ---------------------------------------------------------------------------
// Members of class BDD
// ---------------------------------------------------------------------------

BDD::BDD() : ABDD() {}
BDD::BDD(Capsule *cap, DdNode *bddNode) : ABDD(cap,bddNode) {}
BDD::BDD(Cudd const & manager, DdNode *bddNode) : ABDD(manager,bddNode) {}
BDD::BDD(const BDD &from) : ABDD(from) {}


BDD
BDD::operator=(
  const BDD& right)
{
    if (this == &right) return *this;
    if (right.node != 0) Cudd_Ref(right.node);
    if (node != 0) {
	Cudd_RecursiveDeref(p->manager,node);
	if (p->verbose) {
	    cout << "BDD dereferencing for node " << hex << long(node) <<
		" ref = " << Cudd_Regular(node)->ref << "\n";
	}
    }
    node = right.node;
    p = right.p;
    if (node != 0 && p->verbose) {
	cout << "BDD assignment for node " << hex << long(node) <<
	    " ref = " << Cudd_Regular(node)->ref << "\n";
    }
    return *this;

} // BDD::operator=


bool
BDD::operator<=(
  const BDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return Cudd_bddLeq(mgr,node,other.node);

} // BDD::operator<=


bool
BDD::operator>=(
  const BDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return Cudd_bddLeq(mgr,other.node,node);

} // BDD::operator>=


bool
BDD::operator<(
  const BDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return node != other.node && Cudd_bddLeq(mgr,node,other.node);

} // BDD::operator<


bool
BDD::operator>(
  const BDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return node != other.node && Cudd_bddLeq(mgr,other.node,node);

} // BDD::operator>


BDD
BDD::operator!() const
{
    return BDD(p, Cudd_Not(node));

} // BDD::operator!


BDD
BDD::operator~() const
{
    return BDD(p, Cudd_Not(node));

} // BDD::operator~


BDD
BDD::operator*(
  const BDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddAnd(mgr,node,other.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::operator*


BDD
BDD::operator*=(
  const BDD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddAnd(mgr,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDeref(mgr,node);
    node = result;
    return *this;

} // BDD::operator*=


BDD
BDD::operator&(
  const BDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddAnd(mgr,node,other.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::operator&


BDD
BDD::operator&=(
  const BDD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddAnd(mgr,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDeref(mgr,node);
    node = result;
    return *this;

} // BDD::operator&=


BDD
BDD::operator+(
  const BDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddOr(mgr,node,other.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::operator+


BDD
BDD::operator+=(
  const BDD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddOr(mgr,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDeref(mgr,node);
    node = result;
    return *this;

} // BDD::operator+=


BDD
BDD::operator|(
  const BDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddOr(mgr,node,other.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::operator|


BDD
BDD::operator|=(
  const BDD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddOr(mgr,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDeref(mgr,node);
    node = result;
    return *this;

} // BDD::operator|=


BDD
BDD::operator^(
  const BDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddXor(mgr,node,other.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::operator^


BDD
BDD::operator^=(
  const BDD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddXor(mgr,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDeref(mgr,node);
    node = result;
    return *this;

} // BDD::operator^=


BDD
BDD::operator-(
  const BDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddAnd(mgr,node,Cudd_Not(other.node));
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::operator-


BDD
BDD::operator-=(
  const BDD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_bddAnd(mgr,node,Cudd_Not(other.node));
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDeref(mgr,node);
    node = result;
    return *this;

} // BDD::operator-=


bool
BDD::IsZero() const
{
    return node == Cudd_ReadLogicZero(p->manager);

} // BDD::IsZero


// ---------------------------------------------------------------------------
// Members of class ADD
// ---------------------------------------------------------------------------


ADD::ADD() : ABDD() {}
ADD::ADD(Capsule *cap, DdNode *bddNode) : ABDD(cap,bddNode) {}
ADD::ADD(Cudd const & manager, DdNode *bddNode) : ABDD(manager,bddNode) {}
ADD::ADD(const ADD &from) : ABDD(from) {}


ADD
ADD::operator=(
  const ADD& right)
{
    if (this == &right) return *this;
    if (right.node != 0) Cudd_Ref(right.node);
    if (node != 0) {
	Cudd_RecursiveDeref(p->manager,node);
    }
    node = right.node;
    p = right.p;
    return *this;

} // ADD::operator=


bool
ADD::operator<=(
  const ADD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return Cudd_addLeq(mgr,node,other.node);

} // ADD::operator<=


bool
ADD::operator>=(
  const ADD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return Cudd_addLeq(mgr,other.node,node);

} // ADD::operator>=


bool
ADD::operator<(
  const ADD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return node != other.node && Cudd_addLeq(mgr,node,other.node);

} // ADD::operator<


bool
ADD::operator>(
  const ADD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return node != other.node && Cudd_addLeq(mgr,other.node,node);

} // ADD::operator>


ADD
ADD::operator-() const
{
    return ADD(p, Cudd_addNegate(p->manager,node));

} // ADD::operator-


ADD
ADD::operator*(
  const ADD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_addApply(mgr,Cudd_addTimes,node,other.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::operator*


ADD
ADD::operator*=(
  const ADD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_addApply(mgr,Cudd_addTimes,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDeref(mgr,node);
    node = result;
    return *this;

} // ADD::operator*=


ADD
ADD::operator+(
  const ADD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_addApply(mgr,Cudd_addPlus,node,other.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::operator+


ADD
ADD::operator+=(
  const ADD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_addApply(mgr,Cudd_addPlus,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDeref(mgr,node);
    node = result;
    return *this;

} // ADD::operator+=


ADD
ADD::operator-(
  const ADD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_addApply(mgr,Cudd_addMinus,node,other.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::operator-


ADD
ADD::operator-=(
  const ADD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_addApply(mgr,Cudd_addMinus,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDeref(mgr,node);
    node = result;
    return *this;

} // ADD::operator-=


ADD
ADD::operator~() const
{
    return ADD(p, Cudd_addCmpl(p->manager,node));

} // ADD::operator~


ADD
ADD::operator&(
  const ADD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_addApply(mgr,Cudd_addTimes,node,other.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::operator&


ADD
ADD::operator&=(
  const ADD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_addApply(mgr,Cudd_addTimes,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDeref(mgr,node);
    node = result;
    return *this;

} // ADD::operator&=


ADD
ADD::operator|(
  const ADD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_addApply(mgr,Cudd_addOr,node,other.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::operator|


ADD
ADD::operator|=(
  const ADD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_addApply(mgr,Cudd_addOr,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDeref(mgr,node);
    node = result;
    return *this;

} // ADD::operator|=


bool
ADD::IsZero() const
{
    return node == Cudd_ReadZero(p->manager);

} // ADD::IsZero


// ---------------------------------------------------------------------------
// Members of class ZDD
// ---------------------------------------------------------------------------


ZDD::ZDD(Capsule *cap, DdNode *bddNode) : DD(cap,bddNode) {}
ZDD::ZDD() : DD() {}
ZDD::ZDD(const ZDD &from) : DD(from) {}


ZDD::~ZDD() {
    if (node != 0) {
	Cudd_RecursiveDerefZdd(p->manager,node);
	if (p->verbose) {
	    cout << "ZDD destructor called for node " << hex << long(node) <<
		" ref = " << Cudd_Regular(node)->ref << "\n";
	}
    }

} // ZDD::~ZDD


ZDD
ZDD::operator=(
  const ZDD& right)
{
    if (this == &right) return *this;
    if (right.node != 0) Cudd_Ref(right.node);
    if (node != 0) {
	Cudd_RecursiveDerefZdd(p->manager,node);
	if (p->verbose) {
	    cout << "ZDD dereferencing for node " << hex << long(node) <<
		" ref = " << node->ref << "\n";
	}
    }
    node = right.node;
    p = right.p;
    if (node != 0 && p->verbose) {
	cout << "ZDD assignment for node " << hex << long(node) <<
	    " ref = " << node->ref << "\n";
    }
    return *this;

} // ZDD::operator=


bool
ZDD::operator==(
  const ZDD& other) const
{
    checkSameManager(other);
    return node == other.node;

} // ZDD::operator==


bool
ZDD::operator!=(
  const ZDD& other) const
{
    checkSameManager(other);
    return node != other.node;

} // ZDD::operator!=


bool
ZDD::operator<=(
  const ZDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return Cudd_zddDiffConst(mgr,node,other.node) == Cudd_ReadZero(mgr);

} // ZDD::operator<=


bool
ZDD::operator>=(
  const ZDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return Cudd_zddDiffConst(mgr,other.node,node) == Cudd_ReadZero(mgr);

} // ZDD::operator>=


bool
ZDD::operator<(
  const ZDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return node != other.node &&
	Cudd_zddDiffConst(mgr,node,other.node) == Cudd_ReadZero(mgr);

} // ZDD::operator<


bool
ZDD::operator>(
  const ZDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    return node != other.node &&
	Cudd_zddDiffConst(mgr,other.node,node) == Cudd_ReadZero(mgr);

} // ZDD::operator>


void
ZDD::print(
  int nvars,
  int verbosity) const
{
    cout.flush();
    int retval = Cudd_zddPrintDebug(p->manager,node,nvars,verbosity);
    if (retval == 0) p->errorHandler("print failed");

} // ZDD::print


ZDD
ZDD::operator*(
  const ZDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_zddIntersect(mgr,node,other.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::operator*


ZDD
ZDD::operator*=(
  const ZDD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_zddIntersect(mgr,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDerefZdd(mgr,node);
    node = result;
    return *this;

} // ZDD::operator*=


ZDD
ZDD::operator&(
  const ZDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_zddIntersect(mgr,node,other.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::operator&


ZDD
ZDD::operator&=(
  const ZDD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_zddIntersect(mgr,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDerefZdd(mgr,node);
    node = result;
    return *this;

} // ZDD::operator&=


ZDD
ZDD::operator+(
  const ZDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_zddUnion(mgr,node,other.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::operator+


ZDD
ZDD::operator+=(
  const ZDD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_zddUnion(mgr,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDerefZdd(mgr,node);
    node = result;
    return *this;

} // ZDD::operator+=


ZDD
ZDD::operator|(
  const ZDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_zddUnion(mgr,node,other.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::operator|


ZDD
ZDD::operator|=(
  const ZDD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_zddUnion(mgr,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDerefZdd(mgr,node);
    node = result;
    return *this;

} // ZDD::operator|=


ZDD
ZDD::operator-(
  const ZDD& other) const
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_zddDiff(mgr,node,other.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::operator-


ZDD
ZDD::operator-=(
  const ZDD& other)
{
    DdManager *mgr = checkSameManager(other);
    DdNode *result = Cudd_zddDiff(mgr,node,other.node);
    checkReturnValue(result);
    Cudd_Ref(result);
    Cudd_RecursiveDerefZdd(mgr,node);
    node = result;
    return *this;

} // ZDD::operator-=


// ---------------------------------------------------------------------------
// Members of class Cudd
// ---------------------------------------------------------------------------


Cudd::Cudd(
  unsigned int numVars,
  unsigned int numVarsZ,
  unsigned int numSlots,
  unsigned int cacheSize,
  unsigned long maxMemory)
{
    p = new Capsule;
    p->manager = Cudd_Init(numVars,numVarsZ,numSlots,cacheSize,maxMemory);
    p->errorHandler = defaultError;
    p->timeoutHandler = defaultError;
    p->verbose = 0;		// initially terse
    p->ref = 1;

} // Cudd::Cudd


Cudd::Cudd(
  const Cudd& x)
{
    p = x.p;
    x.p->ref++;
    if (p->verbose)
        cout << "Cudd Copy Constructor" << endl;

} // Cudd::Cudd


Cudd::~Cudd()
{
    if (--p->ref == 0) {
#ifdef DD_DEBUG
	int retval = Cudd_CheckZeroRef(p->manager);
	if (retval != 0) {
	    cerr << retval << " unexpected non-zero reference counts" << endl;
	} else if (p->verbose) {
	    cerr << "All went well" << endl;
	}
#endif
	Cudd_Quit(p->manager);
	delete p;
    }

} // Cudd::~Cudd


Cudd&
Cudd::operator=(
  const Cudd& right)
{
    right.p->ref++;
    if (--p->ref == 0) {	// disconnect self
	int retval = Cudd_CheckZeroRef(p->manager);
	if (retval != 0) {
	    cerr << retval << " unexpected non-zero reference counts" << endl;
	} else if (p->verbose) {
	    cerr << "All went well\n";
	}
	Cudd_Quit(p->manager);
	delete p;
    }
    p = right.p;
    return *this;

} // Cudd::operator=


PFC
Cudd::setHandler(
  PFC newHandler) const
{
    PFC oldHandler = p->errorHandler;
    p->errorHandler = newHandler;
    return oldHandler;

} // Cudd::setHandler


PFC
Cudd::getHandler() const
{
    return p->errorHandler;

} // Cudd::getHandler


PFC
Cudd::setTimeoutHandler(
  PFC newHandler) const
{
    PFC oldHandler = p->timeoutHandler;
    p->timeoutHandler = newHandler;
    return oldHandler;

} // Cudd::setTimeoutHandler


PFC
Cudd::getTimeoutHandler() const
{
    return p->timeoutHandler;

} // Cudd::getTimeourHandler


inline void
Cudd::checkReturnValue(
  const DdNode *result) const
{
    if (result == 0) {
	if (Cudd_ReadErrorCode(p->manager) == CUDD_MEMORY_OUT) {
	    p->errorHandler("Out of memory.");
        } else if (Cudd_ReadErrorCode(p->manager) == CUDD_TOO_MANY_NODES) {
            p->errorHandler("Too many nodes.");
        } else if (Cudd_ReadErrorCode(p->manager) == CUDD_MAX_MEM_EXCEEDED) {
            p->errorHandler("Maximum memory exceeded.");
        } else if (Cudd_ReadErrorCode(p->manager) == CUDD_TIMEOUT_EXPIRED) {
            std::ostringstream msg;
            DdManager *mgr = p->manager;
            unsigned long lag = 
                Cudd_ReadElapsedTime(mgr) - Cudd_ReadTimeLimit(mgr);
            msg << "Timeout expired.  Lag = " << lag << " ms.\n";
            p->timeoutHandler(msg.str());
        } else if (Cudd_ReadErrorCode(p->manager) == CUDD_INVALID_ARG) {
            p->errorHandler("Invalid argument.");
	} else if (Cudd_ReadErrorCode(p->manager) == CUDD_INTERNAL_ERROR) {
	    p->errorHandler("Internal error.");
	} else {
            p->errorHandler("Unexpected error.");
        }
    }

} // Cudd::checkReturnValue


inline void
Cudd::checkReturnValue(
  const int result) const
{
    if (result == 0) {
	if (Cudd_ReadErrorCode(p->manager) == CUDD_MEMORY_OUT) {
	    p->errorHandler("Out of memory.");
        } else if (Cudd_ReadErrorCode(p->manager) == CUDD_TOO_MANY_NODES) {
            p->errorHandler("Too many nodes.");
        } else if (Cudd_ReadErrorCode(p->manager) == CUDD_MAX_MEM_EXCEEDED) {
            p->errorHandler("Maximum memory exceeded.");
        } else if (Cudd_ReadErrorCode(p->manager) == CUDD_TIMEOUT_EXPIRED) {
            std::ostringstream msg;
            DdManager *mgr = p->manager;
            unsigned long lag = 
                Cudd_ReadElapsedTime(mgr) - Cudd_ReadTimeLimit(mgr);
            msg << "Timeout expired.  Lag = " << lag << " ms.\n";
            p->timeoutHandler(msg.str());
        } else if (Cudd_ReadErrorCode(p->manager) == CUDD_INVALID_ARG) {
            p->errorHandler("Invalid argument.");
	} else if (Cudd_ReadErrorCode(p->manager) == CUDD_INTERNAL_ERROR) {
	    p->errorHandler("Internal error.");
	} else {
	    p->errorHandler("Unexpected error.");
	}
    }

} // Cudd::checkReturnValue


void
Cudd::info() const
{
    cout.flush();
    int retval = Cudd_PrintInfo(p->manager,stdout);
    checkReturnValue(retval);

} // Cudd::info


BDD
Cudd::bddVar() const
{
    DdNode *result = Cudd_bddNewVar(p->manager);
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::bddVar


BDD
Cudd::bddVar(
  int index) const
{
    DdNode *result = Cudd_bddIthVar(p->manager,index);
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::bddVar


BDD
Cudd::bddOne() const
{
    DdNode *result = Cudd_ReadOne(p->manager);
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::bddOne


BDD
Cudd::bddZero() const
{
    DdNode *result = Cudd_ReadLogicZero(p->manager);
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::bddZero


ADD
Cudd::addVar() const
{
    DdNode *result = Cudd_addNewVar(p->manager);
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::addVar


ADD
Cudd::addVar(
  int index) const
{
    DdNode *result = Cudd_addIthVar(p->manager,index);
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::addVar


ADD
Cudd::addOne() const
{
    DdNode *result = Cudd_ReadOne(p->manager);
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::addOne


ADD
Cudd::addZero() const
{
    DdNode *result = Cudd_ReadZero(p->manager);
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::addZero


ADD
Cudd::constant(
  CUDD_VALUE_TYPE c) const
{
    DdNode *result = Cudd_addConst(p->manager, c);
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::constant


ADD
Cudd::plusInfinity() const
{
    DdNode *result = Cudd_ReadPlusInfinity(p->manager);
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::plusInfinity


ADD
Cudd::minusInfinity() const
{
    DdNode *result = Cudd_ReadMinusInfinity(p->manager);
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::minusInfinity


ZDD
Cudd::zddVar(
  int index) const
{
    DdNode *result = Cudd_zddIthVar(p->manager,index);
    checkReturnValue(result);
    return ZDD(p, result);

} // Cudd::zddVar


ZDD
Cudd::zddOne(
  int i) const
{
    DdNode *result = Cudd_ReadZddOne(p->manager,i);
    checkReturnValue(result);
    return ZDD(p, result);

} // Cudd::zddOne


ZDD
Cudd::zddZero() const
{
    DdNode *result = Cudd_ReadZero(p->manager);
    checkReturnValue(result);
    return ZDD(p, result);

} // Cudd::zddZero


void
defaultError(
  string message)
{
    cerr << message << endl;
    assert(false);

} // defaultError


// ---------------------------------------------------------------------------
// All the rest
// ---------------------------------------------------------------------------



ADD
Cudd::addNewVarAtLevel(
  int level) const
{
    DdNode *result = Cudd_addNewVarAtLevel(p->manager, level);
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::addNewVarAtLevel


BDD
Cudd::bddNewVarAtLevel(
  int level) const
{
    DdNode *result = Cudd_bddNewVarAtLevel(p->manager, level);
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::bddNewVarAtLevel


void
Cudd::zddVarsFromBddVars(
  int multiplicity) const
{
    int result = Cudd_zddVarsFromBddVars(p->manager, multiplicity);
    checkReturnValue(result);

} // Cudd::zddVarsFromBddVars


unsigned long
Cudd::ReadStartTime() const
{
    return Cudd_ReadStartTime(p->manager);

} // Cudd::ReadStartTime


unsigned long
Cudd::ReadElapsedTime() const
{
    return Cudd_ReadElapsedTime(p->manager);

} // Cudd::ReadElapsedTime


void 
Cudd::SetStartTime(
  unsigned long st) const
{
    Cudd_SetStartTime(p->manager, st);

} // Cudd::SetStartTime


void 
Cudd::ResetStartTime() const
{
    Cudd_ResetStartTime(p->manager);

} // Cudd::ResetStartTime


unsigned long
Cudd::ReadTimeLimit() const
{
    return Cudd_ReadTimeLimit(p->manager);

} // Cudd::ReadTimeLimit


void 
Cudd::SetTimeLimit(
  unsigned long tl) const
{
    Cudd_SetTimeLimit(p->manager, tl);

} // Cudd::SetTimeLimit


void
Cudd::UpdateTimeLimit() const
{
    Cudd_UpdateTimeLimit(p->manager);

} // Cudd::UpdateTimeLimit


void
Cudd::IncreaseTimeLimit(
  unsigned long increase) const
{
    Cudd_IncreaseTimeLimit(p->manager, increase);

} // Cudd::IncreaseTimeLimit


void 
Cudd::UnsetTimeLimit() const
{
    Cudd_UnsetTimeLimit(p->manager);

} // Cudd::UnsetTimeLimit


bool
Cudd::TimeLimited() const
{
    return Cudd_TimeLimited(p->manager);

} // Cudd::TimeLimited


void
Cudd::AutodynEnable(
  Cudd_ReorderingType method) const
{
    Cudd_AutodynEnable(p->manager, method);

} // Cudd::AutodynEnable


void
Cudd::AutodynDisable() const
{
    Cudd_AutodynDisable(p->manager);

} // Cudd::AutodynDisable


bool
Cudd::ReorderingStatus(
  Cudd_ReorderingType * method) const
{
    return Cudd_ReorderingStatus(p->manager, method);

} // Cudd::ReorderingStatus


void
Cudd::AutodynEnableZdd(
  Cudd_ReorderingType method) const
{
    Cudd_AutodynEnableZdd(p->manager, method);

} // Cudd::AutodynEnableZdd


void
Cudd::AutodynDisableZdd() const
{
    Cudd_AutodynDisableZdd(p->manager);

} // Cudd::AutodynDisableZdd


bool
Cudd::ReorderingStatusZdd(
  Cudd_ReorderingType * method) const
{
    return Cudd_ReorderingStatusZdd(p->manager, method);

} // Cudd::ReorderingStatusZdd


bool
Cudd::zddRealignmentEnabled() const
{
    return Cudd_zddRealignmentEnabled(p->manager);

} // Cudd::zddRealignmentEnabled


void
Cudd::zddRealignEnable() const
{
    Cudd_zddRealignEnable(p->manager);

} // Cudd::zddRealignEnable


void
Cudd::zddRealignDisable() const
{
    Cudd_zddRealignDisable(p->manager);

} // Cudd::zddRealignDisable


bool
Cudd::bddRealignmentEnabled() const
{
    return Cudd_bddRealignmentEnabled(p->manager);

} // Cudd::bddRealignmentEnabled


void
Cudd::bddRealignEnable() const
{
    Cudd_bddRealignEnable(p->manager);

} // Cudd::bddRealignEnable


void
Cudd::bddRealignDisable() const
{
    Cudd_bddRealignDisable(p->manager);

} // Cudd::bddRealignDisable


ADD
Cudd::background() const
{
    DdNode *result = Cudd_ReadBackground(p->manager);
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::background


void
Cudd::SetBackground(
  ADD bg) const
{
    DdManager *mgr = p->manager;
    if (mgr != bg.manager()) {
	p->errorHandler("Background comes from different manager.");
    }
    Cudd_SetBackground(mgr, bg.getNode());

} // Cudd::SetBackground


unsigned int
Cudd::ReadCacheSlots() const
{
    return Cudd_ReadCacheSlots(p->manager);

} // Cudd::ReadCacheSlots


double
Cudd::ReadCacheLookUps() const
{
    return Cudd_ReadCacheLookUps(p->manager);

} // Cudd::ReadCacheLookUps


double
Cudd::ReadCacheUsedSlots() const
{
    return Cudd_ReadCacheUsedSlots(p->manager);

} // Cudd::ReadCacheUsedSlots


double
Cudd::ReadCacheHits() const
{
    return Cudd_ReadCacheHits(p->manager);

} // Cudd::ReadCacheHits


unsigned int
Cudd::ReadMinHit() const
{
    return Cudd_ReadMinHit(p->manager);

} // Cudd::ReadMinHit


void
Cudd::SetMinHit(
  unsigned int hr) const
{
    Cudd_SetMinHit(p->manager, hr);

} // Cudd::SetMinHit


unsigned int
Cudd::ReadLooseUpTo() const
{
    return Cudd_ReadLooseUpTo(p->manager);

} // Cudd::ReadLooseUpTo


void
Cudd::SetLooseUpTo(
  unsigned int lut) const
{
    Cudd_SetLooseUpTo(p->manager, lut);

} // Cudd::SetLooseUpTo


unsigned int
Cudd::ReadMaxCache() const
{
    return Cudd_ReadMaxCache(p->manager);

} // Cudd::ReadMaxCache


unsigned int
Cudd::ReadMaxCacheHard() const
{
    return Cudd_ReadMaxCacheHard(p->manager);

} // Cudd::ReadMaxCacheHard


void
Cudd::SetMaxCacheHard(
  unsigned int mc) const
{
    Cudd_SetMaxCacheHard(p->manager, mc);

} // Cudd::SetMaxCacheHard


int
Cudd::ReadSize() const
{
    return Cudd_ReadSize(p->manager);

} // Cudd::ReadSize


int
Cudd::ReadZddSize() const
{
    return Cudd_ReadZddSize(p->manager);

} // Cudd::ReadZddSize


unsigned int
Cudd::ReadSlots() const
{
    return Cudd_ReadSlots(p->manager);

} // Cudd::ReadSlots


unsigned int
Cudd::ReadKeys() const
{
    return Cudd_ReadKeys(p->manager);

} // Cudd::ReadKeys


unsigned int
Cudd::ReadDead() const
{
    return Cudd_ReadDead(p->manager);

} // Cudd::ReadDead


unsigned int
Cudd::ReadMinDead() const
{
    return Cudd_ReadMinDead(p->manager);

} // Cudd::ReadMinDead


unsigned int
Cudd::ReadReorderings() const
{
    return Cudd_ReadReorderings(p->manager);

} // Cudd::ReadReorderings


unsigned int
Cudd::ReadMaxReorderings() const
{
    return Cudd_ReadMaxReorderings(p->manager);

} // Cudd::ReadMaxReorderings

void
Cudd::SetMaxReorderings(
  unsigned int mr) const
{
    Cudd_SetMaxReorderings(p->manager, mr);

} // Cudd::SetMaxReorderings

long
Cudd::ReadReorderingTime() const
{
    return Cudd_ReadReorderingTime(p->manager);

} // Cudd::ReadReorderingTime


int
Cudd::ReadGarbageCollections() const
{
    return Cudd_ReadGarbageCollections(p->manager);

} // Cudd::ReadGarbageCollections


long
Cudd::ReadGarbageCollectionTime() const
{
    return Cudd_ReadGarbageCollectionTime(p->manager);

} // Cudd::ReadGarbageCollectionTime


int
Cudd::ReadSiftMaxVar() const
{
    return Cudd_ReadSiftMaxVar(p->manager);

} // Cudd::ReadSiftMaxVar


void
Cudd::SetSiftMaxVar(
  int smv) const
{
    Cudd_SetSiftMaxVar(p->manager, smv);

} // Cudd::SetSiftMaxVar


int
Cudd::ReadSiftMaxSwap() const
{
    return Cudd_ReadSiftMaxSwap(p->manager);

} // Cudd::ReadSiftMaxSwap


void
Cudd::SetSiftMaxSwap(
  int sms) const
{
    Cudd_SetSiftMaxSwap(p->manager, sms);

} // Cudd::SetSiftMaxSwap


double
Cudd::ReadMaxGrowth() const
{
    return Cudd_ReadMaxGrowth(p->manager);

} // Cudd::ReadMaxGrowth


void
Cudd::SetMaxGrowth(
  double mg) const
{
    Cudd_SetMaxGrowth(p->manager, mg);

} // Cudd::SetMaxGrowth


MtrNode *
Cudd::ReadTree() const
{
    return Cudd_ReadTree(p->manager);

} // Cudd::ReadTree


void
Cudd::SetTree(
  MtrNode * tree) const
{
    Cudd_SetTree(p->manager, tree);

} // Cudd::SetTree


void
Cudd::FreeTree() const
{
    Cudd_FreeTree(p->manager);

} // Cudd::FreeTree


MtrNode *
Cudd::ReadZddTree() const
{
    return Cudd_ReadZddTree(p->manager);

} // Cudd::ReadZddTree


void
Cudd::SetZddTree(
  MtrNode * tree) const
{
    Cudd_SetZddTree(p->manager, tree);

} // Cudd::SetZddTree


void
Cudd::FreeZddTree() const
{
    Cudd_FreeZddTree(p->manager);

} // Cudd::FreeZddTree


int
Cudd::ReadPerm(
  int i) const
{
    return Cudd_ReadPerm(p->manager, i);

} // Cudd::ReadPerm


int
Cudd::ReadPermZdd(
  int i) const
{
    return Cudd_ReadPermZdd(p->manager, i);

} // Cudd::ReadPermZdd


int
Cudd::ReadInvPerm(
  int i) const
{
    return Cudd_ReadInvPerm(p->manager, i);

} // Cudd::ReadInvPerm


int
Cudd::ReadInvPermZdd(
  int i) const
{
    return Cudd_ReadInvPermZdd(p->manager, i);

} // Cudd::ReadInvPermZdd


BDD
Cudd::ReadVars(
  int i) const
{
    DdNode *result = Cudd_ReadVars(p->manager, i);
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::ReadVars


CUDD_VALUE_TYPE
Cudd::ReadEpsilon() const
{
    return Cudd_ReadEpsilon(p->manager);

} // Cudd::ReadEpsilon


void
Cudd::SetEpsilon(
  CUDD_VALUE_TYPE ep) const
{
    Cudd_SetEpsilon(p->manager, ep);

} // Cudd::SetEpsilon


Cudd_AggregationType
Cudd::ReadGroupcheck() const
{
    return Cudd_ReadGroupcheck(p->manager);

} // Cudd::ReadGroupcheck


void
Cudd::SetGroupcheck(
  Cudd_AggregationType gc) const
{
    Cudd_SetGroupcheck(p->manager, gc);

} // Cudd::SetGroupcheck


bool
Cudd::GarbageCollectionEnabled() const
{
    return Cudd_GarbageCollectionEnabled(p->manager);

} // Cudd::GarbageCollectionEnabled


void
Cudd::EnableGarbageCollection() const
{
    Cudd_EnableGarbageCollection(p->manager);

} // Cudd::EnableGarbageCollection


void
Cudd::DisableGarbageCollection() const
{
    Cudd_DisableGarbageCollection(p->manager);

} // Cudd::DisableGarbageCollection


bool
Cudd::DeadAreCounted() const
{
    return Cudd_DeadAreCounted(p->manager);

} // Cudd::DeadAreCounted


void
Cudd::TurnOnCountDead() const
{
    Cudd_TurnOnCountDead(p->manager);

} // Cudd::TurnOnCountDead


void
Cudd::TurnOffCountDead() const
{
    Cudd_TurnOffCountDead(p->manager);

} // Cudd::TurnOffCountDead


int
Cudd::ReadRecomb() const
{
    return Cudd_ReadRecomb(p->manager);

} // Cudd::ReadRecomb


void
Cudd::SetRecomb(
  int recomb) const
{
    Cudd_SetRecomb(p->manager, recomb);

} // Cudd::SetRecomb


int
Cudd::ReadSymmviolation() const
{
    return Cudd_ReadSymmviolation(p->manager);

} // Cudd::ReadSymmviolation


void
Cudd::SetSymmviolation(
  int symmviolation) const
{
    Cudd_SetSymmviolation(p->manager, symmviolation);

} // Cudd::SetSymmviolation


int
Cudd::ReadArcviolation() const
{
    return Cudd_ReadArcviolation(p->manager);

} // Cudd::ReadArcviolation


void
Cudd::SetArcviolation(
  int arcviolation) const
{
    Cudd_SetArcviolation(p->manager, arcviolation);

} // Cudd::SetArcviolation


int
Cudd::ReadPopulationSize() const
{
    return Cudd_ReadPopulationSize(p->manager);

} // Cudd::ReadPopulationSize


void
Cudd::SetPopulationSize(
  int populationSize) const
{
    Cudd_SetPopulationSize(p->manager, populationSize);

} // Cudd::SetPopulationSize


int
Cudd::ReadNumberXovers() const
{
    return Cudd_ReadNumberXovers(p->manager);

} // Cudd::ReadNumberXovers


void
Cudd::SetNumberXovers(
  int numberXovers) const
{
    Cudd_SetNumberXovers(p->manager, numberXovers);

} // Cudd::SetNumberXovers


unsigned int 
Cudd::ReadOrderRandomization() const
{
    return Cudd_ReadOrderRandomization(p->manager);

} // Cudd::ReadOrderRandomization


void 
Cudd::SetOrderRandomization(
  unsigned int factor) const
{
    Cudd_SetOrderRandomization(p->manager, factor);

} // Cudd::SetOrderRandomization


unsigned long
Cudd::ReadMemoryInUse() const
{
    return Cudd_ReadMemoryInUse(p->manager);

} // Cudd::ReadMemoryInUse


long
Cudd::ReadPeakNodeCount() const
{
    return Cudd_ReadPeakNodeCount(p->manager);

} // Cudd::ReadPeakNodeCount


long
Cudd::ReadNodeCount() const
{
    return Cudd_ReadNodeCount(p->manager);

} // Cudd::ReadNodeCount


long
Cudd::zddReadNodeCount() const
{
    return Cudd_zddReadNodeCount(p->manager);

} // Cudd::zddReadNodeCount


void
Cudd::AddHook(
  DD_HFP f,
  Cudd_HookType where) const
{
    int result = Cudd_AddHook(p->manager, f, where);
    checkReturnValue(result);

} // Cudd::AddHook


void
Cudd::RemoveHook(
  DD_HFP f,
  Cudd_HookType where) const
{
    int result = Cudd_RemoveHook(p->manager, f, where);
    checkReturnValue(result);

} // Cudd::RemoveHook


bool
Cudd::IsInHook(
  DD_HFP f,
  Cudd_HookType where) const
{
    return Cudd_IsInHook(p->manager, f, where);

} // Cudd::IsInHook


void
Cudd::EnableReorderingReporting() const
{
    int result = Cudd_EnableReorderingReporting(p->manager);
    checkReturnValue(result);

} // Cudd::EnableReorderingReporting


void
Cudd::DisableReorderingReporting() const
{
    int result = Cudd_DisableReorderingReporting(p->manager);
    checkReturnValue(result);

} // Cudd::DisableReorderingReporting


bool
Cudd::ReorderingReporting() const
{
    return Cudd_ReorderingReporting(p->manager);

} // Cudd::ReorderingReporting


int
Cudd::ReadErrorCode() const
{
    return Cudd_ReadErrorCode(p->manager);

} // Cudd::ReadErrorCode


void
Cudd::ClearErrorCode() const
{
    Cudd_ClearErrorCode(p->manager);

} // Cudd::ClearErrorCode


FILE *
Cudd::ReadStdout() const
{
    return Cudd_ReadStdout(p->manager);

} // Cudd::ReadStdout


void
Cudd::SetStdout(FILE *fp) const
{
    Cudd_SetStdout(p->manager, fp);

} // Cudd::SetStdout


FILE *
Cudd::ReadStderr() const
{
    return Cudd_ReadStderr(p->manager);

} // Cudd::ReadStderr


void
Cudd::SetStderr(FILE *fp) const
{
    Cudd_SetStderr(p->manager, fp);

} // Cudd::SetStderr


unsigned int
Cudd::ReadNextReordering() const
{
    return Cudd_ReadNextReordering(p->manager);

} // Cudd::ReadNextReordering


void
Cudd::SetNextReordering(
  unsigned int next) const
{
    Cudd_SetNextReordering(p->manager, next);

} // Cudd::SetNextReordering


double
Cudd::ReadSwapSteps() const
{
    return Cudd_ReadSwapSteps(p->manager);

} // Cudd::ReadSwapSteps


unsigned int
Cudd::ReadMaxLive() const
{
    return Cudd_ReadMaxLive(p->manager);

} // Cudd::ReadMaxLive


void
Cudd::SetMaxLive(unsigned int maxLive) const
{
    Cudd_SetMaxLive(p->manager, maxLive);

} // Cudd::SetMaxLive


unsigned long
Cudd::ReadMaxMemory() const
{
    return Cudd_ReadMaxMemory(p->manager);

} // Cudd::ReadMaxMemory


void
Cudd::SetMaxMemory(unsigned long maxMem) const
{
    Cudd_SetMaxMemory(p->manager, maxMem);

} // Cudd::SetMaxMemory


int
Cudd::bddBindVar(int index) const
{
    return Cudd_bddBindVar(p->manager, index);

} // Cudd::bddBindVar


int
Cudd::bddUnbindVar(int index) const
{
    return Cudd_bddUnbindVar(p->manager, index);

} // Cudd::bddUnbindVar


bool
Cudd::bddVarIsBound(int index) const
{
    return Cudd_bddVarIsBound(p->manager, index);

} // Cudd::bddVarIsBound


ADD
ADD::ExistAbstract(
  const ADD& cube) const
{
    DdManager *mgr = checkSameManager(cube);
    DdNode *result = Cudd_addExistAbstract(mgr, node, cube.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::ExistAbstract


ADD
ADD::UnivAbstract(
  const ADD& cube) const
{
    DdManager *mgr = checkSameManager(cube);
    DdNode *result = Cudd_addUnivAbstract(mgr, node, cube.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::UnivAbstract


ADD
ADD::OrAbstract(
  const ADD& cube) const
{
    DdManager *mgr = checkSameManager(cube);
    DdNode *result = Cudd_addOrAbstract(mgr, node, cube.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::OrAbstract


ADD
ADD::Plus(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addPlus, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Plus


ADD
ADD::Times(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addTimes, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Times


ADD
ADD::Threshold(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addThreshold, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Threshold


ADD
ADD::SetNZ(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addSetNZ, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::SetNZ


ADD
ADD::Divide(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addDivide, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Divide


ADD
ADD::Minus(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addMinus, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Minus


ADD
ADD::Minimum(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addMinimum, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Minimum


ADD
ADD::Maximum(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addMaximum, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Maximum


ADD
ADD::OneZeroMaximum(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addOneZeroMaximum, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::OneZeroMaximum


ADD
ADD::Diff(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addDiff, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Diff


ADD
ADD::Agreement(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addAgreement, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Agreement


ADD
ADD::Or(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addOr, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Or


ADD
ADD::Nand(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addNand, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Nand


ADD
ADD::Nor(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addNor, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Nor


ADD
ADD::Xor(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addXor, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Xor


ADD
ADD::Xnor(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addApply(mgr, Cudd_addXnor, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Xnor


ADD
ADD::Log() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addMonadicApply(mgr, Cudd_addLog, node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Log


ADD
ADD::FindMax() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addFindMax(mgr, node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::FindMax


ADD
ADD::FindMin() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addFindMin(mgr, node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::FindMin


ADD
ADD::IthBit(
  int bit) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addIthBit(mgr, node, bit);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::IthBit


ADD
ADD::ScalarInverse(
  const ADD& epsilon) const
{
    DdManager *mgr = checkSameManager(epsilon);
    DdNode *result = Cudd_addScalarInverse(mgr, node, epsilon.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::ScalarInverse


ADD
ADD::Ite(
  const ADD& g,
  const ADD& h) const
{
    DdManager *mgr = checkSameManager(g);
    checkSameManager(h);
    DdNode *result = Cudd_addIte(mgr, node, g.node, h.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Ite


ADD
ADD::IteConstant(
  const ADD& g,
  const ADD& h) const
{
    DdManager *mgr = checkSameManager(g);
    checkSameManager(h);
    DdNode *result = Cudd_addIteConstant(mgr, node, g.node, h.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::IteConstant


ADD
ADD::EvalConst(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addEvalConst(mgr, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::EvalConst


bool
ADD::Leq(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    return Cudd_addLeq(mgr, node, g.node);

} // ADD::Leq


ADD
ADD::Cmpl() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addCmpl(mgr, node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Cmpl


ADD
ADD::Negate() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addNegate(mgr, node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Negate


ADD
ADD::RoundOff(
  int N) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addRoundOff(mgr, node, N);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::RoundOff


ADD
Cudd::Walsh(
  vector<ADD> x,
  vector<ADD> y)
{
    int n = x.size();
    DdNode **X = new DdNode *[n];
    DdNode **Y = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	X[i] = x[i].getNode();
	Y[i] = y[i].getNode();
    }
    DdNode *result = Cudd_addWalsh(p->manager, X, Y, n);
    delete [] X;
    delete [] Y;
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Walsh


ADD
Cudd::addResidue(
  int n,
  int m,
  int options,
  int top)
{
    DdNode *result = Cudd_addResidue(p->manager, n, m, options, top);
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::addResidue


BDD
BDD::AndAbstract(
  const BDD& g,
  const BDD& cube,
  unsigned int limit) const
{
    DdManager *mgr = checkSameManager(g);
    checkSameManager(cube);
    DdNode *result;
    if (limit == 0)
	result = Cudd_bddAndAbstract(mgr, node, g.node, cube.node);
    else
	result = Cudd_bddAndAbstractLimit(mgr, node, g.node,
					  cube.node, limit);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::AndAbstract


int
Cudd::ApaNumberOfDigits(
  int binaryDigits) const
{
    return Cudd_ApaNumberOfDigits(binaryDigits);

} // Cudd::ApaNumberOfDigits


DdApaNumber
Cudd::NewApaNumber(
  int digits) const
{
    return Cudd_NewApaNumber(digits);

} // Cudd::NewApaNumber


void
Cudd::ApaCopy(
  int digits,
  DdApaNumber source,
  DdApaNumber dest) const
{
    Cudd_ApaCopy(digits, source, dest);

} // Cudd::ApaCopy


DdApaDigit
Cudd::ApaAdd(
  int digits,
  DdApaNumber a,
  DdApaNumber b,
  DdApaNumber sum) const
{
    return Cudd_ApaAdd(digits, a, b, sum);

} // Cudd::ApaAdd


DdApaDigit
Cudd::ApaSubtract(
  int digits,
  DdApaNumber a,
  DdApaNumber b,
  DdApaNumber diff) const
{
    return Cudd_ApaSubtract(digits, a, b, diff);

} // Cudd::ApaSubtract


DdApaDigit
Cudd::ApaShortDivision(
  int digits,
  DdApaNumber dividend,
  DdApaDigit divisor,
  DdApaNumber quotient) const
{
    return Cudd_ApaShortDivision(digits, dividend, divisor, quotient);

} // Cudd::ApaShortDivision


void
Cudd::ApaShiftRight(
  int digits,
  DdApaDigit in,
  DdApaNumber a,
  DdApaNumber b) const
{
    Cudd_ApaShiftRight(digits, in, a, b);

} // Cudd::ApaShiftRight


void
Cudd::ApaSetToLiteral(
  int digits,
  DdApaNumber number,
  DdApaDigit literal) const
{
    Cudd_ApaSetToLiteral(digits, number, literal);

} // Cudd::ApaSetToLiteral


void
Cudd::ApaPowerOfTwo(
  int digits,
  DdApaNumber number,
  int power) const
{
    Cudd_ApaPowerOfTwo(digits, number, power);

} // Cudd::ApaPowerOfTwo


void
Cudd::ApaPrintHex(
  FILE * fp,
  int digits,
  DdApaNumber number) const
{
    cout.flush();
    int result = Cudd_ApaPrintHex(fp, digits, number);
    checkReturnValue(result);

} // Cudd::ApaPrintHex


void
Cudd::ApaPrintDecimal(
  FILE * fp,
  int digits,
  DdApaNumber number) const
{
    cout.flush();
    int result = Cudd_ApaPrintDecimal(fp, digits, number);
    checkReturnValue(result);

} // Cudd::ApaPrintDecimal


DdApaNumber
ABDD::ApaCountMinterm(
  int nvars,
  int * digits) const
{
    DdManager *mgr = p->manager;
    return Cudd_ApaCountMinterm(mgr, node, nvars, digits);

} // ABDD::ApaCountMinterm


void
ABDD::ApaPrintMinterm(
  int nvars,
  FILE * fp) const
{
    cout.flush();
    DdManager *mgr = p->manager;
    int result = Cudd_ApaPrintMinterm(fp, mgr, node, nvars);
    checkReturnValue(result);

} // ABDD::ApaPrintMinterm


void
ABDD::EpdPrintMinterm(
  int nvars,
  FILE * fp) const
{
    EpDouble count;
    char str[24];
    cout.flush();
    DdManager *mgr = p->manager;
    int result = Cudd_EpdCountMinterm(mgr, node, nvars, &count);
    checkReturnValue(result,0);
    EpdGetString(&count, str);
    fprintf(fp, "%s\n", str);

} // ABDD::ApaPrintMinterm


BDD
BDD::UnderApprox(
  int numVars,
  int threshold,
  bool safe,
  double quality) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_UnderApprox(mgr, node, numVars, threshold, safe, quality);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::UnderApprox


BDD
BDD::OverApprox(
  int numVars,
  int threshold,
  bool safe,
  double quality) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_OverApprox(mgr, node, numVars, threshold, safe, quality);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::OverApprox


BDD
BDD::RemapUnderApprox(
  int numVars,
  int threshold,
  double quality) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_RemapUnderApprox(mgr, node, numVars, threshold, quality);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::RemapUnderApprox


BDD
BDD::RemapOverApprox(
  int numVars,
  int threshold,
  double quality) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_RemapOverApprox(mgr, node, numVars, threshold, quality);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::RemapOverApprox


BDD
BDD::BiasedUnderApprox(
  const BDD& bias,
  int numVars,
  int threshold,
  double quality1,
  double quality0) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_BiasedUnderApprox(mgr, node, bias.node, numVars, 
                                            threshold, quality1, quality0);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::BiasedUnderApprox


BDD
BDD::BiasedOverApprox(
  const BDD& bias,
  int numVars,
  int threshold,
  double quality1,
  double quality0) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_BiasedOverApprox(mgr, node, bias.node, numVars, 
                                           threshold, quality1, quality0);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::BiasedOverApprox


BDD
BDD::ExistAbstract(
  const BDD& cube,
  unsigned int limit) const
{
    DdManager *mgr = checkSameManager(cube);
    DdNode *result;
    if (limit == 0)
        result = Cudd_bddExistAbstract(mgr, node, cube.node);
    else
        result = Cudd_bddExistAbstractLimit(mgr, node, cube.node, limit);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::ExistAbstract


BDD
BDD::XorExistAbstract(
  const BDD& g,
  const BDD& cube) const
{
    DdManager *mgr = checkSameManager(g);
    checkSameManager(cube);
    DdNode *result = Cudd_bddXorExistAbstract(mgr, node, g.node, cube.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::XorExistAbstract


BDD
BDD::UnivAbstract(
  const BDD& cube) const
{
    DdManager *mgr = checkSameManager(cube);
    DdNode *result = Cudd_bddUnivAbstract(mgr, node, cube.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::UnivAbstract


BDD
BDD::BooleanDiff(
  int x) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_bddBooleanDiff(mgr, node, x);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::BooleanDiff


bool
BDD::VarIsDependent(
  const BDD& var) const
{
    DdManager *mgr = p->manager;
    return Cudd_bddVarIsDependent(mgr, node, var.node);

} // BDD::VarIsDependent


double
BDD::Correlation(
  const BDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    return Cudd_bddCorrelation(mgr, node, g.node);

} // BDD::Correlation


double
BDD::CorrelationWeights(
  const BDD& g,
  double * prob) const
{
    DdManager *mgr = checkSameManager(g);
    return Cudd_bddCorrelationWeights(mgr, node, g.node, prob);

} // BDD::CorrelationWeights


BDD
BDD::Ite(
  const BDD& g,
  const BDD& h,
  unsigned int limit) const
{
    DdManager *mgr = checkSameManager(g);
    checkSameManager(h);
    DdNode *result;
    if (limit == 0)
	result = Cudd_bddIte(mgr, node, g.node, h.node);
    else
	result = Cudd_bddIteLimit(mgr, node, g.node, h.node, limit);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Ite


BDD
BDD::IteConstant(
  const BDD& g,
  const BDD& h) const
{
    DdManager *mgr = checkSameManager(g);
    checkSameManager(h);
    DdNode *result = Cudd_bddIteConstant(mgr, node, g.node, h.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::IteConstant


BDD
BDD::Intersect(
  const BDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_bddIntersect(mgr, node, g.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Intersect


BDD
BDD::And(
  const BDD& g,
  unsigned int limit) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result;
    if (limit == 0)
	result = Cudd_bddAnd(mgr, node, g.node);
    else
	result = Cudd_bddAndLimit(mgr, node, g.node, limit);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::And


BDD
BDD::Or(
  const BDD& g,
  unsigned int limit) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result;
    if (limit == 0)
	result = Cudd_bddOr(mgr, node, g.node);
    else
	result = Cudd_bddOrLimit(mgr, node, g.node, limit);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Or


BDD
BDD::Nand(
  const BDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_bddNand(mgr, node, g.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Nand


BDD
BDD::Nor(
  const BDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_bddNor(mgr, node, g.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Nor


BDD
BDD::Xor(
  const BDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_bddXor(mgr, node, g.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Xor


BDD
BDD::Xnor(
  const BDD& g,
  unsigned int limit) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result;
    if (limit == 0)
	result = Cudd_bddXnor(mgr, node, g.node);
    else
	result = Cudd_bddXnorLimit(mgr, node, g.node, limit);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Xnor


bool
BDD::Leq(
  const BDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    return Cudd_bddLeq(mgr, node, g.node);

} // BDD::Leq


BDD
ADD::BddThreshold(
  CUDD_VALUE_TYPE value) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addBddThreshold(mgr, node, value);
    checkReturnValue(result);
    return BDD(p, result);

} // ADD::BddThreshold


BDD
ADD::BddStrictThreshold(
  CUDD_VALUE_TYPE value) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addBddStrictThreshold(mgr, node, value);
    checkReturnValue(result);
    return BDD(p, result);

} // ADD::BddStrictThreshold


BDD
ADD::BddInterval(
  CUDD_VALUE_TYPE lower,
  CUDD_VALUE_TYPE upper) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addBddInterval(mgr, node, lower, upper);
    checkReturnValue(result);
    return BDD(p, result);

} // ADD::BddInterval


BDD
ADD::BddIthBit(
  int bit) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addBddIthBit(mgr, node, bit);
    checkReturnValue(result);
    return BDD(p, result);

} // ADD::BddIthBit


ADD
BDD::Add() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_BddToAdd(mgr, node);
    checkReturnValue(result);
    return ADD(p, result);

} // BDD::Add


BDD
ADD::BddPattern() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addBddPattern(mgr, node);
    checkReturnValue(result);
    return BDD(p, result);

} // ADD::BddPattern


BDD
BDD::Transfer(
  Cudd& destination) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_bddTransfer(mgr, destination.p->manager, node);
    checkReturnValue(result);
    return BDD(destination.p, result);

} // BDD::Transfer


void
Cudd::DebugCheck()
{
    int result = Cudd_DebugCheck(p->manager);
    checkReturnValue(result == 0);

} // Cudd::DebugCheck


void
Cudd::CheckKeys()
{
    int result = Cudd_CheckKeys(p->manager);
    checkReturnValue(result == 0);

} // Cudd::CheckKeys


BDD
BDD::ClippingAnd(
  const BDD& g,
  int maxDepth,
  int direction) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_bddClippingAnd(mgr, node, g.node, maxDepth,
					 direction);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::ClippingAnd


BDD
BDD::ClippingAndAbstract(
  const BDD& g,
  const BDD& cube,
  int maxDepth,
  int direction) const
{
    DdManager *mgr = checkSameManager(g);
    checkSameManager(cube);
    DdNode *result = Cudd_bddClippingAndAbstract(mgr, node, g.node, cube.node,
						 maxDepth, direction);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::ClippingAndAbstract


ADD
ADD::Cofactor(
  const ADD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_Cofactor(mgr, node, g.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Cofactor


BDD
BDD::Cofactor(
  const BDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_Cofactor(mgr, node, g.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Cofactor


BDD
BDD::Compose(
  const BDD& g,
  int v) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_bddCompose(mgr, node, g.node, v);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Compose


ADD
ADD::Compose(
  const ADD& g,
  int v) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_addCompose(mgr, node, g.node, v);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Compose


ADD
ADD::Permute(
  int * permut) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_addPermute(mgr, node, permut);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Permute


ADD
ADD::SwapVariables(
  vector<ADD> x,
  vector<ADD> y) const
{
    int n = x.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[n];
    DdNode **Y = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	X[i] = x[i].node;
	Y[i] = y[i].node;
    }
    DdNode *result = Cudd_addSwapVariables(mgr, node, X, Y, n);
    delete [] X;
    delete [] Y;
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::SwapVariables


BDD
BDD::Permute(
  int * permut) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_bddPermute(mgr, node, permut);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Permute


BDD
BDD::SwapVariables(
  std::vector<BDD> x,
  std::vector<BDD> y) const
{
    int n = x.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[n];
    DdNode **Y = new DdNode *[n];
    for (int i = 0; i < n; i++) {
        X[i] = x[i].node;
        Y[i] = y[i].node;
    }
    DdNode *result = Cudd_bddSwapVariables(mgr, node, X, Y, n);
    delete [] X;
    delete [] Y;
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::SwapVariables


BDD
BDD::AdjPermuteX(
  vector<BDD> x) const
{
    int n = x.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	X[i] = x[i].node;
    }
    DdNode *result = Cudd_bddAdjPermuteX(mgr, node, X, n);
    delete [] X;
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::AdjPermuteX


ADD
ADD::VectorCompose(
  vector<ADD> vector) const
{
    DdManager *mgr = p->manager;
    int n = Cudd_ReadSize(mgr);
    DdNode **X = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	X[i] = vector[i].node;
    }
    DdNode *result = Cudd_addVectorCompose(mgr, node, X);
    delete [] X;
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::VectorCompose


ADD
ADD::NonSimCompose(
  vector<ADD> vector) const
{
    DdManager *mgr = p->manager;
    int n = Cudd_ReadSize(mgr);
    DdNode **X = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	X[i] = vector[i].node;
    }
    DdNode *result = Cudd_addNonSimCompose(mgr, node, X);
    delete [] X;
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::NonSimCompose


BDD
BDD::VectorCompose(
  vector<BDD> vector) const
{
    DdManager *mgr = p->manager;
    int n = Cudd_ReadSize(mgr);
    DdNode **X = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	X[i] = vector[i].node;
    }
    DdNode *result = Cudd_bddVectorCompose(mgr, node, X);
    delete [] X;
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::VectorCompose


void
BDD::ApproxConjDecomp(
  BDD* g,
  BDD* h) const
{
    DdManager *mgr = p->manager;
    DdNode **pieces;
    int result = Cudd_bddApproxConjDecomp(mgr, node, &pieces);
    checkReturnValue(result == 2);
    *g = BDD(p, pieces[0]);
    *h = BDD(p, pieces[1]);
    Cudd_RecursiveDeref(mgr,pieces[0]);
    Cudd_RecursiveDeref(mgr,pieces[1]);
    free(pieces);

} // BDD::ApproxConjDecomp


void
BDD::ApproxDisjDecomp(
  BDD* g,
  BDD* h) const
{
    DdManager *mgr = p->manager;
    DdNode **pieces;
    int result = Cudd_bddApproxDisjDecomp(mgr, node, &pieces);
    checkReturnValue(result == 2);
    *g = BDD(p, pieces[0]);
    *h = BDD(p, pieces[1]);
    Cudd_RecursiveDeref(mgr,pieces[0]);
    Cudd_RecursiveDeref(mgr,pieces[1]);
    free(pieces);

} // BDD::ApproxDisjDecomp


void
BDD::IterConjDecomp(
  BDD* g,
  BDD* h) const
{
    DdManager *mgr = p->manager;
    DdNode **pieces;
    int result = Cudd_bddIterConjDecomp(mgr, node, &pieces);
    checkReturnValue(result == 2);
    *g = BDD(p, pieces[0]);
    *h = BDD(p, pieces[1]);
    Cudd_RecursiveDeref(mgr,pieces[0]);
    Cudd_RecursiveDeref(mgr,pieces[1]);
    free(pieces);

} // BDD::IterConjDecomp


void
BDD::IterDisjDecomp(
  BDD* g,
  BDD* h) const
{
    DdManager *mgr = p->manager;
    DdNode **pieces;
    int result = Cudd_bddIterDisjDecomp(mgr, node, &pieces);
    checkReturnValue(result == 2);
    *g = BDD(p, pieces[0]);
    *h = BDD(p, pieces[1]);
    Cudd_RecursiveDeref(mgr,pieces[0]);
    Cudd_RecursiveDeref(mgr,pieces[1]);
    free(pieces);

} // BDD::IterDisjDecomp


void
BDD::GenConjDecomp(
  BDD* g,
  BDD* h) const
{
    DdManager *mgr = p->manager;
    DdNode **pieces;
    int result = Cudd_bddGenConjDecomp(mgr, node, &pieces);
    checkReturnValue(result == 2);
    *g = BDD(p, pieces[0]);
    *h = BDD(p, pieces[1]);
    Cudd_RecursiveDeref(mgr,pieces[0]);
    Cudd_RecursiveDeref(mgr,pieces[1]);
    free(pieces);

} // BDD::GenConjDecomp


void
BDD::GenDisjDecomp(
  BDD* g,
  BDD* h) const
{
    DdManager *mgr = p->manager;
    DdNode **pieces;
    int result = Cudd_bddGenDisjDecomp(mgr, node, &pieces);
    checkReturnValue(result == 2);
    *g = BDD(p, pieces[0]);
    *h = BDD(p, pieces[1]);
    Cudd_RecursiveDeref(mgr,pieces[0]);
    Cudd_RecursiveDeref(mgr,pieces[1]);
    free(pieces);

} // BDD::GenDisjDecomp


void
BDD::VarConjDecomp(
  BDD* g,
  BDD* h) const
{
    DdManager *mgr = p->manager;
    DdNode **pieces;
    int result = Cudd_bddVarConjDecomp(mgr, node, &pieces);
    checkReturnValue(result == 2);
    *g = BDD(p, pieces[0]);
    *h = BDD(p, pieces[1]);
    Cudd_RecursiveDeref(mgr,pieces[0]);
    Cudd_RecursiveDeref(mgr,pieces[1]);
    free(pieces);

} // BDD::VarConjDecomp


void
BDD::VarDisjDecomp(
  BDD* g,
  BDD* h) const
{
    DdManager *mgr = p->manager;
    DdNode **pieces;
    int result = Cudd_bddVarDisjDecomp(mgr, node, &pieces);
    checkReturnValue(result == 2);
    *g = BDD(p, pieces[0]);
    *h = BDD(p, pieces[1]);
    Cudd_RecursiveDeref(mgr,pieces[0]);
    Cudd_RecursiveDeref(mgr,pieces[1]);
    free(pieces);

} // BDD::VarDisjDecomp


bool
ABDD::IsCube() const
{
    DdManager *mgr = p->manager;
    return Cudd_CheckCube(mgr, node);

} // ABDD::IsCube


BDD
ABDD::FindEssential() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_FindEssential(mgr, node);
    checkReturnValue(result);
    return BDD(p, result);

} // ABDD::FindEssential


bool
BDD::IsVarEssential(
  int id,
  int phase) const
{
    DdManager *mgr = p->manager;
    return Cudd_bddIsVarEssential(mgr, node, id, phase);

} // BDD::IsVarEssential


void
ABDD::PrintTwoLiteralClauses(
  char **names,
  FILE *fp) const
{
    DdManager *mgr = p->manager;
    int result = Cudd_PrintTwoLiteralClauses(mgr, node, names, fp);
    checkReturnValue(result);

} // ABDD::PrintTwoLiteralClauses


void
Cudd::DumpBlif(
  const vector<BDD>& nodes,
  char ** inames,
  char ** onames,
  char * mname,
  FILE * fp,
  int mv) const
{
    DdManager *mgr = p->manager;
    int n = nodes.size();
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i ++) {
	F[i] = nodes[i].getNode();
    }
    int result = Cudd_DumpBlif(mgr, n, F, inames, onames, mname, fp, mv);
    delete [] F;
    checkReturnValue(result);

} // vector<BDD>::DumpBlif


void
Cudd::DumpDot(
  const vector<BDD>& nodes,
  char ** inames,
  char ** onames,
  FILE * fp) const
{
    DdManager *mgr = p->manager;
    int n = nodes.size();
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i ++) {
	F[i] = nodes[i].getNode();
    }
    int result = Cudd_DumpDot(mgr, n, F, inames, onames, fp);
    delete [] F;
    checkReturnValue(result);

} // vector<BDD>::DumpDot


void
Cudd::DumpDot(
  const vector<ADD>& nodes,
  char ** inames,
  char ** onames,
  FILE * fp) const
{
    DdManager *mgr = p->manager;
    int n = nodes.size();
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i ++) {
	F[i] = nodes[i].getNode();
    }
    int result = Cudd_DumpDot(mgr, n, F, inames, onames, fp);
    delete [] F;
    checkReturnValue(result);

} // vector<ADD>::DumpDot


void
Cudd::DumpDaVinci(
  const vector<BDD>& nodes,
  char ** inames,
  char ** onames,
  FILE * fp) const
{
    DdManager *mgr = p->manager;
    int n = nodes.size();
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i ++) {
	F[i] = nodes[i].getNode();
    }
    int result = Cudd_DumpDaVinci(mgr, n, F, inames, onames, fp);
    delete [] F;
    checkReturnValue(result);

} // vector<BDD>::DumpDaVinci


void
Cudd::DumpDaVinci(
  const vector<ADD>& nodes,
  char ** inames,
  char ** onames,
  FILE * fp) const
{
    DdManager *mgr = p->manager;
    int n = nodes.size();
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i ++) {
	F[i] = nodes[i].getNode();
    }
    int result = Cudd_DumpDaVinci(mgr, n, F, inames, onames, fp);
    delete [] F;
    checkReturnValue(result);

} // vector<ADD>::DumpDaVinci


void
Cudd::DumpDDcal(
  const vector<BDD>& nodes,
  char ** inames,
  char ** onames,
  FILE * fp) const
{
    DdManager *mgr = p->manager;
    int n = nodes.size();
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i ++) {
	F[i] = nodes[i].getNode();
    }
    int result = Cudd_DumpDDcal(mgr, n, F, inames, onames, fp);
    delete [] F;
    checkReturnValue(result);

} // vector<BDD>::DumpDDcal


void
Cudd::DumpFactoredForm(
  const vector<BDD>& nodes,
  char ** inames,
  char ** onames,
  FILE * fp) const
{
    DdManager *mgr = p->manager;
    int n = nodes.size();
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i ++) {
	F[i] = nodes[i].getNode();
    }
    int result = Cudd_DumpFactoredForm(mgr, n, F, inames, onames, fp);
    delete [] F;
    checkReturnValue(result);

} // vector<BDD>::DumpFactoredForm


BDD
BDD::Constrain(
  const BDD& c) const
{
    DdManager *mgr = checkSameManager(c);
    DdNode *result = Cudd_bddConstrain(mgr, node, c.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Constrain


BDD
BDD::Restrict(
  const BDD& c) const
{
    DdManager *mgr = checkSameManager(c);
    DdNode *result = Cudd_bddRestrict(mgr, node, c.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Restrict


BDD
BDD::NPAnd(
  const BDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_bddNPAnd(mgr, node, g.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::NPAnd


ADD
ADD::Constrain(
  const ADD& c) const
{
    DdManager *mgr = checkSameManager(c);
    DdNode *result = Cudd_addConstrain(mgr, node, c.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Constrain


vector<BDD>
BDD::ConstrainDecomp() const
{
    DdManager *mgr = p->manager;
    DdNode **result = Cudd_bddConstrainDecomp(mgr, node);
    checkReturnValue((DdNode *)result);
    int size = Cudd_ReadSize(mgr);
    vector<BDD> vect;
    for (int i = 0; i < size; i++) {
	Cudd_Deref(result[i]);
	vect.push_back(BDD(p, result[i]));
    }
    free(result);
    return vect;

} // BDD::ConstrainDecomp


ADD
ADD::Restrict(
  const ADD& c) const
{
    DdManager *mgr = checkSameManager(c);
    DdNode *result = Cudd_addRestrict(mgr, node, c.node);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Restrict


vector<BDD>
BDD::CharToVect() const
{
    DdManager *mgr = p->manager;
    DdNode **result = Cudd_bddCharToVect(mgr, node);
    checkReturnValue((DdNode *)result);
    int size = Cudd_ReadSize(mgr);
    vector<BDD> vect;
    for (int i = 0; i < size; i++) {
	Cudd_Deref(result[i]);
	vect.push_back(BDD(p, result[i]));
    }
    free(result);
    return vect;

} // BDD::CharToVect


BDD
BDD::LICompaction(
  const BDD& c) const
{
    DdManager *mgr = checkSameManager(c);
    DdNode *result = Cudd_bddLICompaction(mgr, node, c.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::LICompaction


BDD
BDD::Squeeze(
  const BDD& u) const
{
    DdManager *mgr = checkSameManager(u);
    DdNode *result = Cudd_bddSqueeze(mgr, node, u.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Squeeze


BDD
BDD::Minimize(
  const BDD& c) const
{
    DdManager *mgr = checkSameManager(c);
    DdNode *result = Cudd_bddMinimize(mgr, node, c.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Minimize


BDD
BDD::SubsetCompress(
  int nvars,
  int threshold) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_SubsetCompress(mgr, node, nvars, threshold);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::SubsetCompress


BDD
BDD::SupersetCompress(
  int nvars,
  int threshold) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_SupersetCompress(mgr, node, nvars, threshold);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::SupersetCompress


MtrNode *
Cudd::MakeTreeNode(
  unsigned int low,
  unsigned int size,
  unsigned int type) const
{
    return Cudd_MakeTreeNode(p->manager, low, size, type);

} // Cudd::MakeTreeNode


/* This is incorrect, but we'll wait for this one.
void
Cudd::Harwell(
  FILE * fp,
  DdManager * dd,
  ADD* E,
  ADD** x,
  ADD** y,
  ADD** xn,
  ADD** yn_,
  int * nx,
  int * ny,
  int * m,
  int * n,
  int bx,
  int sx,
  int by,
  int sy,
  int pr)
{
    DdManager *mgr = p->manager;
    int result = Cudd_addHarwell(fp, mgr, E, x, y, xn, yn_, nx, ny, m, n, bx, sx, by, sy, pr);
    checkReturnValue(result);

} // Cudd::Harwell
*/


void
Cudd::PrintLinear()
{
    cout.flush();
    int result = Cudd_PrintLinear(p->manager);
    checkReturnValue(result);

} // Cudd::PrintLinear


int
Cudd::ReadLinear(
  int x,
  int y)
{
    return Cudd_ReadLinear(p->manager, x, y);

} // Cudd::ReadLinear


BDD
BDD::LiteralSetIntersection(
  const BDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_bddLiteralSetIntersection(mgr, node, g.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::LiteralSetIntersection


ADD
ADD::MatrixMultiply(
  const ADD& B,
  vector<ADD> z) const
{
    int nz = z.size();
    DdManager *mgr = checkSameManager(B);
    DdNode **Z = new DdNode *[nz];
    for (int i = 0; i < nz; i++) {
	Z[i] = z[i].node;
    }
    DdNode *result = Cudd_addMatrixMultiply(mgr, node, B.node, Z, nz);
    delete [] Z;
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::MatrixMultiply


ADD
ADD::TimesPlus(
  const ADD& B,
  vector<ADD> z) const
{
    int nz = z.size();
    DdManager *mgr = checkSameManager(B);
    DdNode **Z = new DdNode *[nz];
    for (int i = 0; i < nz; i++) {
	Z[i] = z[i].node;
    }
    DdNode *result = Cudd_addTimesPlus(mgr, node, B.node, Z, nz);
    delete [] Z;
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::TimesPlus


ADD
ADD::Triangle(
  const ADD& g,
  vector<ADD> z) const
{
    int nz = z.size();
    DdManager *mgr = checkSameManager(g);
    DdNode **Z = new DdNode *[nz];
    for (int i = 0; i < nz; i++) {
	Z[i] = z[i].node;
    }
    DdNode *result = Cudd_addTriangle(mgr, node, g.node, Z, nz);
    delete [] Z;
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Triangle


BDD
BDD::PrioritySelect(
  vector<BDD> x,
  vector<BDD> y,
  vector<BDD> z,
  const BDD& Pi,
  DD_PRFP Pifunc) const
{
    int n = x.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[n];
    DdNode **Y = new DdNode *[n];
    DdNode **Z = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	X[i] = x[i].node;
	Y[i] = y[i].node;
	Z[i] = z[i].node;
    }
    DdNode *result = Cudd_PrioritySelect(mgr, node, X, Y, Z, Pi.node, n, Pifunc);
    delete [] X;
    delete [] Y;
    delete [] Z;
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::PrioritySelect


BDD
Cudd::Xgty(
  vector<BDD> z,
  vector<BDD> x,
  vector<BDD> y)
{
    int N = z.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[N];
    DdNode **Y = new DdNode *[N];
    DdNode **Z = new DdNode *[N];
    for (int i = 0; i < N; i++) {
	X[i] = x[i].getNode();
	Y[i] = y[i].getNode();
	Z[i] = z[i].getNode();
    }
    DdNode *result = Cudd_Xgty(mgr, N, Z, X, Y);
    delete [] X;
    delete [] Y;
    delete [] Z;
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::Xgty


BDD
Cudd::Xeqy(
  vector<BDD> x,
  vector<BDD> y)
{
    int N = x.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[N];
    DdNode **Y = new DdNode *[N];
    for (int i = 0; i < N; i++) {
	X[i] = x[i].getNode();
	Y[i] = y[i].getNode();
    }
    DdNode *result = Cudd_Xeqy(mgr, N, X, Y);
    delete [] X;
    delete [] Y;
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Xeqy


ADD
Cudd::Xeqy(
  vector<ADD> x,
  vector<ADD> y)
{
    int N = x.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[N];
    DdNode **Y = new DdNode *[N];
    for (int i = 0; i < N; i++) {
	X[i] = x[i].getNode();
	Y[i] = y[i].getNode();
    }
    DdNode *result = Cudd_addXeqy(mgr, N, X, X);
    delete [] X;
    delete [] Y;
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Xeqy


BDD
Cudd::Dxygtdxz(
  vector<BDD> x,
  vector<BDD> y,
  vector<BDD> z)
{
    int N = x.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[N];
    DdNode **Y = new DdNode *[N];
    DdNode **Z = new DdNode *[N];
    for (int i = 0; i < N; i++) {
	X[i] = x[i].getNode();
	Y[i] = y[i].getNode();
	Z[i] = z[i].getNode();
    }
    DdNode *result = Cudd_Dxygtdxz(mgr, N, X, Y, Z);
    delete [] X;
    delete [] Y;
    delete [] Z;
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::Dxygtdxz


BDD
Cudd::Dxygtdyz(
  vector<BDD> x,
  vector<BDD> y,
  vector<BDD> z)
{
    int N = x.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[N];
    DdNode **Y = new DdNode *[N];
    DdNode **Z = new DdNode *[N];
    for (int i = 0; i < N; i++) {
	X[i] = x[i].getNode();
	Y[i] = y[i].getNode();
	Z[i] = z[i].getNode();
    }
    DdNode *result = Cudd_Dxygtdyz(mgr, N, X, Y, Z);
    delete [] X;
    delete [] Y;
    delete [] Z;
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::Dxygtdyz


BDD
Cudd::Inequality(
  int c,
  vector<BDD> x,
  vector<BDD> y)
{
    int N = x.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[N];
    DdNode **Y = new DdNode *[N];
    for (int i = 0; i < N; i++) {
	X[i] = x[i].getNode();
	Y[i] = y[i].getNode();
    }
    DdNode *result = Cudd_Inequality(mgr, N, c, X, Y);
    delete [] X;
    delete [] Y;
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::Inequality


BDD
Cudd::Disequality(
  int c,
  vector<BDD> x,
  vector<BDD> y)
{
    int N = x.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[N];
    DdNode **Y = new DdNode *[N];
    for (int i = 0; i < N; i++) {
	X[i] = x[i].getNode();
	Y[i] = y[i].getNode();
    }
    DdNode *result = Cudd_Disequality(mgr, N, c, X, Y);
    delete [] X;
    delete [] Y;
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::Disequality


BDD
Cudd::Interval(
  vector<BDD> x,
  unsigned int lowerB,
  unsigned int upperB)
{
    int N = x.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[N];
    for (int i = 0; i < N; i++) {
	X[i] = x[i].getNode();
    }
    DdNode *result = Cudd_bddInterval(mgr, N, X, lowerB, upperB);
    delete [] X;
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::Interval


BDD
BDD::CProjection(
  const BDD& Y) const
{
    DdManager *mgr = checkSameManager(Y);
    DdNode *result = Cudd_CProjection(mgr, node, Y.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::CProjection


int
BDD::MinHammingDist(
  int *minterm,
  int upperBound) const
{
    DdManager *mgr = p->manager;
    int result = Cudd_MinHammingDist(mgr, node, minterm, upperBound);
    return result;

} // BDD::MinHammingDist


ADD
Cudd::Hamming(
  vector<ADD> xVars,
  vector<ADD> yVars)
{
    int nVars = xVars.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[nVars];
    DdNode **Y = new DdNode *[nVars];
    for (int i = 0; i < nVars; i++) {
	X[i] = xVars[i].getNode();
	Y[i] = yVars[i].getNode();
    }
    DdNode *result = Cudd_addHamming(mgr, X, Y, nVars);
    delete [] X;
    delete [] Y;
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::Hamming


/* We'll leave these two out for the time being.
void
Cudd::Read(
  FILE * fp,
  ADD* E,
  ADD** x,
  ADD** y,
  ADD** xn,
  ADD** yn_,
  int * nx,
  int * ny,
  int * m,
  int * n,
  int bx,
  int sx,
  int by,
  int sy)
{
    DdManager *mgr = p->manager;
    int result = Cudd_addRead(fp, mgr, E, x, y, xn, yn_, nx, ny, m, n, bx, sx, by, sy);
    checkReturnValue(result);

} // Cudd::Read


void
Cudd::Read(
  FILE * fp,
  BDD* E,
  BDD** x,
  BDD** y,
  int * nx,
  int * ny,
  int * m,
  int * n,
  int bx,
  int sx,
  int by,
  int sy)
{
    DdManager *mgr = p->manager;
    int result = Cudd_bddRead(fp, mgr, E, x, y, nx, ny, m, n, bx, sx, by, sy);
    checkReturnValue(result);

} // Cudd::Read
*/


void
Cudd::ReduceHeap(
  Cudd_ReorderingType heuristic,
  int minsize)
{
    int result = Cudd_ReduceHeap(p->manager, heuristic, minsize);
    checkReturnValue(result);

} // Cudd::ReduceHeap


void
Cudd::ShuffleHeap(
  int * permutation)
{
    int result = Cudd_ShuffleHeap(p->manager, permutation);
    checkReturnValue(result);

} // Cudd::ShuffleHeap


ADD
ADD::Eval(
  int * inputs) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_Eval(mgr, node, inputs);
    checkReturnValue(result);
    return ADD(p, result);

} // ADD::Eval


BDD
BDD::Eval(
  int * inputs) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_Eval(mgr, node, inputs);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Eval


BDD
ABDD::ShortestPath(
  int * weight,
  int * support,
  int * length) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_ShortestPath(mgr, node, weight, support, length);
    checkReturnValue(result);
    return BDD(p, result);

} // ABDD::ShortestPath


BDD
ABDD::LargestCube(
  int * length) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_LargestCube(mgr, node, length);
    checkReturnValue(result);
    return BDD(p, result);

} // ABDD::LargestCube


int
ABDD::ShortestLength(
  int * weight) const
{
    DdManager *mgr = p->manager;
    int result = Cudd_ShortestLength(mgr, node, weight);
    checkReturnValue(result != CUDD_OUT_OF_MEM);
    return result;

} // ABDD::ShortestLength


BDD
BDD::Decreasing(
  int i) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_Decreasing(mgr, node, i);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Decreasing


BDD
BDD::Increasing(
  int i) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_Increasing(mgr, node, i);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Increasing


bool
ABDD::EquivDC(
  const ABDD& G,
  const ABDD& D) const
{
    DdManager *mgr = checkSameManager(G);
    checkSameManager(D);
    return Cudd_EquivDC(mgr, node, G.node, D.node);

} // ABDD::EquivDC

bool
BDD::LeqUnless(
  const BDD& G,
  const BDD& D) const
{
    DdManager *mgr = checkSameManager(G);
    checkSameManager(D);
    int res = Cudd_bddLeqUnless(mgr, node, G.node, D.node);
    return res;

} // BDD::LeqUnless


bool
ADD::EqualSupNorm(
  const ADD& g,
  CUDD_VALUE_TYPE tolerance,
  int pr) const
{
    DdManager *mgr = checkSameManager(g);
    return Cudd_EqualSupNorm(mgr, node, g.node, tolerance, pr);

} // ADD::EqualSupNorm


BDD
BDD::MakePrime(
  const BDD& F) const
{
    DdManager *mgr = checkSameManager(F);
    if (!Cudd_CheckCube(mgr, node)) {
        p->errorHandler("Invalid argument.");
    }
    DdNode *result = Cudd_bddMakePrime(mgr, node, F.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD:MakePrime


BDD
BDD::MaximallyExpand(
  const BDD& ub,
  const BDD& f)
{
    DdManager *mgr = checkSameManager(ub);
    checkSameManager(f);
    DdNode *result = Cudd_bddMaximallyExpand(mgr, node, ub.node, f.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::MaximallyExpand


BDD
BDD::LargestPrimeUnate(
  const BDD& phases)
{
    DdManager *mgr = checkSameManager(phases);
    DdNode *result = Cudd_bddLargestPrimeUnate(mgr, node, phases.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::LargestPrimeUnate


double *
ABDD::CofMinterm() const
{
    DdManager *mgr = p->manager;
    double *result = Cudd_CofMinterm(mgr, node);
    checkReturnValue((DdNode *)result);
    return result;

} // ABDD::CofMinterm


BDD
BDD::SolveEqn(
  const BDD& Y,
  BDD* G,
  int ** yIndex,
  int n) const
{
    DdManager *mgr = checkSameManager(Y);
    DdNode **g = new DdNode *[n];
    DdNode *result = Cudd_SolveEqn(mgr, node, Y.node, g, yIndex, n);
    checkReturnValue(result);
    for (int i = 0; i < n; i++) {
	G[i] = BDD(p, g[i]);
	Cudd_RecursiveDeref(mgr,g[i]);
    }
    delete [] g;
    return BDD(p, result);

} // BDD::SolveEqn


BDD
BDD::VerifySol(
  BDD* G,
  int * yIndex,
  int n) const
{
    DdManager *mgr = p->manager;
    DdNode **g = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	g[i] = G[i].node;
    }
    DdNode *result = Cudd_VerifySol(mgr, node, g, yIndex, n);
    delete [] g;
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::VerifySol


BDD
BDD::SplitSet(
  vector<BDD> xVars,
  double m) const
{
    int n = xVars.size();
    DdManager *mgr = p->manager;
    DdNode **X = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	X[i] = xVars[i].node;
    }
    DdNode *result = Cudd_SplitSet(mgr, node, X, n, m);
    delete [] X;
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::SplitSet


BDD
BDD::SubsetHeavyBranch(
  int numVars,
  int threshold) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_SubsetHeavyBranch(mgr, node, numVars, threshold);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::SubsetHeavyBranch


BDD
BDD::SupersetHeavyBranch(
  int numVars,
  int threshold) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_SupersetHeavyBranch(mgr, node, numVars, threshold);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::SupersetHeavyBranch


BDD
BDD::SubsetShortPaths(
  int numVars,
  int threshold,
  bool hardlimit) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_SubsetShortPaths(mgr, node, numVars, threshold, hardlimit);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::SubsetShortPaths


BDD
BDD::SupersetShortPaths(
  int numVars,
  int threshold,
  bool hardlimit) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_SupersetShortPaths(mgr, node, numVars, threshold, hardlimit);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::SupersetShortPaths


void
Cudd::SymmProfile(
  int lower,
  int upper) const
{
    Cudd_SymmProfile(p->manager, lower, upper);

} // Cudd::SymmProfile


unsigned int
Cudd::Prime(
  unsigned int pr) const
{
    return Cudd_Prime(pr);

} // Cudd::Prime


void
Cudd::Reserve(
  int amount) const
{
    int result = Cudd_Reserve(p->manager, amount);
    checkReturnValue(result);

} // Cudd::Reserve


void
ABDD::PrintMinterm() const
{
    cout.flush();
    DdManager *mgr = p->manager;
    int result = Cudd_PrintMinterm(mgr, node);
    checkReturnValue(result);

} // ABDD::PrintMinterm


void
BDD::PrintCover() const
{
    cout.flush();
    DdManager *mgr = p->manager;
    int result = Cudd_bddPrintCover(mgr, node, node);
    checkReturnValue(result);

} // BDD::PrintCover


void
BDD::PrintCover(
  const BDD& u) const
{
    checkSameManager(u);
    cout.flush();
    DdManager *mgr = p->manager;
    int result = Cudd_bddPrintCover(mgr, node, u.node);
    checkReturnValue(result);

} // BDD::PrintCover


int
BDD::EstimateCofactor(
  int i,
  int phase) const
{
    DdManager *mgr = p->manager;
    int result = Cudd_EstimateCofactor(mgr, node, i, phase);
    checkReturnValue(result != CUDD_OUT_OF_MEM);
    return result;

} // BDD::EstimateCofactor


int
BDD::EstimateCofactorSimple(
  int i) const
{
    int result = Cudd_EstimateCofactorSimple(node, i);
    return result;

} // BDD::EstimateCofactorSimple


int
Cudd::SharingSize(
  DD* nodes,
  int n) const
{
    DdNode **nodeArray = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	nodeArray[i] = nodes[i].getNode();
    }
    int result = Cudd_SharingSize(nodeArray, n);
    delete [] nodeArray;
    checkReturnValue(n == 0 || result > 0);
    return result;

} // Cudd::SharingSize


int
Cudd::SharingSize(
  const vector<BDD>& v) const
{
    vector<BDD>::size_type n = v.size();
    DdNode **nodeArray = new DdNode *[n];
    for (vector<BDD>::size_type i = 0; i != n; ++i) {
	nodeArray[i] = v[i].getNode();
    }
    int result = Cudd_SharingSize(nodeArray, n);
    delete [] nodeArray;
    checkReturnValue(n == 0 || result > 0);
    return result;

} // Cudd::SharingSize


double
ABDD::CountMinterm(
  int nvars) const
{
    DdManager *mgr = p->manager;
    double result = Cudd_CountMinterm(mgr, node, nvars);
    checkReturnValue(result != (double) CUDD_OUT_OF_MEM);
    return result;

} // ABDD::CountMinterm


double
ABDD::CountPath() const
{
    double result = Cudd_CountPath(node);
    checkReturnValue(result != (double) CUDD_OUT_OF_MEM);
    return result;

} // ABDD::CountPath


BDD
ABDD::Support() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_Support(mgr, node);
    checkReturnValue(result);
    return BDD(p, result);

} // ABDD::Support


int
ABDD::SupportSize() const
{
    DdManager *mgr = p->manager;
    int result = Cudd_SupportSize(mgr, node);
    checkReturnValue(result != CUDD_OUT_OF_MEM);
    return result;

} // ABDD::SupportSize


BDD
Cudd::VectorSupport(const vector<BDD>& roots) const
{
    int n = roots.size();
    DdManager *mgr = p->manager;
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	F[i] = roots[i].getNode();
    }
    DdNode *result = Cudd_VectorSupport(mgr, F, n);
    delete [] F;
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::VectorSupport


vector<unsigned int>
ABDD::SupportIndices() const
{
    unsigned int *support;
    DdManager *mgr = p->manager;
    int size = Cudd_SupportIndices(mgr, node, (int **)&support);
    checkReturnValue(size >= 0);
    // size could be 0, in which case support is 0 too!
    vector<unsigned int> indices(support, support+size);
    if (support) free(support);
    return indices;

} // ABDD::SupportIndices


vector<unsigned int>
Cudd::SupportIndices(const vector<ABDD>& roots) const
{
    unsigned int *support;
    int n = roots.size();
    DdManager *mgr = p->manager;
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	F[i] = roots[i].getNode();
    }
    int size = Cudd_VectorSupportIndices(mgr, F, n, (int **)&support);
    delete [] F;
    checkReturnValue(size >= 0);
    // size could be 0, in which case support is 0 too!
    vector<unsigned int> indices(support, support+size);
    if (support) free(support);
    return indices;

} // Cudd::SupportIndices


int
Cudd::nodeCount(const vector<BDD>& roots) const
{
    int n = roots.size();
    DdNode **nodeArray = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	nodeArray[i] = roots[i].getNode();
    }
    int result = Cudd_SharingSize(nodeArray, n);
    delete [] nodeArray;
    checkReturnValue(result > 0);
    return result;

} // vector<BDD>::nodeCount


BDD
Cudd::VectorSupport(const vector<ADD>& roots) const
{
    int n = roots.size();
    DdManager *mgr = p->manager;
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	F[i] = roots[i].getNode();
    }
    DdNode *result = Cudd_VectorSupport(mgr, F, n);
    delete [] F;
    checkReturnValue(result);
    return BDD(p, result);

} // vector<ADD>::VectorSupport


int
Cudd::VectorSupportSize(const vector<BDD>& roots) const
{
    int n = roots.size();
    DdManager *mgr = p->manager;
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	F[i] = roots[i].getNode();
    }
    int result = Cudd_VectorSupportSize(mgr, F, n);
    delete [] F;
    checkReturnValue(result != CUDD_OUT_OF_MEM);
    return result;

} // vector<BDD>::VectorSupportSize


int
Cudd::VectorSupportSize(const vector<ADD>& roots) const
{
    int n = roots.size();
    DdManager *mgr = p->manager;
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	F[i] = roots[i].getNode();
    }
    int result = Cudd_VectorSupportSize(mgr, F, n);
    delete [] F;
    checkReturnValue(result != CUDD_OUT_OF_MEM);
    return result;

} // vector<ADD>::VectorSupportSize


void
ABDD::ClassifySupport(
  const ABDD& g,
  BDD* common,
  BDD* onlyF,
  BDD* onlyG) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *C, *F, *G;
    int result = Cudd_ClassifySupport(mgr, node, g.node, &C, &F, &G);
    checkReturnValue(result);
    *common = BDD(p, C);
    *onlyF = BDD(p, F);
    *onlyG = BDD(p, G);

} // ABDD::ClassifySupport


int
ABDD::CountLeaves() const
{
    return Cudd_CountLeaves(node);

} // ABDD::CountLeaves


void
BDD::PickOneCube(
  char * string) const
{
    DdManager *mgr = p->manager;
    int result = Cudd_bddPickOneCube(mgr, node, string);
    checkReturnValue(result);

} // BDD::PickOneCube


BDD
BDD::PickOneMinterm(
  vector<BDD> vars) const
{
    int n = vars.size();
    DdManager *mgr = p->manager;
    DdNode **V = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	V[i] = vars[i].node;
    }
    DdNode *result = Cudd_bddPickOneMinterm(mgr, node, V, n);
    delete [] V;
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::PickOneMinterm


DdGen *
ABDD::FirstCube(
  int ** cube,
  CUDD_VALUE_TYPE * value) const
{
    DdManager *mgr = p->manager;
    DdGen *result = Cudd_FirstCube(mgr, node, cube, value);
    checkReturnValue((DdNode *)result);
    return result;

} // ABDD::FirstCube


int
NextCube(
  DdGen * gen,
  int ** cube,
  CUDD_VALUE_TYPE * value)
{
    return Cudd_NextCube(gen, cube, value);

} // NextCube


BDD
Cudd::bddComputeCube(
  BDD * vars,
  int * phase,
  int n) const
{
    DdManager *mgr = p->manager;
    DdNode **V = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	V[i] = vars[i].getNode();
    }
    DdNode *result = Cudd_bddComputeCube(mgr, V, phase, n);
    delete [] V;
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::bddComputeCube


ADD
Cudd::addComputeCube(
  ADD * vars,
  int * phase,
  int n)
{
    DdManager *mgr = p->manager;
    DdNode **V = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	V[i] = vars[i].getNode();
    }
    DdNode *result = Cudd_addComputeCube(mgr, V, phase, n);
    delete [] V;
    checkReturnValue(result);
    return ADD(p, result);

} // Cudd::addComputeCube


DdGen *
BDD::FirstNode(
  BDD* fnode) const
{
    DdManager *mgr = p->manager;
    DdNode *Fn;
    DdGen *result = Cudd_FirstNode(mgr, node, &Fn);
    checkReturnValue((DdNode *)result);
    *fnode = BDD(p, Fn);
    return result;

} // DD::FirstNode


int
Cudd::NextNode(
  DdGen * gen,
  BDD * nnode)
{
    DdNode *nn;
    int result = Cudd_NextNode(gen, &nn);
    *nnode = BDD(p, nn);
    return result;

} // Cudd::NextNode


int
GenFree(
  DdGen * gen)
{
    return Cudd_GenFree(gen);

} // GenFree


int
IsGenEmpty(
  DdGen * gen)
{
    return Cudd_IsGenEmpty(gen);

} // IsGenEmpty


BDD
Cudd::IndicesToCube(
  int * array,
  int n)
{
    DdNode *result = Cudd_IndicesToCube(p->manager, array, n);
    checkReturnValue(result);
    return BDD(p, result);

} // Cudd::IndicesToCube


void
Cudd::PrintVersion(
  FILE * fp) const
{
    cout.flush();
    Cudd_PrintVersion(fp);

} // Cudd::PrintVersion


double
Cudd::AverageDistance() const
{
    return Cudd_AverageDistance(p->manager);

} // Cudd::AverageDistance


long
Cudd::Random() const
{
    return Cudd_Random();

} // Cudd::Random


void
Cudd::Srandom(
  long seed) const
{
    Cudd_Srandom(seed);

} // Cudd::Srandom


double
ABDD::Density(
  int nvars) const
{
    DdManager *mgr = p->manager;
    double result = Cudd_Density(mgr, node, nvars);
    checkReturnValue(result != (double) CUDD_OUT_OF_MEM);
    return result;

} // ABDD::Density


int
ZDD::Count() const
{
    DdManager *mgr = p->manager;
    int result = Cudd_zddCount(mgr, node);
    checkReturnValue(result != CUDD_OUT_OF_MEM);
    return result;

} // ZDD::Count


double
ZDD::CountDouble() const
{
    DdManager *mgr = p->manager;
    double result = Cudd_zddCountDouble(mgr, node);
    checkReturnValue(result != (double) CUDD_OUT_OF_MEM);
    return result;

} // ZDD::CountDouble


ZDD
ZDD::Product(
  const ZDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_zddProduct(mgr, node, g.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::Product


ZDD
ZDD::UnateProduct(
  const ZDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_zddUnateProduct(mgr, node, g.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::UnateProduct


ZDD
ZDD::WeakDiv(
  const ZDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_zddWeakDiv(mgr, node, g.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::WeakDiv


ZDD
ZDD::Divide(
  const ZDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_zddDivide(mgr, node, g.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::Divide


ZDD
ZDD::WeakDivF(
  const ZDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_zddWeakDivF(mgr, node, g.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::WeakDivF


ZDD
ZDD::DivideF(
  const ZDD& g) const
{
    DdManager *mgr = checkSameManager(g);
    DdNode *result = Cudd_zddDivideF(mgr, node, g.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::DivideF


MtrNode *
Cudd::MakeZddTreeNode(
  unsigned int low,
  unsigned int size,
  unsigned int type)
{
    return Cudd_MakeZddTreeNode(p->manager, low, size, type);

} // Cudd::MakeZddTreeNode


BDD
BDD::zddIsop(
  const BDD& U,
  ZDD* zdd_I) const
{
    DdManager *mgr = checkSameManager(U);
    DdNode *Z;
    DdNode *result = Cudd_zddIsop(mgr, node, U.node, &Z);
    checkReturnValue(result);
    *zdd_I = ZDD(p, Z);
    return BDD(p, result);

} // BDD::Isop


BDD
BDD::Isop(
  const BDD& U) const
{
    DdManager *mgr = checkSameManager(U);
    DdNode *result = Cudd_bddIsop(mgr, node, U.node);
    checkReturnValue(result);
    return BDD(p, result);

} // BDD::Isop


double
ZDD::CountMinterm(
  int path) const
{
    DdManager *mgr = p->manager;
    double result = Cudd_zddCountMinterm(mgr, node, path);
    checkReturnValue(result != (double) CUDD_OUT_OF_MEM);
    return result;

} // ZDD::CountMinterm


void
Cudd::zddPrintSubtable() const
{
    cout.flush();
    Cudd_zddPrintSubtable(p->manager);

} // Cudd::zddPrintSubtable


ZDD
BDD::PortToZdd() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_zddPortFromBdd(mgr, node);
    checkReturnValue(result);
    return ZDD(p, result);

} // BDD::PortToZdd


BDD
ZDD::PortToBdd() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_zddPortToBdd(mgr, node);
    checkReturnValue(result);
    return BDD(p, result);

} // ZDD::PortToBdd


void
Cudd::zddReduceHeap(
  Cudd_ReorderingType heuristic,
  int minsize)
{
    int result = Cudd_zddReduceHeap(p->manager, heuristic, minsize);
    checkReturnValue(result);

} // Cudd::zddReduceHeap


void
Cudd::zddShuffleHeap(
  int * permutation)
{
    int result = Cudd_zddShuffleHeap(p->manager, permutation);
    checkReturnValue(result);

} // Cudd::zddShuffleHeap


ZDD
ZDD::Ite(
  const ZDD& g,
  const ZDD& h) const
{
    DdManager *mgr = checkSameManager(g);
    checkSameManager(h);
    DdNode *result = Cudd_zddIte(mgr, node, g.node, h.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::Ite


ZDD
ZDD::Union(
  const ZDD& Q) const
{
    DdManager *mgr = checkSameManager(Q);
    DdNode *result = Cudd_zddUnion(mgr, node, Q.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::Union


ZDD
ZDD::Intersect(
  const ZDD& Q) const
{
    DdManager *mgr = checkSameManager(Q);
    DdNode *result = Cudd_zddIntersect(mgr, node, Q.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::Intersect


ZDD
ZDD::Diff(
  const ZDD& Q) const
{
    DdManager *mgr = checkSameManager(Q);
    DdNode *result = Cudd_zddDiff(mgr, node, Q.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::Diff


ZDD
ZDD::DiffConst(
  const ZDD& Q) const
{
    DdManager *mgr = checkSameManager(Q);
    DdNode *result = Cudd_zddDiffConst(mgr, node, Q.node);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::DiffConst


ZDD
ZDD::Subset1(
  int var) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_zddSubset1(mgr, node, var);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::Subset1


ZDD
ZDD::Subset0(
  int var) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_zddSubset0(mgr, node, var);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::Subset0


ZDD
ZDD::Change(
  int var) const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_zddChange(mgr, node, var);
    checkReturnValue(result);
    return ZDD(p, result);

} // ZDD::Change


void
Cudd::zddSymmProfile(
  int lower,
  int upper) const
{
    Cudd_zddSymmProfile(p->manager, lower, upper);

} // Cudd::zddSymmProfile


void
ZDD::PrintMinterm() const
{
    cout.flush();
    DdManager *mgr = p->manager;
    int result = Cudd_zddPrintMinterm(mgr, node);
    checkReturnValue(result);

} // ZDD::PrintMinterm


void
ZDD::PrintCover() const
{
    cout.flush();
    DdManager *mgr = p->manager;
    int result = Cudd_zddPrintCover(mgr, node);
    checkReturnValue(result);

} // ZDD::PrintCover


BDD
ZDD::Support() const
{
    DdManager *mgr = p->manager;
    DdNode *result = Cudd_zddSupport(mgr, node);
    checkReturnValue(result);
    return BDD(p, result);

} // ZDD::Support


void
Cudd::DumpDot(
  const vector<ZDD>& nodes,
  char ** inames,
  char ** onames,
  FILE * fp) const
{
    DdManager *mgr = p->manager;
    int n = nodes.size();
    DdNode **F = new DdNode *[n];
    for (int i = 0; i < n; i++) {
	F[i] = nodes[i].getNode();
    }
    int result = Cudd_zddDumpDot(mgr, n, F, inames, onames, fp);
    delete [] F;
    checkReturnValue(result);

} // vector<ZDD>::DumpDot
