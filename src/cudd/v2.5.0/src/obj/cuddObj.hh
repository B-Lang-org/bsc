/**CHeaderFile***************************************************************

  FileName    [cuddObj.hh]

  PackageName [cudd]

  Synopsis    [Class definitions for C++ object-oriented encapsulation of
  CUDD.]

  Description [Class definitions for C++ object-oriented encapsulation of
  CUDD.]

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

  Revision    [$Id: cuddObj.hh,v 1.13 2012/02/05 01:06:40 fabio Exp fabio $]

******************************************************************************/

#ifndef _CPPCUDD
#define _CPPCUDD

#if defined (__GNUC__)
#if (__GNUC__ >2 || __GNUC_MINOR__ >=7) && !defined(UNUSED)
#define UNUSED __attribute__ ((unused))
#else
#define UNUSED
#endif
#else
#define UNUSED
#endif

/*---------------------------------------------------------------------------*/
/* Nested includes                                                           */
/*---------------------------------------------------------------------------*/

#include <cstdio>
#include <string>
#include <vector>
#include "cudd.h"

/*---------------------------------------------------------------------------*/
/* Type definitions                                                          */
/*---------------------------------------------------------------------------*/
class BDD;
class ADD;
class ZDD;
class Cudd;

typedef void (*PFC)(std::string);	// handler function type

/*---------------------------------------------------------------------------*/
/* Class definitions                                                         */
/*---------------------------------------------------------------------------*/

/**Class***********************************************************************

  Synopsis     [Class for reference counting of CUDD managers.]

  Description  []

  SeeAlso      [Cudd DD ABDD ADD BDD ZDD]

******************************************************************************/
class Capsule {
    friend class DD;
    friend class ABDD;
    friend class BDD;
    friend class ADD;
    friend class ZDD;
    friend class Cudd;
private:
    DdManager *manager;
    PFC errorHandler;
    PFC timeoutHandler;
    bool verbose;
    int ref;
};


/**Class***********************************************************************

  Synopsis     [Base class for all decision diagrams in CUDD.]

  Description  []

  SeeAlso      [Cudd ABDD ADD BDD ZDD]

******************************************************************************/
class DD {
    friend class ABDD;
    friend class BDD;
    friend class ADD;
    friend class ZDD;
private:
    Capsule *p;
    DdNode *node;
    inline DdManager * checkSameManager(const DD &other) const;
    inline void checkReturnValue(const DdNode *result) const;
    inline void checkReturnValue(const int result, const int expected = 1)
	const;
public:
    DD();
    DD(Capsule *cap, DdNode *ddNode);
    DD(Cudd const & manager, DdNode *ddNode);
    DD(const DD &from);
    virtual ~DD();
    operator bool() const { return node; }
    DdManager *manager() const;
    DdNode * getNode() const;
    DdNode * getRegularNode() const;
    int nodeCount() const;
    unsigned int NodeReadIndex() const;

}; // DD


/**Class***********************************************************************

  Synopsis     [Class for ADDs and BDDs.]

  Description  []

  SeeAlso      [Cudd ADD BDD]

******************************************************************************/
class ABDD : public DD {
    friend class BDD;
    friend class ADD;
    friend class Cudd;
public:
    ABDD();
    ABDD(Capsule *cap, DdNode *bddNode);
    ABDD(Cudd const & manager, DdNode *ddNode);
    ABDD(const ABDD &from);
    virtual ~ABDD();
    bool operator==(const ABDD &other) const;
    bool operator!=(const ABDD &other) const;
    void print(int nvars, int verbosity = 1) const;
    DdApaNumber ApaCountMinterm(int nvars, int * digits) const;
    void ApaPrintMinterm(int nvars, FILE * fp = stdout) const;
    void EpdPrintMinterm(int nvars, FILE * fp = stdout) const;
    bool IsOne() const;
    bool IsCube() const;
    BDD FindEssential() const;
    void PrintTwoLiteralClauses(char ** names, FILE * fp = stdout) const;
    BDD ShortestPath(int * weight, int * support, int * length) const;
    BDD LargestCube(int * length = 0) const;
    int ShortestLength(int * weight) const;
    bool EquivDC(const ABDD& G, const ABDD& D) const;
    double * CofMinterm() const;
    void PrintMinterm() const;
    double CountMinterm(int nvars) const;
    double CountPath() const;
    BDD Support() const;
    int SupportSize() const;
    std::vector<unsigned int> SupportIndices() const;
    void ClassifySupport(const ABDD& g, BDD* common, BDD* onlyF, BDD* onlyG)
	const;
    int CountLeaves() const;
    DdGen * FirstCube(int ** cube, CUDD_VALUE_TYPE * value) const;
    double Density(int nvars) const;

}; // ABDD


/**Class***********************************************************************

  Synopsis     [Class for BDDs.]

  Description  []

  SeeAlso      [Cudd]

******************************************************************************/
class BDD : public ABDD {
    friend class Cudd;
public:
    BDD();
    BDD(Capsule *cap, DdNode *bddNode);
    BDD(Cudd const & manager, DdNode *ddNode);
    BDD(const BDD &from);
    BDD operator=(const BDD& right);
    bool operator<=(const BDD& other) const;
    bool operator>=(const BDD& other) const;
    bool operator<(const BDD& other) const;
    bool operator>(const BDD& other) const;
    BDD operator!() const;
    BDD operator~() const;
    BDD operator*(const BDD& other) const;
    BDD operator*=(const BDD& other);
    BDD operator&(const BDD& other) const;
    BDD operator&=(const BDD& other);
    BDD operator+(const BDD& other) const;
    BDD operator+=(const BDD& other);
    BDD operator|(const BDD& other) const;
    BDD operator|=(const BDD& other);
    BDD operator^(const BDD& other) const;
    BDD operator^=(const BDD& other);
    BDD operator-(const BDD& other) const;
    BDD operator-=(const BDD& other);
    bool IsZero() const;
    BDD AndAbstract(const BDD& g, const BDD& cube, unsigned int limit = 0)
	const;
    BDD UnderApprox(
      int numVars,
      int threshold = 0,
      bool safe = false,
      double quality = 1.0) const;
    BDD OverApprox(
      int numVars,
      int threshold = 0,
      bool safe = false,
      double quality = 1.0) const;
    BDD RemapUnderApprox(int numVars, int threshold = 0, double quality = 1.0)
	const;
    BDD RemapOverApprox(int numVars, int threshold = 0, double quality = 1.0)
	const;
    BDD BiasedUnderApprox(const BDD& bias, int numVars, int threshold = 0, 
                          double quality1 = 1.0, double quality0 = 1.0) const;
    BDD BiasedOverApprox(const BDD& bias, int numVars, int threshold = 0, 
                         double quality1 = 1.0, double quality0 = 1.0) const;
    BDD ExistAbstract(const BDD& cube, unsigned int limit = 0) const;
    BDD XorExistAbstract(const BDD& g, const BDD& cube) const;
    BDD UnivAbstract(const BDD& cube) const;
    BDD BooleanDiff(int x) const;
    bool VarIsDependent(const BDD& var) const;
    double Correlation(const BDD& g) const;
    double CorrelationWeights(const BDD& g, double * prob) const;
    BDD Ite(const BDD& g, const BDD& h, unsigned int limit = 0) const;
    BDD IteConstant(const BDD& g, const BDD& h) const;
    BDD Intersect(const BDD& g) const;
    BDD And(const BDD& g, unsigned int limit = 0) const;
    BDD Or(const BDD& g, unsigned int limit = 0) const;
    BDD Nand(const BDD& g) const;
    BDD Nor(const BDD& g) const;
    BDD Xor(const BDD& g) const;
    BDD Xnor(const BDD& g, unsigned int limit = 0) const;
    bool Leq(const BDD& g) const;
    ADD Add() const;
    BDD Transfer(Cudd& destination) const;
    BDD ClippingAnd(const BDD& g, int maxDepth, int direction) const;
    BDD ClippingAndAbstract(const BDD& g, const BDD& cube, int maxDepth,
			    int direction) const;
    BDD Cofactor(const BDD& g) const;
    BDD Compose(const BDD& g, int v) const;
    BDD Permute(int * permut) const;
    BDD SwapVariables(std::vector<BDD> x, std::vector<BDD> y) const;
    BDD AdjPermuteX(std::vector<BDD> x) const;
    BDD VectorCompose(std::vector<BDD> vector) const;
    void ApproxConjDecomp(BDD* g, BDD* h) const;
    void ApproxDisjDecomp(BDD* g, BDD* h) const;
    void IterConjDecomp(BDD* g, BDD* h) const;
    void IterDisjDecomp(BDD* g, BDD* h) const;
    void GenConjDecomp(BDD* g, BDD* h) const;
    void GenDisjDecomp(BDD* g, BDD* h) const;
    void VarConjDecomp(BDD* g, BDD* h) const;
    void VarDisjDecomp(BDD* g, BDD* h) const;
    bool IsVarEssential(int id, int phase) const;
    BDD Constrain(const BDD& c) const;
    BDD Restrict(const BDD& c) const;
    BDD NPAnd(const BDD& g) const;
    std::vector<BDD> ConstrainDecomp() const;
    std::vector<BDD> CharToVect() const;
    BDD LICompaction(const BDD& c) const;
    BDD Squeeze(const BDD& u) const;
    BDD Minimize(const BDD& c) const;
    BDD SubsetCompress(int nvars, int threshold) const;
    BDD SupersetCompress(int nvars, int threshold) const;
    BDD LiteralSetIntersection(const BDD& g) const;
    BDD PrioritySelect(std::vector<BDD> x, std::vector<BDD> y,
		       std::vector<BDD> z, const BDD& Pi, DD_PRFP Pifunc) const;
    BDD CProjection(const BDD& Y) const;
    int MinHammingDist(int *minterm, int upperBound) const;
    BDD Eval(int * inputs) const;
    BDD Decreasing(int i) const;
    BDD Increasing(int i) const;
    bool LeqUnless(const BDD& G, const BDD& D) const;
    BDD MakePrime(const BDD& F) const;
    BDD MaximallyExpand(const BDD& ub, const BDD& f);
    BDD LargestPrimeUnate(const BDD& phases);
    BDD SolveEqn(const BDD& Y, BDD* G, int ** yIndex, int n) const;
    BDD VerifySol(BDD* G, int * yIndex, int n) const;
    BDD SplitSet(std::vector<BDD> xVars, double m) const;
    BDD SubsetHeavyBranch(int numVars, int threshold) const;
    BDD SupersetHeavyBranch(int numVars, int threshold) const;
    BDD SubsetShortPaths(int numVars, int threshold, bool hardlimit = false) const;
    BDD SupersetShortPaths(int numVars, int threshold, bool hardlimit = false) const;
    void PrintCover() const;
    void PrintCover(const BDD& u) const;
    int EstimateCofactor(int i, int phase) const;
    int EstimateCofactorSimple(int i) const;
    void PickOneCube(char * string) const;
    BDD PickOneMinterm(std::vector<BDD> vars) const;
    DdGen * FirstNode(BDD* fnode) const;
    BDD zddIsop(const BDD& U, ZDD* zdd_I) const;
    BDD Isop(const BDD& U) const;
    ZDD PortToZdd() const;

}; // BDD


/**Class***********************************************************************

  Synopsis     [Class for ADDs.]

  Description  []

  SeeAlso      [Cudd]

******************************************************************************/
class ADD : public ABDD {
    friend class Cudd;
public:
    ADD();
    ADD(Capsule *cap, DdNode *bddNode);
    ADD(Cudd const & manager, DdNode *ddNode);
    ADD(const ADD &from);
    ADD operator=(const ADD& right);
    // Relational operators
    bool operator<=(const ADD& other) const;
    bool operator>=(const ADD& other) const;
    bool operator<(const ADD& other) const;
    bool operator>(const ADD& other) const;
    // Arithmetic operators
    ADD operator-() const;
    ADD operator*(const ADD& other) const;
    ADD operator*=(const ADD& other);
    ADD operator+(const ADD& other) const;
    ADD operator+=(const ADD& other);
    ADD operator-(const ADD& other) const;
    ADD operator-=(const ADD& other);
    // Logical operators
    ADD operator~() const;
    ADD operator&(const ADD& other) const;
    ADD operator&=(const ADD& other);
    ADD operator|(const ADD& other) const;
    ADD operator|=(const ADD& other);
    bool IsZero() const;
    ADD ExistAbstract(const ADD& cube) const;
    ADD UnivAbstract(const ADD& cube) const;
    ADD OrAbstract(const ADD& cube) const;
    ADD Plus(const ADD& g) const;
    ADD Times(const ADD& g) const;
    ADD Threshold(const ADD& g) const;
    ADD SetNZ(const ADD& g) const;
    ADD Divide(const ADD& g) const;
    ADD Minus(const ADD& g) const;
    ADD Minimum(const ADD& g) const;
    ADD Maximum(const ADD& g) const;
    ADD OneZeroMaximum(const ADD& g) const;
    ADD Diff(const ADD& g) const;
    ADD Agreement(const ADD& g) const;
    ADD Or(const ADD& g) const;
    ADD Nand(const ADD& g) const;
    ADD Nor(const ADD& g) const;
    ADD Xor(const ADD& g) const;
    ADD Xnor(const ADD& g) const;
    ADD Log() const;
    ADD FindMax() const;
    ADD FindMin() const;
    ADD IthBit(int bit) const;
    ADD ScalarInverse(const ADD& epsilon) const;
    ADD Ite(const ADD& g, const ADD& h) const;
    ADD IteConstant(const ADD& g, const ADD& h) const;
    ADD EvalConst(const ADD& g) const;
    bool Leq(const ADD& g) const;
    ADD Cmpl() const;
    ADD Negate() const;
    ADD RoundOff(int N) const;
    BDD BddThreshold(CUDD_VALUE_TYPE value) const;
    BDD BddStrictThreshold(CUDD_VALUE_TYPE value) const;
    BDD BddInterval(CUDD_VALUE_TYPE lower, CUDD_VALUE_TYPE upper) const;
    BDD BddIthBit(int bit) const;
    BDD BddPattern() const;
    ADD Cofactor(const ADD& g) const;
    ADD Compose(const ADD& g, int v) const;
    ADD Permute(int * permut) const;
    ADD SwapVariables(std::vector<ADD> x, std::vector<ADD> y) const;
    ADD VectorCompose(std::vector<ADD> vector) const;
    ADD NonSimCompose(std::vector<ADD> vector) const;
    ADD Constrain(const ADD& c) const;
    ADD Restrict(const ADD& c) const;
    ADD MatrixMultiply(const ADD& B, std::vector<ADD> z) const;
    ADD TimesPlus(const ADD& B, std::vector<ADD> z) const;
    ADD Triangle(const ADD& g, std::vector<ADD> z) const;
    ADD Eval(int * inputs) const;
    bool EqualSupNorm(const ADD& g, CUDD_VALUE_TYPE tolerance, int pr) const;

}; // ADD


/**Class***********************************************************************

  Synopsis     [Class for ZDDs.]

  Description  []

  SeeAlso      [Cudd]

******************************************************************************/
class ZDD : public DD {
    friend class Cudd;
public:
    ZDD(Capsule *cap, DdNode *bddNode);
    ZDD();
    ZDD(const ZDD &from);
    ~ZDD();
    ZDD operator=(const ZDD& right);
    bool operator==(const ZDD& other) const;
    bool operator!=(const ZDD& other) const;
    bool operator<=(const ZDD& other) const;
    bool operator>=(const ZDD& other) const;
    bool operator<(const ZDD& other) const;
    bool operator>(const ZDD& other) const;
    void print(int nvars, int verbosity = 1) const;
    ZDD operator*(const ZDD& other) const;
    ZDD operator*=(const ZDD& other);
    ZDD operator&(const ZDD& other) const;
    ZDD operator&=(const ZDD& other);
    ZDD operator+(const ZDD& other) const;
    ZDD operator+=(const ZDD& other);
    ZDD operator|(const ZDD& other) const;
    ZDD operator|=(const ZDD& other);
    ZDD operator-(const ZDD& other) const;
    ZDD operator-=(const ZDD& other);
    int Count() const;
    double CountDouble() const;
    ZDD Product(const ZDD& g) const;
    ZDD UnateProduct(const ZDD& g) const;
    ZDD WeakDiv(const ZDD& g) const;
    ZDD Divide(const ZDD& g) const;
    ZDD WeakDivF(const ZDD& g) const;
    ZDD DivideF(const ZDD& g) const;
    double CountMinterm(int path) const;
    BDD PortToBdd() const;
    ZDD Ite(const ZDD& g, const ZDD& h) const;
    ZDD Union(const ZDD& Q) const;
    ZDD Intersect(const ZDD& Q) const;
    ZDD Diff(const ZDD& Q) const;
    ZDD DiffConst(const ZDD& Q) const;
    ZDD Subset1(int var) const;
    ZDD Subset0(int var) const;
    ZDD Change(int var) const;
    void PrintMinterm() const;
    void PrintCover() const;
    BDD Support() const;

}; // ZDD


/**Class***********************************************************************

  Synopsis     [Class for CUDD managers.]

  Description  []

  SeeAlso      [DD]

******************************************************************************/
class Cudd {
    friend class DD;
    friend class ABDD;
    friend class BDD;
    friend class ADD;
    friend class ZDD;
private:
    Capsule *p;
public:
    Cudd(
      unsigned int numVars = 0,
      unsigned int numVarsZ = 0,
      unsigned int numSlots = CUDD_UNIQUE_SLOTS,
      unsigned int cacheSize = CUDD_CACHE_SLOTS,
      unsigned long maxMemory = 0);
    Cudd(const Cudd& x);
    ~Cudd();
    PFC setHandler(PFC newHandler) const;
    PFC getHandler() const;
    PFC setTimeoutHandler(PFC newHandler) const;
    PFC getTimeoutHandler() const;
    DdManager *getManager() const {return p->manager;}
    inline void makeVerbose() const {p->verbose = 1;}
    inline void makeTerse() {p->verbose = 0;}
    inline bool isVerbose() const {return p->verbose;}
    inline void checkReturnValue(const DdNode *result) const;
    inline void checkReturnValue(const int result) const;
    Cudd& operator=(const Cudd& right);
    void info() const;
    BDD bddVar() const;
    BDD bddVar(int index) const;
    BDD bddOne() const;
    BDD bddZero() const;
    ADD addVar() const;
    ADD addVar(int index) const;
    ADD addOne() const;
    ADD addZero() const;
    ADD constant(CUDD_VALUE_TYPE c) const;
    ADD plusInfinity() const;
    ADD minusInfinity() const;
    ZDD zddVar(int index) const;
    ZDD zddOne(int i) const;
    ZDD zddZero() const;
    ADD addNewVarAtLevel(int level) const;
    BDD bddNewVarAtLevel(int level) const;
    void zddVarsFromBddVars(int multiplicity) const;
    unsigned long ReadStartTime() const;
    unsigned long ReadElapsedTime() const;
    void SetStartTime(unsigned long st) const;
    void ResetStartTime() const;
    unsigned long ReadTimeLimit() const;
    void SetTimeLimit(unsigned long tl) const;
    void UpdateTimeLimit() const;
    void IncreaseTimeLimit(unsigned long increase) const;
    void UnsetTimeLimit() const;
    bool TimeLimited() const;
    void AutodynEnable(Cudd_ReorderingType method) const;
    void AutodynDisable() const;
    bool ReorderingStatus(Cudd_ReorderingType * method) const;
    void AutodynEnableZdd(Cudd_ReorderingType method) const;
    void AutodynDisableZdd() const;
    bool ReorderingStatusZdd(Cudd_ReorderingType * method) const;
    bool zddRealignmentEnabled() const;
    void zddRealignEnable() const;
    void zddRealignDisable() const;
    bool bddRealignmentEnabled() const;
    void bddRealignEnable() const;
    void bddRealignDisable() const;
    ADD background() const;
    void SetBackground(ADD bg) const;
    unsigned int ReadCacheSlots() const;
    double ReadCacheUsedSlots() const;
    double ReadCacheLookUps() const;
    double ReadCacheHits() const;
    unsigned int ReadMinHit() const;
    void SetMinHit(unsigned int hr) const;
    unsigned int ReadLooseUpTo() const;
    void SetLooseUpTo(unsigned int lut) const;
    unsigned int ReadMaxCache() const;
    unsigned int ReadMaxCacheHard() const;
    void SetMaxCacheHard(unsigned int mc) const;
    int ReadSize() const;
    int ReadZddSize() const;
    unsigned int ReadSlots() const;
    unsigned int ReadKeys() const;
    unsigned int ReadDead() const;
    unsigned int ReadMinDead() const;
    unsigned int ReadReorderings() const;
    unsigned int ReadMaxReorderings() const;
    void SetMaxReorderings(unsigned int mr) const;
    long ReadReorderingTime() const;
    int ReadGarbageCollections() const;
    long ReadGarbageCollectionTime() const;
    int ReadSiftMaxVar() const;
    void SetSiftMaxVar(int smv) const;
    int ReadSiftMaxSwap() const;
    void SetSiftMaxSwap(int sms) const;
    double ReadMaxGrowth() const;
    void SetMaxGrowth(double mg) const;
    MtrNode * ReadTree() const;
    void SetTree(MtrNode * tree) const;
    void FreeTree() const;
    MtrNode * ReadZddTree() const;
    void SetZddTree(MtrNode * tree) const;
    void FreeZddTree() const;
    int ReadPerm(int i) const;
    int ReadPermZdd(int i) const;
    int ReadInvPerm(int i) const;
    int ReadInvPermZdd(int i) const;
    BDD ReadVars(int i) const;
    CUDD_VALUE_TYPE ReadEpsilon() const;
    void SetEpsilon(CUDD_VALUE_TYPE ep) const;
    Cudd_AggregationType ReadGroupcheck() const;
    void SetGroupcheck(Cudd_AggregationType gc) const;
    bool GarbageCollectionEnabled() const;
    void EnableGarbageCollection() const;
    void DisableGarbageCollection() const;
    bool DeadAreCounted() const;
    void TurnOnCountDead() const;
    void TurnOffCountDead() const;
    int ReadRecomb() const;
    void SetRecomb(int recomb) const;
    int ReadSymmviolation() const;
    void SetSymmviolation(int symmviolation) const;
    int ReadArcviolation() const;
    void SetArcviolation(int arcviolation) const;
    int ReadPopulationSize() const;
    void SetPopulationSize(int populationSize) const;
    int ReadNumberXovers() const;
    void SetNumberXovers(int numberXovers) const;
    unsigned int ReadOrderRandomization() const;
    void SetOrderRandomization(unsigned int factor) const;
    unsigned long ReadMemoryInUse() const;
    long ReadPeakNodeCount() const;
    long ReadNodeCount() const;
    long zddReadNodeCount() const;
    void AddHook(DD_HFP f, Cudd_HookType where) const;
    void RemoveHook(DD_HFP f, Cudd_HookType where) const;
    bool IsInHook(DD_HFP f, Cudd_HookType where) const;
    void EnableReorderingReporting() const;
    void DisableReorderingReporting() const;
    bool ReorderingReporting() const;
    int ReadErrorCode() const;
    void ClearErrorCode() const;
    FILE *ReadStdout() const;
    void SetStdout(FILE *) const;
    FILE *ReadStderr() const;
    void SetStderr(FILE *) const;
    unsigned int ReadNextReordering() const;
    void SetNextReordering(unsigned int) const;
    double ReadSwapSteps() const;
    unsigned int ReadMaxLive() const;
    void SetMaxLive(unsigned int) const;
    unsigned long ReadMaxMemory() const;
    void SetMaxMemory(unsigned long) const;
    int bddBindVar(int) const;
    int bddUnbindVar(int) const;
    bool bddVarIsBound(int) const;
    ADD Walsh(std::vector<ADD> x, std::vector<ADD> y);
    ADD addResidue(int n, int m, int options, int top);
    int ApaNumberOfDigits(int binaryDigits) const;
    DdApaNumber NewApaNumber(int digits) const;
    void ApaCopy(int digits, DdApaNumber source, DdApaNumber dest) const;
    DdApaDigit ApaAdd(int digits, DdApaNumber a, DdApaNumber b, DdApaNumber
		      sum) const;
    DdApaDigit ApaSubtract(int digits, DdApaNumber a, DdApaNumber b,
			   DdApaNumber diff) const;
    DdApaDigit ApaShortDivision(int digits, DdApaNumber dividend, DdApaDigit
				divisor, DdApaNumber quotient) const;
    void ApaShiftRight(int digits, DdApaDigit in, DdApaNumber a, DdApaNumber
		       b) const;
    void ApaSetToLiteral(int digits, DdApaNumber number, DdApaDigit literal)
      const;
    void ApaPowerOfTwo(int digits, DdApaNumber number, int power) const;
    void ApaPrintHex(FILE * fp, int digits, DdApaNumber number) const;
    void ApaPrintDecimal(FILE * fp, int digits, DdApaNumber number) const;
    void DebugCheck();
    void CheckKeys();
    MtrNode * MakeTreeNode(unsigned int low, unsigned int size, unsigned int type) const;
    // void Harwell(FILE * fp, ADD* E, ADD** x, ADD** y, ADD** xn, ADD** yn_, int * nx, int * ny, int * m, int * n, int bx, int sx, int by, int sy, int pr);
    void PrintLinear();
    int ReadLinear(int x, int y);
    BDD Xgty(std::vector<BDD> z, std::vector<BDD> x, std::vector<BDD> y);
    BDD Xeqy(std::vector<BDD> x, std::vector<BDD> y);
    ADD Xeqy(std::vector<ADD> x, std::vector<ADD> y);
    BDD Dxygtdxz(std::vector<BDD> x, std::vector<BDD> y, std::vector<BDD> z);
    BDD Dxygtdyz(std::vector<BDD> x, std::vector<BDD> y, std::vector<BDD> z);
    BDD Inequality(int c, std::vector<BDD> x, std::vector<BDD> y);
    BDD Disequality(int c, std::vector<BDD> x, std::vector<BDD> y);
    BDD Interval(std::vector<BDD> x, unsigned int lowerB, unsigned int upperB);
    ADD Hamming(std::vector<ADD> xVars, std::vector<ADD> yVars);
    // void Read(FILE * fp, ADD* E, ADD** x, ADD** y, ADD** xn, ADD** yn_, int * nx, int * ny, int * m, int * n, int bx, int sx, int by, int sy);
    // void Read(FILE * fp, BDD* E, BDD** x, BDD** y, int * nx, int * ny, int * m, int * n, int bx, int sx, int by, int sy);
    void ReduceHeap(Cudd_ReorderingType heuristic, int minsize);
    void ShuffleHeap(int * permutation);
    void SymmProfile(int lower, int upper) const;
    unsigned int Prime(unsigned int pr) const;
    void Reserve(int amount) const;
    int SharingSize(DD* nodes, int n) const;
    int SharingSize(const std::vector<BDD>& v) const;
    BDD bddComputeCube(BDD * vars, int * phase, int n) const;
    ADD addComputeCube(ADD * vars, int * phase, int n);
    int NextNode(DdGen * gen, BDD * nnode);
    BDD IndicesToCube(int * array, int n);
    void PrintVersion(FILE * fp) const;
    double AverageDistance() const;
    long Random() const;
    void Srandom(long seed) const;
    MtrNode * MakeZddTreeNode(unsigned int low, unsigned int size, unsigned int type);
    void zddPrintSubtable() const;
    void zddReduceHeap(Cudd_ReorderingType heuristic, int minsize);
    void zddShuffleHeap(int * permutation);
    void zddSymmProfile(int lower, int upper) const;
    void DumpDot(
      const std::vector<BDD>& nodes, 
      char ** inames = 0, 
      char ** onames = 0, 
      FILE * fp = stdout) const;
    void DumpDaVinci(
      const std::vector<BDD>& nodes, 
      char ** inames = 0,
      char ** onames = 0,
      FILE * fp = stdout) const;
    void DumpBlif(
      const std::vector<BDD>& nodes, 
      char ** inames = 0,
      char ** onames = 0,
      char * mname = 0,
      FILE * fp = stdout,
      int mv = 0) const;
    void DumpDDcal(
      const std::vector<BDD>& nodes, 
      char ** inames = 0, 
      char ** onames = 0, 
      FILE * fp = stdout) const;
    void DumpFactoredForm(
      const std::vector<BDD>& nodes, 
      char ** inames = 0,
      char ** onames = 0,
      FILE * fp = stdout) const;
    BDD VectorSupport(const std::vector<BDD>& roots) const;
    std::vector<unsigned int> 
    SupportIndices(const std::vector<ABDD>& roots) const;
    int nodeCount(const std::vector<BDD>& roots) const;
    int VectorSupportSize(const std::vector<BDD>& roots) const;
    void DumpDot(
      const std::vector<ADD>& nodes,
      char ** inames = 0, 
      char ** onames = 0, 
      FILE * fp = stdout) const;
    void DumpDaVinci(
      const std::vector<ADD>& nodes,
      char ** inames = 0,
      char ** onames = 0,
      FILE * fp = stdout) const;
    BDD VectorSupport(const std::vector<ADD>& roots) const;
    int VectorSupportSize(const std::vector<ADD>& roots) const;
    void DumpDot(
      const std::vector<ZDD>& nodes,
      char ** inames = 0,
      char ** onames = 0,
      FILE * fp = stdout) const;

}; // Cudd


extern void defaultError(std::string message);

#endif
