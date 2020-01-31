/**CFile***********************************************************************

  FileName    [testobj.cc]

  PackageName [cuddObj]

  Synopsis    [Test program for the C++ object-oriented encapsulation of CUDD.]

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

#include "cuddObj.hh"
#include <math.h>
#include <iostream>
#include <cassert>

using namespace std;

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

#ifndef lint
static char rcsid[] UNUSED = "$Id: testobj.cc,v 1.7 2012/02/05 01:06:40 fabio Exp fabio $";
#endif

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static void testBdd(Cudd& mgr, int verbosity);
static void testAdd(Cudd& mgr, int verbosity);
static void testAdd2(Cudd& mgr, int verbosity);
static void testZdd(Cudd& mgr, int verbosity);
static void testBdd2(Cudd& mgr, int verbosity);
static void testBdd3(Cudd& mgr, int verbosity);
static void testZdd2(Cudd& mgr, int verbosity);
static void testBdd4(Cudd& mgr, int verbosity);
static void testBdd5(Cudd& mgr, int verbosity);


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Main program for testobj.]

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
int
main(int argc, char **argv)
{
    int verbosity = 0;

    if (argc == 2) {
        int retval = sscanf(argv[1], "%d", &verbosity);
        if (retval != 1)
            return 1;
    } else if (argc != 1) {
        return 1;
    }

    Cudd mgr(0,2);
    // mgr.makeVerbose();		// trace constructors and destructors
    testBdd(mgr,verbosity);
    testAdd(mgr,verbosity);
    testAdd2(mgr,verbosity);
    testZdd(mgr,verbosity);
    testBdd2(mgr,verbosity);
    testBdd3(mgr,verbosity);
    testZdd2(mgr,verbosity);
    testBdd4(mgr,verbosity);
    testBdd5(mgr,verbosity);
    if (verbosity) mgr.info();
    return 0;

} // main


/**Function********************************************************************

  Synopsis    [Test basic operators on BDDs.]

  Description [Test basic operators on BDDs. The function returns void
  because it relies on the error handling done by the interface. The
  default error handler causes program termination.]

  SideEffects [Creates BDD variables in the manager.]

  SeeAlso     [testBdd2 testBdd3 testBdd4 testBdd5]

******************************************************************************/
static void
testBdd(
  Cudd& mgr,
  int verbosity)
{
    if (verbosity) cout << "Entering testBdd\n";
    // Create two new variables in the manager. If testBdd is called before
    // any variable is created in mgr, then x gets index 0 and y gets index 1.
    BDD x = mgr.bddVar();
    BDD y = mgr.bddVar();

    BDD f = x * y;
    if (verbosity) cout << "f"; f.print(2,verbosity);

    BDD g = y + !x;
    if (verbosity) cout << "g"; g.print(2,verbosity);

    if (verbosity) 
        cout << "f and g are" << (f == !g ? "" : " not") << " complementary\n";
    if (verbosity) 
        cout << "f is" << (f <= g ? "" : " not") << " less than or equal to g\n";

    g = f | ~g;
    if (verbosity) cout << "g"; g.print(2,verbosity);

    BDD h = f = y;
    if (verbosity) cout << "h"; h.print(2,verbosity);

    if (verbosity) cout << "x + h has " << (x+h).nodeCount() << " nodes\n";

    h += x;
    if (verbosity) cout << "h"; h.print(2,verbosity);

} // testBdd


/**Function********************************************************************

  Synopsis    [Test basic operators on ADDs.]

  Description [Test basic operators on ADDs. The function returns void
  because it relies on the error handling done by the interface. The
  default error handler causes program termination.]

  SideEffects [May create ADD variables in the manager.]

  SeeAlso     [testAdd2]

******************************************************************************/
static void
testAdd(
  Cudd& mgr,
  int verbosity)
{
    if (verbosity) cout << "Entering testAdd\n";
    // Create two ADD variables. If we called method addVar without an
    // argument, we would get two new indices. If testAdd is indeed called
    // after testBdd, then those indices would be 2 and 3. By specifying the
    // arguments, on the other hand, we avoid creating new unnecessary BDD
    // variables.
    ADD p = mgr.addVar(0);
    ADD q = mgr.addVar(1);

    // Test arithmetic operators.
    ADD r = p + q;
    if (verbosity) cout << "r"; r.print(2,verbosity);

    // CUDD_VALUE_TYPE is double.
    ADD s = mgr.constant(3.0);
    s *= p * q;
    if (verbosity) cout << "s"; s.print(2,verbosity);

    s += mgr.plusInfinity();
    if (verbosity) cout << "s"; s.print(2,verbosity);

    // Test relational operators.
    if (verbosity) 
        cout << "p is" << (p <= r ? "" : " not") << " less than or equal to r\n";

    // Test logical operators.
    r = p | q;
    if (verbosity) cout << "r"; r.print(2,verbosity);

} // testAdd


/**Function********************************************************************

  Synopsis    [Test some more operators on ADDs.]

  Description [Test some more operators on ADDs. The function returns void
  because it relies on the error handling done by the interface. The
  default error handler causes program termination.]

  SideEffects [May create ADD variables in the manager.]

  SeeAlso     [testAdd]

******************************************************************************/
static void
testAdd2(
  Cudd& mgr,
  int verbosity)
{
    if (verbosity) cout << "Entering testAdd2\n";
    // Create two ADD variables. If we called method addVar without an
    // argument, we would get two new indices.
    int i;
    vector<ADD> x(2);
    for (i = 0; i < 2; i++) {
	x[i] = mgr.addVar(i);
    }

    // Build a probability density function: [0.1, 0.2, 0.3, 0.4].
    ADD f0 = x[1].Ite(mgr.constant(0.2), mgr.constant(0.1));
    ADD f1 = x[1].Ite(mgr.constant(0.4), mgr.constant(0.3));
    ADD f  = x[0].Ite(f1, f0);
    if (verbosity) cout << "f"; f.print(2,verbosity);

    // Compute the entropy.
    ADD l = f.Log();
    if (verbosity) cout << "l"; l.print(2,verbosity);
    ADD r = f * l;
    if (verbosity) cout << "r"; r.print(2,verbosity);

    ADD e = r.MatrixMultiply(mgr.constant(-1.0/log(2.0)),x);
    if (verbosity) cout << "e"; e.print(2,verbosity);

} // testAdd2


/**Function********************************************************************

  Synopsis    [Test basic operators on ZDDs.]

  Description [Test basic operators on ZDDs. The function returns void
  because it relies on the error handling done by the interface. The
  default error handler causes program termination.]

  SideEffects [May create ZDD variables in the manager.]

  SeeAlso     [testZdd2]

******************************************************************************/
static void
testZdd(
  Cudd& mgr,
  int verbosity)
{
    if (verbosity) cout << "Entering testZdd\n";
    ZDD v = mgr.zddVar(0);
    ZDD w = mgr.zddVar(1);

    ZDD s = v + w;
    if (verbosity) cout << "s"; s.print(2,verbosity);

    if (verbosity) cout << "v is" << (v < s ? "" : " not") << " less than s\n";

    s -= v;
    if (verbosity) cout << "s"; s.print(2,verbosity);

} // testZdd


/**Function********************************************************************

  Synopsis    [Test vector operators on BDDs.]

  Description [Test vector operators on BDDs. The function returns void
  because it relies on the error handling done by the interface. The
  default error handler causes program termination.]

  SideEffects [May create BDD variables in the manager.]

  SeeAlso     [testBdd testBdd3 testBdd4 testBdd5]

******************************************************************************/
static void
testBdd2(
  Cudd& mgr,
  int verbosity)
{
    if (verbosity) cout << "Entering testBdd2\n";
    vector<BDD> x(4);
    for (int i = 0; i < 4; i++) {
	x[i] = mgr.bddVar(i);
    }

    // Create the BDD for the Achilles' Heel function.
    BDD p1 = x[0] * x[2];
    BDD p2 = x[1] * x[3];
    BDD f = p1 + p2;
    const char* inames[] = {"x0", "x1", "x2", "x3"};
    if (verbosity) {
        cout << "f"; f.print(4,verbosity);
        cout << "Irredundant cover of f:" << endl; f.PrintCover();
        cout << "Number of minterms (arbitrary precision): "; f.ApaPrintMinterm(4);
        cout << "Number of minterms (extended precision):  "; f.EpdPrintMinterm(4);
        cout << "Two-literal clauses of f:" << endl;
        f.PrintTwoLiteralClauses((char **)inames); cout << endl;
    }

    vector<BDD> vect = f.CharToVect();
    if (verbosity) {
        for (size_t i = 0; i < vect.size(); i++) {
            cout << "vect[" << i << "]" << endl; vect[i].PrintCover();
        }
    }

    // v0,...,v3 suffice if testBdd2 is called before testBdd3.
    if (verbosity) {
        const char* onames[] = {"v0", "v1", "v2", "v3", "v4", "v5"};
        mgr.DumpDot(vect, (char **)inames,(char **)onames);
    }

} // testBdd2


/**Function********************************************************************

  Synopsis    [Test additional operators on BDDs.]

  Description [Test additional operators on BDDs. The function returns
  void because it relies on the error handling done by the
  interface. The default error handler causes program termination.]

  SideEffects [May create BDD variables in the manager.]

  SeeAlso     [testBdd testBdd2 testBdd4 testBdd5]

******************************************************************************/
static void
testBdd3(
  Cudd& mgr,
  int verbosity)
{
    if (verbosity) cout << "Entering testBdd3\n";
    vector<BDD> x(6);
    for (int i = 0; i < 6; i++) {
	x[i] = mgr.bddVar(i);
    }

    BDD G = x[4] + !x[5];
    BDD H = x[4] * x[5];
    BDD E = x[3].Ite(G,!x[5]);
    BDD F = x[3] + !H;
    BDD D = x[2].Ite(F,!H);
    BDD C = x[2].Ite(E,!F);
    BDD B = x[1].Ite(C,!F);
    BDD A = x[0].Ite(B,!D);
    BDD f = !A;
    if (verbosity) cout << "f"; f.print(6,verbosity);

    BDD f1 = f.RemapUnderApprox(6);
    if (verbosity) cout << "f1"; f1.print(6,verbosity);
    if (verbosity) 
        cout << "f1 is" << (f1 <= f ? "" : " not") << " less than or equal to f\n";

    BDD g;
    BDD h;
    f.GenConjDecomp(&g,&h);
    if (verbosity) {
        cout << "g"; g.print(6,verbosity);
        cout << "h"; h.print(6,verbosity);
        cout << "g * h " << (g * h == f ? "==" : "!=") << " f\n";
    }

} // testBdd3


/**Function********************************************************************

  Synopsis    [Test cover manipulation with BDDs and ZDDs.]

  Description [Test cover manipulation with BDDs and ZDDs.  The
  function returns void because it relies on the error handling done by
  the interface.  The default error handler causes program
  termination.  This function builds the BDDs for a transformed adder:
  one in which the inputs are transformations of the original
  inputs. It then creates ZDDs for the covers from the BDDs.]

  SideEffects [May create BDD and ZDD variables in the manager.]

  SeeAlso     [testZdd]

******************************************************************************/
static void
testZdd2(
  Cudd& mgr,
  int verbosity)
{
    if (verbosity) cout << "Entering testZdd2\n";
    int N = 3;			// number of bits
    // Create variables.
    vector<BDD> a(N);
    vector<BDD> b(N);
    vector<BDD> c(N+1);
    for (int i = 0; i < N; i++) {
	a[N-1-i] = mgr.bddVar(2*i);
	b[N-1-i] = mgr.bddVar(2*i+1);
    }
    c[0] = mgr.bddVar(2*N);
    // Build functions.
    vector<BDD> s(N);
    for (int i = 0; i < N; i++) {
	s[i] = a[i].Xnor(c[i]);
	c[i+1] = a[i].Ite(b[i],c[i]);
    }

    // Create array of outputs and print it.
    vector<BDD> p(N+1);
    for (int i = 0; i < N; i++) {
	p[i] = s[i];
    }
    p[N] = c[N];
    if (verbosity) {
        for (size_t i = 0; i < p.size(); i++) {
            cout << "p[" << i << "]"; p[i].print(2*N+1,verbosity);
        }
    }
    const char* onames[] = {"s0", "s1", "s2", "c3"};
    if (verbosity) {
        const char* inames[] = {"a2", "b2", "a1", "b1", "a0", "b0", "c0"};
        mgr.DumpDot(p, (char **)inames,(char **)onames);
    }

    // Create ZDD variables and build ZDD covers from BDDs.
    mgr.zddVarsFromBddVars(2);
    vector<ZDD> z(N+1);
    for (int i = 0; i < N+1; i++) {
	ZDD temp;
	BDD dummy = p[i].zddIsop(p[i],&temp);
	z[i] = temp;
    }

    // Print out covers.
    if (verbosity) {
        for (size_t i = 0; i < z.size(); i++) {
            cout << "z[" << i << "]"; z[i].print(4*N+2,verbosity);
        }
        for (size_t i = 0; i < z.size(); i++) {
            cout << "z[" << i << "]\n"; z[i].PrintCover();
        }
        const char* znames[] = {"a2+", "a2-", "b2+", "b2-", "a1+", "a1-", "b1+",
                                "b1-", "a0+", "a0-", "b0+", "b0-", "c0+", "c0-"};
        mgr.DumpDot(z, (char **)znames,(char **)onames);
    }

} // testZdd2


/**Function********************************************************************

  Synopsis    [Test transfer between BDD managers.]

  Description [Test transfer between BDD managers.  The
  function returns void because it relies on the error handling done by
  the interface.  The default error handler causes program
  termination.]

  SideEffects [May create BDD variables in the manager.]

  SeeAlso     [testBdd testBdd2 testBdd3 testBdd5]

******************************************************************************/
static void
testBdd4(
  Cudd& mgr,
  int verbosity)
{
    if (verbosity) cout << "Entering testBdd4\n";
    BDD x = mgr.bddVar(0);
    BDD y = mgr.bddVar(1);
    BDD z = mgr.bddVar(2);

    BDD f = !x * !y * !z + x * y;
    if (verbosity) cout << "f"; f.print(3,verbosity);

    Cudd otherMgr(0,0);
    BDD g = f.Transfer(otherMgr);
    if (verbosity) cout << "g"; g.print(3,verbosity);

    BDD h = g.Transfer(mgr);
    if (verbosity) 
        cout << "f and h are" << (f == h ? "" : " not") << " identical\n";

} // testBdd4



/**Function********************************************************************

  Synopsis    [Test maximal expansion of cubes.]

  Description [Test maximal expansion of cubes.  The function returns
  void because it relies on the error handling done by the interface.
  The default error handler causes program termination.]

  SideEffects [May create BDD variables in the manager.]

  SeeAlso     [testBdd testBdd2 testBdd3 testBdd4]

******************************************************************************/
static void
testBdd5(
  Cudd& mgr,
  int verbosity)
{
    if (verbosity) cout << "Entering testBdd5\n";
    vector<BDD> x;
    x.reserve(4);
    for (int i = 0; i < 4; i++) {
	x.push_back(mgr.bddVar(i));
    }
    const char* inames[] = {"a", "b", "c", "d"};
    BDD f = (x[1] & x[3]) | (x[0] & !x[2] & x[3]) | (!x[0] & x[1] & !x[2]);
    BDD lb = x[1] & !x[2] & x[3];
    BDD ub = x[3];
    BDD primes = lb.MaximallyExpand(ub,f);
    assert(primes == (x[1] & x[3]));
    BDD lprime = primes.LargestPrimeUnate(lb);
    assert(lprime == primes);
    if (verbosity) {
      const char * onames[] = {"lb", "ub", "f", "primes", "lprime"};
        vector<BDD> z;
        z.reserve(5);
        z.push_back(lb);
        z.push_back(ub);
        z.push_back(f);
        z.push_back(primes);
        z.push_back(lprime);
        mgr.DumpDot(z, (char **)inames, (char **)onames);
        cout << "primes(1)"; primes.print(4,verbosity);
    }

    lb = !x[0] & x[2] & x[3];
    primes = lb.MaximallyExpand(ub,f);
    assert(primes == mgr.bddZero());
    if (verbosity) {
        cout << "primes(2)"; primes.print(4,verbosity);
    }

    lb = x[0] & !x[2] & x[3];
    primes = lb.MaximallyExpand(ub,f);
    assert(primes == lb);
    lprime = primes.LargestPrimeUnate(lb);
    assert(lprime == primes);
    if (verbosity) {
        cout << "primes(3)"; primes.print(4,verbosity);
    }

    lb = !x[0] & x[1] & !x[2] & x[3];
    ub = mgr.bddOne();
    primes = lb.MaximallyExpand(ub,f);
    assert(primes == ((x[1] & x[3]) | (!x[0] & x[1] & !x[2])));
    lprime = primes.LargestPrimeUnate(lb);
    assert(lprime == (x[1] & x[3]));
    if (verbosity) {
        cout << "primes(4)"; primes.print(4,1); primes.PrintCover();
    }

    ub = !x[0] & x[3];
    primes = lb.MaximallyExpand(ub,f);
    assert(primes == (!x[0] & x[1] & x[3]));
    lprime = primes.LargestPrimeUnate(lb);
    assert(lprime == primes);
    if (verbosity) {
        cout << "primes(5)"; primes.print(4,verbosity);
    }

} // testBdd5
