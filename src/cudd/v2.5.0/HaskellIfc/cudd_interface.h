
#include <stdio.h>
#include <sys/types.h>
#include <unistd.h>

#include "cudd.h"


/*#define HSCUDDDEBUG 10000 */
/* #define HSCUDDTRACEORDER */



/* A wrapped DdManager need to allow propber destruction of manger when all references are removed. */
typedef struct  {
  DdManager	*pManager ;     /* the manager */
  uint		uiRefCount ;
} WDdManager ;


/* A wrapped Bdd node-- pointer to these nodes are passed back to the haskell side */
typedef struct  {
  DdNode 	*pNode ;             /* the DD node */
  WDdManager	*pWMan ;             /* the manager */
#ifdef HSCUDDDEBUG 
  int            nodeId;        /*  A unique Id */
#endif
} WBddNode ;




typedef int Boolean ;

typedef  int  (*PIntFuncBddMgr) ( WDdManager *dd ) ;
typedef  void (*PVoidFuncBddMgr)( WDdManager *dd ) ;
typedef  void (*PVoidFuncPVoid)( void * ) ;
typedef  void (*PVoidFuncBddPtr)( WBddNode * ) ;



/* Prototypes */
void hcuddnoop( void *);
WDdManager *hcuddNull() ;
void 		hcuddDestroyBdd( WBddNode *pWnode );
PVoidFuncBddMgr  hcuddManagerDestructor() ;
PVoidFuncPVoid   hcuddNoOpDestructor() ;
PVoidFuncBddPtr hcuddBddDestructor();
void hcuddQuit( WDdManager *pMgr );
WDdManager *hcuddInit( Boolean, unsigned int, unsigned int, unsigned int, unsigned int, unsigned long );
void hcuddRef( DdNode *tmp );

WBddNode *hcuddBddNewVar( WDdManager *pManager ) ;
WBddNode *hcuddBddNewVarAtLevel( WDdManager *pManager, int level ) ;
WBddNode *hcuddBddIthVar( WDdManager *pManager, int index );
int       hcuddGetLevel( WDdManager *pManager, int index );
WBddNode *hcuddReadOne( WDdManager *pManager ) ;
WBddNode *hcuddReadZero( WDdManager *pManager ) ;

WBddNode *hcuddBddIte( WBddNode *aw, WBddNode *bw, WBddNode *cw ) ;
WBddNode *hcuddBddAnd( WBddNode *aw, WBddNode *bw );
WBddNode *hcuddBddOr( WBddNode *aw, WBddNode *bw );
WBddNode *hcuddBddXor( WBddNode *aw, WBddNode *bw );
WBddNode *hcuddBddNand( WBddNode *aw, WBddNode *bw );
WBddNode *hcuddBddNor( WBddNode *aw, WBddNode *bw );
WBddNode *hcuddBddXNor( WBddNode *aw, WBddNode *bw );
WBddNode *hcuddBddNot( WBddNode *aw );
WBddNode *hcuddBddIntersect( WBddNode *aw, WBddNode *bw );
Boolean hcuddLeq ( WBddNode *aw,  WBddNode *bw );

WBddNode *hcuddBddThen( WBddNode *aw );
WBddNode *hcuddBddElse( WBddNode *aw );

DdNode *hcuddBddThenRaw( DdNode * );
DdNode *hcuddBddElseRaw( DdNode * );

Boolean  hcuddIsComplement( WBddNode *aw );
Boolean hcuddIsConstant( WBddNode *dd ) ;
Boolean hcuddIsNull( WBddNode *dd ) ;
Boolean hcuddIsFalse (WBddNode *aw );
Boolean hcuddIsTrue (WBddNode *aw );

int  hcuddNodeReadIndex( WBddNode  *) ;
int  hcuddSupportSize( WBddNode * ) ;

Boolean  hcuddIsComplementRaw( DdNode * );
Boolean hcuddIsConstantRaw( DdNode *dd ) ;
Boolean hcuddIsNullRaw( DdNode *dd ) ;
int  hcuddNodeReadIndexRaw( DdNode  *) ;


DdNode *hcuddRawAnd ( DdNode *, WBddNode * ) ;
DdNode *hcuddRawOr  ( DdNode *, WBddNode * ) ;
DdNode *hcuddRawXor ( DdNode *, WBddNode * ) ;
DdNode *hcuddRawULEBit ( DdNode *, WBddNode *, WBddNode * ) ;
DdNode *hcuddRawAddBit( Boolean, DdNode *cin, WBddNode *aw, WBddNode *bw ) ;
DdNode *hcuddRawCoutBit( Boolean, DdNode *cin, WBddNode *aw, WBddNode *bw ) ;

DdNode *hcuddReadOneRaw( WDdManager * );
DdNode *hcuddReadZeroRaw( WDdManager * ) ;
DdNode *hcuddGetRawUnsafe( WBddNode * ) ;
DdNode *hcuddBddThenRawUnsafe( DdNode *) ;
DdNode *hcuddBddElseRawUnsafe( DdNode *) ;

WBddNode *hcuddToXBddPtr( WDdManager *, DdNode * ) ;

void hcuddDotDump( WBddNode * ) ;
int  hcuddPrintMinterm( WBddNode * ) ;
double hcuddCountMinterm( WBddNode *, int term_count ) ;
double hcuddDagRatio( WBddNode *) ;
int hcuddDagSize( WBddNode *) ;

int hcuddVarCount ( WDdManager *);
