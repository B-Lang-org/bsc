

#include <stdlib.h>
#include <assert.h>
#include <math.h>
#include "cudd_interface.h"


#define GetNode(WrappedNode)    ((WrappedNode)->pNode )
#define GetMgr(WrappedNode)     ((WrappedNode)->pWMan->pManager )
#define GetWMan(WrappedNode)     ((WrappedNode)->pWMan )
#define GetFromWMan(WrappedMan)    ((WrappedMan)->pManager )

#define SAMEMANAGER( NodeA, NodeB )  (assert(GetMgr(NodeA) == GetMgr(NodeB)))
#define MAX(a,b)                ((a) < (b) ? (b) : (a) )
#define MIN(a,b)                ((a) < (b) ? (a) : (b) )



#ifdef HSCUDDDEBUG
static unsigned int iNodeCount = 0;
static unsigned int iNodeId = 0;
#endif


/* Prototypes */
static WBddNode 	*hcuddWrapNode( DdNode *pNode, WDdManager *pManager ) ;
static void              hcuddRecursizeDeref( DdManager *pMan, DdNode *pNode ) ;
/* End Prototypes */


void   hcuddDerefWman( WDdManager *pWMan ) 
{
  --(pWMan->uiRefCount) ;        /* decrement ref count */

  if ( pWMan->uiRefCount == 0 )
    {
#ifdef HSCUDDDEBUG
      printf( "Wrapped Manager reference Count at Zero -- call quit. Node Count%4d addr: %p\n\n",
              iNodeCount, pWMan );
#endif      
      DdManager *pMgr = pWMan->pManager ;
      Cudd_Quit( pMgr ) ;
      pWMan->pManager = (void *) 5 ;     /* debug */

      free( pWMan );
    }
}

void   hcuddRefWman( WDdManager *pWMan ) 
{
  ++(pWMan->uiRefCount) ;        /* decrement ref count */
}


/* Wrapps a regular bdd ptr into a WrappedNode, updates reference count, ready for pointer back to haskell */
static WBddNode *hcuddWrapNode( DdNode *pNode, WDdManager *pWMan )
{
  if ( pNode != 0 ) {
    WBddNode *tmp = (WBddNode *) malloc( sizeof( WBddNode ) ) ;

#ifdef HSCUDDDEBUG
    ++iNodeCount ;
    ++iNodeId ;
    if ( ( iNodeCount % HSCUDDDEBUG ) ==  0 ) {
      printf( "Calling Wrapper on node id= %4u %4u, %8p %8p\n", iNodeId, iNodeCount, tmp, pWMan ) ;
    }
    tmp->nodeId = iNodeId ;
#endif

    tmp->pNode = pNode ;
    tmp->pWMan = pWMan ;
    hcuddRefWman( pWMan ) ;
    hcuddRef( pNode ) ;
    return tmp ;
  } else {
    return 0;
  }
}

void hcuddDestroyBdd( WBddNode *pWnode )
{
  WDdManager *pWMan   = GetWMan( pWnode ) ;
  DdManager *pManager = GetFromWMan( pWMan );
  DdNode    *pNode    = GetNode( pWnode ) ;


  hcuddRecursizeDeref( pManager, pNode ) ;

#ifdef HSCUDDDEBUG
  --iNodeCount ;
  if ( ( iNodeCount % HSCUDDDEBUG ) == 0 ) {
    printf( "Calling destructor on node id = %4u   %4u, %8p \n", pWnode->nodeId, iNodeCount, pWnode ) ;
  }
#endif

  pWnode->pWMan = (void *) 5 ;  /* debug */
  hcuddDerefWman( pWMan ) ;

  free( pWnode );
}


/* return a pointer to a bdd manager destructor  -- needed for Haskell's finalized pointers
 */
PVoidFuncBddMgr  hcuddManagerDestructor() 
{
  return hcuddQuit ;
}
PVoidFuncPVoid   hcuddNoOpDestructor() 
{
  return hcuddnoop ;
}

PVoidFuncBddPtr hcuddBddDestructor()
{
  return hcuddDestroyBdd ;
}

void myPrintVarOrders( DdManager *pmgr ) 
{
  int i ;
  int size = Cudd_ReadSize( pmgr ) ;
  for ( i = 0 ; i < size ; ++i )
      printf ( "Var/Order: %4d  %4d\n", i, Cudd_ReadPerm( pmgr, i ) ) ;
  
}

int myPostReorderHood( DdManager *pmgr, char *name, void *ns)
{
  unsigned int nextorder, maxcache;
  nextorder = Cudd_ReadNextReordering( pmgr ) ;
  maxcache = Cudd_ReadMaxCacheHard( pmgr );

  fflush ( stdout ) ;
  printf( "Calling post reorder hook -- next order is %u -- max cache is %u\n", nextorder, maxcache ) ;
  myPrintVarOrders( pmgr ) ;
  Cudd_PrintInfo( pmgr, stdout ) ;
  fflush ( stdout ) ;

  return 1;
}


WDdManager *hcuddInit(  Boolean  reorder,
                        unsigned int numVars,
                        unsigned int numVarsZ,
                        unsigned int numSlots,
                        unsigned int cacheSize,
                        unsigned long maxMemory)
{
  WDdManager *pWMan ;
  DdManager *pmgr = Cudd_Init(numVars, numVarsZ, numSlots, cacheSize, maxMemory);

  if ( reorder ) {
    Cudd_AutodynEnable( pmgr, CUDD_REORDER_SIFT );
  }

  /* Cudd_AutodynEnable( pmgr, CUDD_REORDER_RANDOM );*/
  /* Cudd_AutodynEnable( pmgr, CUDD_REORDER_SYMM_SIFT ); -- not a good idea -- did not see grouping formed.*/


  Cudd_SetStdout( pmgr, stdout ) ;

#ifdef HSCUDDTRACEORDER
  Cudd_AddHook( pmgr, myPostReorderHood, CUDD_POST_REORDERING_HOOK );
#endif  

  /* Allocate a handle for the package to deal with */ 
  pWMan = (WDdManager *) malloc ( sizeof ( WDdManager ) ) ;
  pWMan->pManager = pmgr ;
  pWMan->uiRefCount = 1 ;

#ifdef HSCUDDDEBUG
  printf( "Created a new bdd manager %p\n", pWMan ) ;
#endif

  return pWMan ;
}


/*  generate noop function */
WDdManager *hcuddNull()
{
  return 0;
}
void hcuddnoop( void *ignore)
{
}


void hcuddQuit( WDdManager *pMgr )
{
#ifdef HSCUDDDEBUG
  printf ( "Calling manager quit -- current allocated Node is %u, refcount = %u\n", iNodeCount, pMgr->uiRefCount );
#endif
  hcuddDerefWman( pMgr ) ;

}

/* convience function to avoid referencing a null pointer */
void hcuddRef( DdNode *pNode )
{
  if (0 != Cudd_Regular( pNode ) ) {
    Cudd_Ref( pNode ) ;
  }
}
static void hcuddRecursizeDeref( DdManager *pMan, DdNode *pNode ) 
{
  if ( Cudd_Regular( pNode )) {
    Cudd_RecursiveDeref( pMan, pNode );
  }
}


WBddNode *hcuddBddNewVar( WDdManager *pWMan ) 
{
  DdManager *pManager = GetFromWMan( pWMan ) ;
  DdNode *tmp = Cudd_bddNewVar( pManager ) ;
#ifdef HSCUDDDEBUG
  if (tmp == 0) { fprintf(stderr, "BDD NEW VAR returns null\n"); }
#endif
  return hcuddWrapNode( tmp, pWMan ) ;
}
WBddNode *hcuddBddNewVarAtLevel( WDdManager *pWMan, int level ) 
{
  DdManager *pManager = GetFromWMan( pWMan ) ;
  DdNode *tmp = Cudd_bddNewVarAtLevel( pManager, MIN( level, 1 ) ) ;
#ifdef HSCUDDDEBUG
  if (tmp == 0) { fprintf(stderr, "BDD NEW VAR at level returns null\nu"); }
#endif
  return hcuddWrapNode( tmp, pWMan ) ;
}
int hcuddGetLevel( WDdManager *pWMan, int index )
{
  DdManager *pManager = GetFromWMan( pWMan ) ;
  return Cudd_ReadPerm( pManager, index );
}

WBddNode *hcuddBddIthVar( WDdManager *pWMan, int index )
{
  DdManager *pManager = GetFromWMan( pWMan ) ;
  DdNode *tmp = Cudd_bddIthVar( pManager, index );
  return hcuddWrapNode ( tmp, pWMan ) ;
}

WBddNode *hcuddReadOne( WDdManager *pWMan ) 
{
  DdManager *pManager = GetFromWMan( pWMan ) ;
  DdNode *tmp = Cudd_ReadOne( pManager );
  return hcuddWrapNode ( tmp, pWMan ) ;
}

WBddNode *hcuddReadZero( WDdManager *pWMan ) 
{
  DdManager *pManager = GetFromWMan( pWMan ) ;
  DdNode *tmp = Cudd_ReadLogicZero( pManager );
  return hcuddWrapNode ( tmp, pWMan ) ;
}

int hcuddSupportSize( WBddNode *aw )
{ 
  DdNode *ap;
  DdManager *mgr ;
  ap = GetNode( aw ) ;
  mgr = GetMgr ( aw ) ;
  return Cudd_SupportSize( mgr, ap) ;
}

WBddNode *hcuddBddIte( WBddNode *aw, WBddNode *bw, WBddNode *cw ) 
{
  DdNode *ap, *bp, *cp, *tmp ;
  DdManager *mgr ;
  WDdManager *pWMan = GetWMan( aw ) ;
  SAMEMANAGER( aw, bw ) ;
  SAMEMANAGER( aw, cw ) ;
  
  ap = GetNode( aw ) ;
  bp = GetNode( bw ) ;
  cp = GetNode( cw ) ;
  mgr = GetMgr ( aw ) ;

  tmp = Cudd_bddIte( mgr, ap, bp, cp ) ;
  return hcuddWrapNode ( tmp, pWMan ) ;
}



WBddNode *hcuddBddAnd( WBddNode *aw, WBddNode *bw )
{
  DdNode *ap, *bp, *tmp ;
  DdManager *mgr ;
  WDdManager *pWMan = GetWMan( aw ) ;
  SAMEMANAGER( aw, bw ) ;

  ap = GetNode( aw ) ;
  bp = GetNode( bw ) ;
  mgr = GetMgr ( aw ) ;

  tmp = Cudd_bddAnd( mgr, ap, bp ) ;
  return hcuddWrapNode ( tmp, pWMan ) ;
}


WBddNode *hcuddBddOr( WBddNode *aw, WBddNode *bw )
{
  DdNode *ap, *bp, *tmp ;
  DdManager *mgr ;
  WDdManager *pWMan = GetWMan( aw ) ;
  SAMEMANAGER( aw, bw ) ;

  ap = GetNode( aw ) ;
  bp = GetNode( bw ) ;
  mgr = GetMgr ( aw ) ;

  tmp = Cudd_bddOr( mgr, ap, bp ) ;
  return hcuddWrapNode ( tmp, pWMan ) ;
}

WBddNode *hcuddBddXor( WBddNode *aw, WBddNode *bw )
{
  DdNode *ap, *bp, *tmp ;
  DdManager *mgr ;
  WDdManager *pWMan = GetWMan( aw ) ;
  SAMEMANAGER( aw, bw ) ;

  ap = GetNode( aw ) ;
  bp = GetNode( bw ) ;
  mgr = GetMgr ( aw ) ;

  tmp = Cudd_bddXor( mgr, ap, bp ) ;
  return hcuddWrapNode ( tmp, pWMan ) ;
}

WBddNode *hcuddBddNand( WBddNode *aw, WBddNode *bw )
{
  DdNode *ap, *bp, *tmp ;
  DdManager *mgr ;
  WDdManager *pWMan = GetWMan( aw ) ;
  SAMEMANAGER( aw, bw ) ;

  ap = GetNode( aw ) ;
  bp = GetNode( bw ) ;
  mgr = GetMgr ( aw ) ;

  tmp = Cudd_bddNand( mgr, ap, bp ) ;
  return hcuddWrapNode ( tmp, pWMan ) ;
}

WBddNode *hcuddBddNor( WBddNode *aw, WBddNode *bw )
{
  DdNode *ap, *bp, *tmp ;
  DdManager *mgr ;
  WDdManager *pWMan = GetWMan( aw ) ;
  SAMEMANAGER( aw, bw ) ;

  ap = GetNode( aw ) ;
  bp = GetNode( bw ) ;
  mgr = GetMgr ( aw ) ;

  tmp = Cudd_bddNor( mgr, ap, bp ) ;
  return hcuddWrapNode ( tmp, pWMan ) ;
}


WBddNode *hcuddBddXNor( WBddNode *aw, WBddNode *bw )
{
  DdNode *ap, *bp, *tmp ;
  DdManager *mgr ;
  WDdManager *pWMan = GetWMan( aw ) ;
  SAMEMANAGER( aw, bw ) ;

  ap = GetNode( aw ) ;
  bp = GetNode( bw ) ;
  mgr = GetMgr ( aw ) ;

  tmp = Cudd_bddXnor( mgr, ap, bp ) ;
  return hcuddWrapNode ( tmp, pWMan ) ;
}

WBddNode *hcuddBddNot( WBddNode *aw )
{
  DdNode *ap, *tmp ;
  WDdManager *pWMan = GetWMan( aw ) ;
  
  ap = GetNode( aw ) ;

  tmp = Cudd_Not( ap ) ;
  return hcuddWrapNode ( tmp, pWMan ) ;
}

WBddNode *hcuddBddIntersect( WBddNode *aw, WBddNode *bw )
{
  DdNode *ap, *bp, *tmp ;
  DdManager *mgr ;
  WDdManager *pWMan = GetWMan( aw ) ;
  SAMEMANAGER( aw, bw ) ;

  ap = GetNode( aw ) ;
  bp = GetNode( bw ) ;
  mgr = GetMgr ( aw ) ;

  tmp = Cudd_bddIntersect( mgr, ap, bp ) ;
  return hcuddWrapNode ( tmp, pWMan ) ;
}


WBddNode *hcuddBddThen( WBddNode *aw )
{
  DdNode *ap, *tmp ;
  WDdManager *pWMan = GetWMan( aw ) ;
  
  ap = GetNode( aw ) ;

  tmp = Cudd_T( ap ) ;
  return hcuddWrapNode ( tmp, pWMan ) ;
}

WBddNode *hcuddBddElse( WBddNode *aw )
{
  DdNode *ap, *tmp ;
  WDdManager *pWMan = GetWMan( aw ) ;

  ap = GetNode( aw ) ;

  tmp = Cudd_E( ap ) ;
  return hcuddWrapNode ( tmp, pWMan ) ;
}


/* Note-- reference count unchanged. */
DdNode *hcuddGetRawUnsafe( WBddNode *aw )
{
  return GetNode ( aw );
}
/* These nodes do not have reference count > 0, unless their parent is still alive. */
DdNode *hcuddBddThenRawUnsafe( DdNode *ap )
{
   return Cudd_T( ap ) ;
}

/* These nodes do not have reference count > 0, unless their parent is still alive. */
DdNode *hcuddBddElseRawUnsafe( DdNode *ap )
{
  return Cudd_E( ap ) ;
}

Boolean  hcuddIsComplement( WBddNode *aw )
{
  DdNode *ap = GetNode( aw ) ;

  return Cudd_IsComplement( ap );
}
Boolean hcuddIsConstant( WBddNode *aw ) 
{
  DdNode *ap = GetNode( aw ) ;

  return Cudd_IsConstant( ap );
}
Boolean hcuddIsNull( WBddNode *aw ) 
{
  DdNode *ap = GetNode( aw ) ;

  return 0 == Cudd_Regular( ap ) ;
}
Boolean hcuddIsTrue ( WBddNode *aw )
{
  DdNode *ap = GetNode( aw ) ;
  return  Cudd_IsConstant( ap ) && ! Cudd_IsComplement( ap );
}
Boolean hcuddIsFalse ( WBddNode *aw )
{
  DdNode *ap = GetNode( aw ) ;
  return  Cudd_IsConstant( ap ) && Cudd_IsComplement( ap );
}

Boolean hcuddLeq ( WBddNode *aw,  WBddNode *bw )
{
  DdNode *ap, *bp ;
  DdManager *mgr ;
  SAMEMANAGER( aw, bw ) ;

  ap = GetNode( aw ) ;
  bp = GetNode( bw ) ;
  mgr = GetMgr ( aw ) ;

  return Cudd_bddLeq (mgr, ap, bp ) ;

}

int hcuddNodeReadIndex( WBddNode *aw )
{
  DdNode *ap = GetNode( aw );
  return Cudd_NodeReadIndex( ap ) ;
}

Boolean hcuddIsComplementRaw( DdNode *ap )
{
  return Cudd_IsComplement( ap ) ;
}
Boolean hcuddIsConstantRaw( DdNode *ap )
{
  return Cudd_IsConstant( ap );
}
Boolean hcuddIsNullRaw( DdNode *ap )
{
  return 0 == Cudd_Regular( ap ) ;
}
int hcuddNodeReadIndexRaw( DdNode *ap )
{
  return Cudd_NodeReadIndex( ap ) ;
}


/* TODO return a file name */
void hcuddDotDump( WBddNode *wnode)
{
  DdManager *pMgr = GetMgr( wnode ) ;
  DdNode *b = GetNode ( wnode ) ;
  static int iCount = 0 ;
  FILE *fp ;

  char  buffer[1000] ;
  
  pid_t pid = getpid() ;
  sprintf( buffer, "/tmp/bddDump_%d_%d.dot", pid, ++iCount );
 
  fp = fopen ( buffer, "w" );
  if ( fp ) {
    Cudd_DumpDot( pMgr, 1, & b ,0,0, fp ) ;
    
    fclose ( fp ) ;
  }
}

int  hcuddPrintMinterm( WBddNode *wnode ) 
{
  int returnValue = 0;
  DdManager *pMgr = GetMgr( wnode ) ;
  DdNode *b = GetNode ( wnode ) ;
  fflush ( stdout ) ;
  printf( "Print MinTerms: \n");
  returnValue = Cudd_PrintMinterm( pMgr, b ) ;
  fflush ( stdout ) ;
  return returnValue ;
}

double hcuddCountMinterm( WBddNode *wnode, int term_count ) 
{
  DdManager *pMgr = GetMgr( wnode ) ;
  DdNode *b = GetNode ( wnode ) ;

  return Cudd_CountMinterm( pMgr, b, term_count ) ;
}


/* The raw functions deal return raw DdNode pointers with the referenc count increased.
These should be used in back into Raw function to allow for Deref of the pointer
or hcuddToXBddPtr which derefs and wraps the pointer.
*/
DdNode *hcuddRawAnd ( DdNode *ap, WBddNode *bw ) 
{
  DdNode *bp = GetNode( bw ) ;
  DdManager *mgr = GetMgr ( bw ) ;

  DdNode *tmp = Cudd_bddAnd( mgr, ap, bp ) ;
  hcuddRef( tmp );
  hcuddRecursizeDeref( mgr, ap ) ;
  return tmp ;
}
DdNode *hcuddRawOr  ( DdNode *ap, WBddNode *bw ) 
{
  DdNode *bp = GetNode( bw ) ;
  DdManager *mgr = GetMgr ( bw ) ;

  DdNode *tmp = Cudd_bddOr( mgr, ap, bp ) ;
  hcuddRef( tmp ) ;
  hcuddRecursizeDeref( mgr, ap ) ;
  return tmp ;
}
DdNode *hcuddRawXor ( DdNode *ap, WBddNode *bw ) 
{
  DdNode *bp = GetNode( bw ) ;
  DdManager *mgr = GetMgr ( bw ) ;

  DdNode *tmp =  Cudd_bddXor( mgr, ap, bp ) ;
  hcuddRef( tmp ) ;
  hcuddRecursizeDeref( mgr, ap ) ;
  return tmp ;
}


/* computes aw < bw for given bit position,  where prev is the bdd representing the
   result from the least significant bit. 
   Note --  prev is de-referenced here  */
DdNode *hcuddRawULEBit( DdNode *prev, WBddNode *aw, WBddNode *bw )
{
  DdNode *ap = GetNode ( aw ) ;
  DdNode *bp = GetNode ( bw ) ;
  DdManager *mgr = GetMgr( aw ) ;

  DdNode *tmp, *t1, *t2, *t3 ;
  SAMEMANAGER( aw, bw )  ;
  
  /* tmp = (~A & B) | ( A == B ) & prev */
  t1 = Cudd_bddXnor ( mgr, ap, bp ) ;
  hcuddRef ( t1 ) ;

  t2 = Cudd_bddAnd ( mgr, t1, prev ) ;
  hcuddRef( t2 ) ;

  t3 = Cudd_bddAnd( mgr,  Cudd_Not( ap ), bp ) ;
  hcuddRef ( t3 ) ;

  tmp = Cudd_bddOr( mgr, t3, t2 ) ;
  hcuddRef( tmp ) ;

  hcuddRecursizeDeref( mgr, prev ) ;
  hcuddRecursizeDeref( mgr, t1 ) ;
  hcuddRecursizeDeref( mgr, t2 ) ;
  hcuddRecursizeDeref( mgr, t3 ) ;
  return tmp ;
}

/* Generates the sum or difference of aw, bw, and cin.  
   Note that cin is dereferenced here. */
DdNode *hcuddRawAddBit( Boolean bAddSub, DdNode *cin, WBddNode *aw, WBddNode *bw )
{
  DdNode *ap = GetNode ( aw ) ;
  DdNode *bp = bAddSub ? GetNode ( bw ) : Cudd_Not( GetNode (bw ) ) ;
  DdManager *mgr = GetMgr( aw ) ;

  DdNode *tmp, *t1 ;
  SAMEMANAGER( aw, bw )  ;

  t1 = Cudd_bddXor( mgr, ap, bp );
  hcuddRef( t1 );
  
  tmp = Cudd_bddXor( mgr, t1, cin ) ;
  hcuddRef( tmp ) ;

  hcuddRecursizeDeref( mgr, cin ) ;
  hcuddRecursizeDeref( mgr, t1 ) ;

  return tmp ;
}
/*  Generated the carry out from the addition of aw, bw and cin
    Note that cin is derferenced here.
*/
DdNode *hcuddRawCoutBit( Boolean bAddSub, DdNode *cin, WBddNode *aw, WBddNode *bw )
{
  DdNode *ap = GetNode ( aw ) ;
  DdNode *bp =  bAddSub ? GetNode ( bw ) : Cudd_Not( GetNode (bw ) ) ;
  DdManager *mgr = GetMgr( aw ) ;

  DdNode *tmp, *t1, *t2, *t3, *t4 ;
  SAMEMANAGER( aw, bw )  ;

  t1 = Cudd_bddAnd( mgr, ap, bp );
  hcuddRef( t1 );
  
  t2 = Cudd_bddAnd( mgr, ap, cin );
  hcuddRef( t2 );

  t3 = Cudd_bddAnd( mgr, bp, cin );
  hcuddRef( t3 );

  t4 = Cudd_bddOr( mgr, t1, t2 );
  hcuddRef( t4 );

  tmp = Cudd_bddOr( mgr, t4, t3 ) ;
  hcuddRef( tmp ) ;

  hcuddRecursizeDeref( mgr, cin ) ;
  hcuddRecursizeDeref( mgr, t1 ) ;
  hcuddRecursizeDeref( mgr, t2 ) ;
  hcuddRecursizeDeref( mgr, t3 ) ;
  hcuddRecursizeDeref( mgr, t4 ) ;

  return tmp ;
}

DdNode *hcuddReadOneRaw( WDdManager *pWMan )
{
  DdManager *pManager = GetFromWMan( pWMan ) ;
  DdNode *tmp = Cudd_ReadOne( pManager ) ;
  hcuddRef( tmp );
  return tmp ;
}
DdNode *hcuddReadZeroRaw( WDdManager *pWMan ) 
{
  DdManager *pManager = GetFromWMan( pWMan ) ;
  DdNode *tmp = Cudd_ReadLogicZero( pManager ) ;
  hcuddRef( tmp );
  return tmp ;
}

/*
  This function is used to "wrap" nodes for the Haskell Foreign Ptr interface. The use of the
  function is tranfoering ownership of the point from the caller to the wrapped node.   This is
  the reason for dereference call.
 */
WBddNode *hcuddToXBddPtr( WDdManager *pWMan, DdNode *node ) 
{
  DdManager *pManager = GetFromWMan( pWMan ) ;
  WBddNode *tmp = hcuddWrapNode ( node, pWMan ) ;
  hcuddRecursizeDeref( pManager, node ) ;
  return tmp ;
}


/* return the ratio of dag size / support ^(1.5)
   The use of this ratio is for heuristic estimates in prediciting bdd behavior.
 */
double hcuddDagRatio( WBddNode *aw ) 
{
  DdNode *ap = GetNode ( aw ) ;
  DdManager *mgr = GetMgr( aw ) ;
  double supportSize, dagSize, divider, ratio ;

  if (0 == Cudd_Regular(ap)) return 0.0 ;

  supportSize = (double) Cudd_SupportSize( mgr, ap );
  if ( supportSize <= 10.1 ) return 1.0 ;

  divider = supportSize < 22 ? pow( supportSize, 1.5 ) : 100.0 ;
  dagSize = (double) Cudd_DagSize( ap ) ;
  ratio = dagSize / divider ;
  return MAX( 1.0, ratio);

}

/* return the dag size  */
int hcuddDagSize( WBddNode *aw ) 
{
  DdNode *ap = GetNode ( aw ) ;

  if (0 == Cudd_Regular ( ap )) return 1 ;
  return Cudd_DagSize( ap ) ;
}

/* number of vars used */
int hcuddVarCount ( WDdManager *pWMan )
{
  DdManager *pMgr = pWMan->pManager ;
  return Cudd_ReadSize( pMgr );
 
}
