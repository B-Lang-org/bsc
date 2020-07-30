#include <stdio.h>
#include <stdlib.h>

#define ENDCODE 12345  

typedef union {
  float fs;
  int us ;
} usingle ;

typedef union {
  double fd ;
  struct {
    int ud1;
    int ud2;
  } ud ;
} udouble ;


typedef struct {
  usingle ss;
  udouble dd;
}  BITS ;



static void addfp ( BITS a, BITS b, BITS c ) ;
static void addfpD ( BITS a, BITS b, BITS c ) ;
static void mulfp ( BITS a, BITS b, BITS c ) ;
static void mulfpD ( BITS a, BITS b, BITS c ) ;
static void macfp ( BITS a, BITS b, BITS c ) ;
static void macfpD ( BITS a, BITS b, BITS c ) ;

static void padfp();
static void padfpD();
static void padterfp();
static void padterfpD();

int main ( int argc, char *argv[] )
{
  double testdata[] = { (double) 1.0, 1.5, 1.5, 2.0, 4.0, 100.0, 1.0, 100.0, 0,
                       10.e8, 1.0, 10.e8, 10e4, 12345e3, 2.0, 3.0, 7e-7, 18e-9,
                       0.0, 0.0, 1.0, 255.0, 0.0,
                       -3.0, 1.0, -3.0, -2.0, 0.0 , -32.0, 31.5, -31.4999566, 0.0, 
                       1.9999999, 2.9999997, 0.0000002 , 3.0, ENDCODE } ;

  BITS a, b, c, out ;
  void (*fun_ptr)(BITS, BITS, BITS)  ; /* pointer to test generator function */
  void (*pad_ptr)(); /* pointer to padding function */
  int add_mul ;
  double *ptest ;

  // Some initial data 
  a.ss.fs = 1.0 ; a.dd.fd = 1.0 ;
  b.ss.fs = 1.5 ; b.dd.fd = 1.0 ;
  c.ss.fs = 6.5 ; c.dd.fd = 6.5 ;
  add_mul = 0 ;

  if ( argc != 2 )
    {
      printf( "Need 1 argument add-- 0 or mult-- 1 or mac -- 2.\n" );
      exit ( -1 ) ;             
    }
  add_mul = atoi( argv[1] ) ;


  if ( 0 ==  add_mul )
    {
      printf( "// adden triples a + b = sum\n" );
      fun_ptr = addfp ;
      pad_ptr = padfp;
    }
  else if ( 1 == add_mul ) 
    {
      printf( "// product triples a * b = prod \n" );
      fun_ptr = mulfp ;
      pad_ptr = padfp;
    }
  else if ( 2 == add_mul ) 
    {
      printf( "// product triples a * b + c = prod \n" );
      fun_ptr = macfp ;
      pad_ptr = padterfp;
    }
  else if ( 3 == add_mul ) 
    {
      printf( "// product triples a + b = prod \n" );
      fun_ptr = addfpD ;
      pad_ptr = padfpD;
    }
  else if ( 4 == add_mul ) 
    {
      printf( "// product triples a * b = prod \n" );
      fun_ptr = mulfpD ;
      pad_ptr = padfpD;
    }
  else if ( 5 == add_mul ) 
    {
      printf( "// product triples a * b +c = prod \n" );
      fun_ptr = macfpD ;
      pad_ptr = padterfpD;
    }
  else
    {
      printf( "bad argument  should be 0, 1, or 2" );
      exit ( -1 ) ;
    }

  // make sure the data file has 128 entries so there are no warnings
  int i = 128;
  for (ptest = testdata ; ENDCODE != *ptest ; ptest ++ )
    {
      a.ss.fs = *ptest ;
      a.dd.fd = *ptest ;

      fun_ptr( a, b, c ) ;

      c = b ;
      b = a ;
      i--;
    }

  for(; i > 0; i--) {
    pad_ptr();
  }
}

// Test function for add
static void addfp ( BITS a, BITS b, BITS c ) 
{
  BITS res;
  res.ss.fs = (a.ss.fs + b.ss.fs ) ;
  printf( "%08x_%08x_%08x // %g %g %g \n",
          a.ss.us, b.ss.us, res.ss.us,
          a.ss.fs, b.ss.fs, res.ss.fs );
  
}

// padding function for single-precision
static void padfp()
{
  printf("AAAAAAAA_AAAAAAAA_AAAAAAAA // padding\n");
}

static void addfpD ( BITS a, BITS b, BITS c ) 
{
  BITS res;
  res.dd.fd = (a.dd.fd + b.dd.fd ) ;
  printf( "%08x%08x_%08x%08x_%08x%08x // %g %g %g \n",
          a.dd.ud.ud2, a.dd.ud.ud1, 
          b.dd.ud.ud2, b.dd.ud.ud1, 
          res.dd.ud.ud2, res.dd.ud.ud1, 
          a.dd.fd, b.dd.fd, res.dd.fd );
  
}


// padding function for double-precision
static void padfpD()
{
  printf("AAAAAAAAAAAAAAAA_AAAAAAAAAAAAAAAA_");
  printf("AAAAAAAAAAAAAAAA // padding\n");
}

static void mulfpD ( BITS a, BITS b, BITS c ) 
{
  BITS res;
  res.dd.fd = (a.dd.fd * b.dd.fd ) ;
  printf( "%08x%08x_%08x%08x_%08x%08x // %g %g %g \n",
          a.dd.ud.ud2, a.dd.ud.ud1, 
          b.dd.ud.ud2, b.dd.ud.ud1, 
          res.dd.ud.ud2, res.dd.ud.ud1, 
          a.dd.fd, b.dd.fd, res.dd.fd );  
}

static void macfpD ( BITS a, BITS b, BITS c ) 
{
  BITS res;
  res.dd.fd = (a.dd.fd * b.dd.fd ) + c.dd.fd ;
  printf( "%08x%08x_%08x%08x_%08x%08x_%08x%08x // %g %g %g %g\n",
          a.dd.ud.ud2, a.dd.ud.ud1, 
          b.dd.ud.ud2, b.dd.ud.ud1, 
          c.dd.ud.ud2, c.dd.ud.ud1, 
          res.dd.ud.ud2, res.dd.ud.ud1, 
          a.dd.fd, b.dd.fd, c.dd.fd, res.dd.fd );
  
}


// padding function for double-precision
static void padterfpD()
{
  printf("AAAAAAAAAAAAAAAA_AAAAAAAAAAAAAAAA_");
  printf("AAAAAAAAAAAAAAAA_AAAAAAAAAAAAAAAA // padding\n");
}


// Test function for mult
static void mulfp ( BITS a, BITS b, BITS c ) 
{
  BITS res;
  res.ss.fs = (a.ss.fs * b.ss.fs ) ;
  printf( "%08x_%08x_%08x // %g %g %g \n",
          a.ss.us, b.ss.us, res.ss.us,
          a.ss.fs, b.ss.fs, res.ss.fs );
  
}

// Test function for mult and add (mac)  a*b + c 
static void macfp ( BITS a, BITS b, BITS c ) 
{
  BITS res;
  res.ss.fs = (a.ss.fs * b.ss.fs ) + c.ss.fs ;
  printf( "%08x_%08x_%08x_%08x // %g %g %g %g \n",
          a.ss.us, b.ss.us, c.ss.us, res.ss.us,
          a.ss.fs, b.ss.fs, c.ss.fs, res.ss.fs );

  
}

// padding for a ternary single-precision function
static void padterfp() {
  printf("AAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA // padding\n");
}
