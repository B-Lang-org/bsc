#include "HsFFI.h"

#include "stdio.h"
#include "stdlib.h"

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 703)
#include "Rts.h"
#endif

#include "haskellInt.h"


//  initialization of the haskell runtime system 
int init_haskellSystem(int *argc, char **argv[])
{
  int status;

  // Iniialize the haskell system
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 703)
  RtsConfig conf = defaultRtsConfig;
  conf.rts_opts_enabled = RtsOptsAll;
  hs_init_ghc(argc, argv, conf);
#else
  hs_init(argc, argv);
#endif

  // register haskell exit function
  status = atexit ( hs_exit );

  return status;
}


