#include <cstdlib>

#include "rand32.h"

extern "C" unsigned int rand32 ()
{
  unsigned int res;
  res = (unsigned int)random();
  return res;
}
