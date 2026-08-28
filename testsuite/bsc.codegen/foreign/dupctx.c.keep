#include <stdio.h>

/* Duplicate the low nsz bits of x: ret = {x, x} (2*nsz bits wide).
   Polymorphic BDPI arguments and results are passed as word pointers;
   this test keeps 2*nsz <= 32 so a single word suffices on each side. */
void bit_dup(unsigned int* ret, unsigned int* x, unsigned int nsz)
{
  unsigned int v = x[0] & ((nsz >= 32) ? ~0u : ((1u << nsz) - 1));
  ret[0] = (v << nsz) | v;
}
