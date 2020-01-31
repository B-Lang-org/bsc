#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "bdpi.h"

// -------------------------

#define BYTES_PER_WORD (sizeof(unsigned int))
#define BITS_PER_WORD  (8 * BYTES_PER_WORD)

#define DEBUG_VPI_MEM 0
#define DEBUG_VPI_SIM 0

static void* debug_vpi_malloc(size_t sz, unsigned int count, const char* desc)
{
  void* ptr = malloc(sz*count);
#if DEBUG_VPI_MEM
  if (desc)
    printf("%p: alloced %0d x %0d (%0d bytes) (%s)\n", ptr, (unsigned int) sz, count, (unsigned int) (sz*count), desc);
  else
    printf("%p: alloced %0d x %0d (%0d bytes)\n", ptr, (unsigned int) sz, count, (unsigned int) (sz*count));
  fflush(NULL);
#endif
  return ptr;
}

static void debug_vpi_free(void* ptr, const char* desc)
{
#if DEBUG_VPI_MEM
  if (desc)
    printf("%p: freed (%s)\n", ptr, desc);
  else
    printf("%p: freed\n", ptr);
  fflush(NULL);
#endif
  free(ptr);
}

typedef struct tMemBlock tMemBlock;
struct tMemBlock
{
  tMemBlock* next;
  void*      mem;
};

/* used to record allocated argument memory */
static tMemBlock* allocated_args = NULL;

static unsigned int num_words(unsigned int nBits)
{
  return (nBits + BITS_PER_WORD - 1) / BITS_PER_WORD;
}

static unsigned int num_chars(unsigned int nBits)
{
  return (nBits + 7) / 8;
}

/* allocate memory for an argument and store a pointer to it */
static void* alloc_arg(unsigned int nBits)
{
  void* ptr = debug_vpi_malloc(BYTES_PER_WORD, num_words(nBits), "argument words");
  tMemBlock* block = (tMemBlock*) debug_vpi_malloc(sizeof(tMemBlock), 1, "tMemBlock");

  block->next    = allocated_args;
  block->mem     = ptr;
  allocated_args = block;

  return ptr;
}

static s_vpi_vecval* make_vecval(int bits)
{
  void* ptr = debug_vpi_malloc(sizeof(s_vpi_vecval), num_words(bits), "s_vpi_vecval");
  return (s_vpi_vecval*) ptr;
}

// -------------------------

typedef enum { CVC, MODELSIM, NCSIM, VCS, ICARUS, UNKNOWN, UNSET } tSimulator;

static tSimulator theSim = UNSET;

static tSimulator get_vpi_simulator()
{

  if (theSim == UNSET) {
    s_vpi_vlog_info vli;

    if (0 == vpi_get_vlog_info (&vli) ) {
      fprintf (stderr, "Error: Could not access verilog info.\n" );
      exit(1);
    }

    int matches;
    char ignore[1024], name[1024];

    if (theSim == UNSET) {
      matches = sscanf(vli.product, "%s %s %s %s", (char *) ignore, (char *) ignore, (char *) name, (char *) ignore);
      if (matches == 4 && strcmp(name,"VCS") == 0) {
#if DEBUG_VPI_MEM
	fprintf(stderr, "Info: Simulator is vcs.\n");
#endif
	theSim = VCS;
      }
    }

    if (theSim == UNSET) {
      matches = sscanf(vli.product, "%s %s %s", (char *) name, (char *) ignore, (char *) ignore);
      if (matches == 3 && strcmp(name,"CVC") == 0) {
#if DEBUG_VPI_MEM
	fprintf(stderr, "Info: Simulator is cvc.\n");
#endif
	theSim = CVC;
      }
      if (matches == 3 && strcmp(name,"ModelSim") == 0) {
#if DEBUG_VPI_MEM
	fprintf(stderr, "Info: Simulator is modelsim.\n");
#endif
	theSim = MODELSIM;
      }
      if (matches == 1 && strcmp(name,"ncsim") == 0) {
#if DEBUG_VPI_MEM
	fprintf(stderr, "Info: Simulator is ncsim.\n");
#endif
	theSim = NCSIM;
      }
      if (matches == 1 && strcmp(name,"ncsim(64)") == 0) {
#if DEBUG_VPI_MEM
	fprintf(stderr, "Info: Simulator is ncsim.\n");
#endif
	theSim = NCSIM;
      }
      if (matches == 2 && strcmp(name,"Icarus") == 0) {
#if DEBUG_VPI_MEM
	fprintf(stderr, "Info: Simulator is icarus.\n");
#endif
	theSim = ICARUS;
      }
    }

    if (theSim == UNSET) {
#if DEBUG_VPI_MEM
      fprintf(stderr, "Info: Simulator is unknown.\n");
#endif
      theSim = UNKNOWN;
    }
  }

  return theSim;
}

// -------------------------

/* allocate storage for a result, if needed */
void make_vpi_result(vpiHandle hdl, void* ptr, tPtrType type)
{
  /* get the size of the argument */
  PLI_INT32 bits = vpi_get(vpiSize, hdl);

  if (bits > 64 || type == POLYMORPHIC)
  {
    /* ptr will be an unsigned int**, and we should allocate memory */
    unsigned int** ptr_typed = (unsigned int**) ptr;
    *ptr_typed = (unsigned int*) debug_vpi_malloc(BYTES_PER_WORD, num_words(bits), "result words");
  }
  else
  {
    /* no allocation is required */
  }
}

// -------------------------

/* copy a value from the Verilog side, allocating storage if required */
void get_vpi_arg(vpiHandle hdl, void* ptr, tPtrType type)
{
  const unsigned long long mask32 = (1llu << 32) - 1;
  s_vpi_value vpi_value_buf;

  /* get the size of the argument */
  PLI_INT32 bits = vpi_get(vpiSize, hdl);

  if (type == STRING)
  {

    tSimulator sim = get_vpi_simulator();

    if (vpi_get(vpiType, hdl) != vpiConstant && vpi_get(vpiType, hdl) != vpiParameter) {
      bits = bits * 8;
    }

    if (vpi_get(vpiType, hdl) == vpiParameter && sim == VCS) {
      bits = (bits - 1) * 8;
    }

    char** ptr_typed = (char**) ptr;

    /* allocate a string and copy it from the Verilog */
    char* str = (char*) alloc_arg(bits+8);
    vpi_value_buf.format = vpiStringVal;
    vpi_get_value(hdl, &vpi_value_buf);
    if (bits == 8 && vpi_get(vpiType, hdl) == vpiParameter && vpi_value_buf.value.str[0] == ' ') {
      bits = 0;
    }
    strncpy(str, vpi_value_buf.value.str, num_chars(bits));
    str[num_chars(bits)] = '\0';
    *ptr_typed = str;
  }
  else if (bits > 64 || type == POLYMORPHIC)
  {
    /* ptr will be an unsigned int** */
    unsigned int** ptr_typed = (unsigned int**) ptr;

    /* allocate an unsigned int array */
    unsigned int* data = (unsigned int*) alloc_arg(bits);
    if (bits == 1)
    {
      /* copy from a single bit */
      vpi_value_buf.format = vpiScalarVal;
      vpi_get_value(hdl, &vpi_value_buf);
      data[0] = (vpi_value_buf.value.scalar == vpi1) ? 1 : 0;
    }
    else
    {
      /* copy from a vector */
      int count = bits;
      int idx = 0;
      vpi_value_buf.format = vpiVectorVal;
      vpi_get_value(hdl, &vpi_value_buf);
      while (count > 0)
      {
	unsigned int mask    = (count < 32) ? ((1 << count) - 1) : ~0;
        unsigned int val     = vpi_value_buf.value.vector[idx].aval;
        unsigned int unknown = vpi_value_buf.value.vector[idx].bval;
	data[idx] = mask & ((val & ~unknown) | (0xAAAAAAAA & unknown));
	count -= 32;
	++idx;
      }
    }
    *ptr_typed = data;
  }
  else if (bits > 32)
  {
    /* ptr will be an unsigned long long* */
    unsigned long long* ptr_typed = (unsigned long long*) ptr;

    /* no need to allocate, just construct a value */
    unsigned long long mask = (bits < 64) ? ((1llu << bits) - 1llu) : ~0llu;
    unsigned long long val;
    unsigned long long unknown;
    vpi_value_buf.format = vpiVectorVal;
    vpi_get_value(hdl, &vpi_value_buf);
    val = (unsigned long long) vpi_value_buf.value.vector[1].aval;
    val = val << 32;
    val |= ((unsigned long long) vpi_value_buf.value.vector[0].aval) & mask32;
    unknown = (unsigned long long) vpi_value_buf.value.vector[1].bval;
    unknown = unknown << 32;
    unknown |= ((unsigned long long) vpi_value_buf.value.vector[0].bval) & mask32;
    *ptr_typed = mask & ((val & ~unknown) | (0xAAAAAAAAAAAAAAAAllu & unknown));
  }
  else if (bits > 8)
  {
    /* ptr will be an unsigned int* */
    unsigned int* ptr_typed = (unsigned int*) ptr;

    /* no need to allocate, just construct a value */
    unsigned int mask = (bits < 32) ? ((1 << bits) - 1) : ~0;
    unsigned int val;
    unsigned int unknown;
    vpi_value_buf.format = vpiVectorVal;
    vpi_get_value(hdl, &vpi_value_buf);
    val = vpi_value_buf.value.vector[0].aval;
    unknown = vpi_value_buf.value.vector[0].bval;
    *ptr_typed = mask & ((val & ~unknown) | (0xAAAAAAAA & unknown));
  }
  else if (bits > 1)
  {
    /* ptr will be a char* */
    char* ptr_typed = (char*) ptr;

    /* no need to allocate, just construct a value */
    unsigned int mask = (bits < 32) ? ((1 << bits) - 1) : ~0;
    unsigned int val;
    unsigned int unknown;
    vpi_value_buf.format = vpiVectorVal;
    vpi_get_value(hdl, &vpi_value_buf);
    val = vpi_value_buf.value.vector[0].aval;
    unknown = vpi_value_buf.value.vector[0].bval;
    *ptr_typed = (char) (mask & ((val & ~unknown) | (0xAAAAAAAA & unknown)));
  }
  else
  {
    /* ptr will be a char* */
    char* ptr_typed = (char*) ptr;

    /* no need to allocate, just construct a value */
    vpi_value_buf.format = vpiScalarVal;
    vpi_get_value(hdl, &vpi_value_buf);
    *ptr_typed = (vpi_value_buf.value.scalar == vpi1) ? 1 : 0;
  }
}

// -------------------------

/* copy a return value back to the Verilog side and free the storage */
void put_vpi_result(vpiHandle hdl, void* ptr, tPtrType type)
{
  s_vpi_value vpi_value_buf;
  s_vpi_vecval* data = NULL;

  /* get the size of the argument */
  PLI_INT32 bits = vpi_get(vpiSize, hdl);

  if (bits > 64 || type == POLYMORPHIC)
  {
    /* ptr will be an unsigned int** */
    unsigned int** ptr_typed = (unsigned int**) ptr;

    if (bits == 1)
    {
      vpi_value_buf.format = vpiScalarVal;
      vpi_value_buf.value.scalar = (**ptr_typed & 0x01) ? vpi1 : vpi0;
    }
    else
    {
      int count = bits;
      int idx = 0;
      vpi_value_buf.format = vpiVectorVal;
      data = make_vecval(bits);
      while (count > 0)
      {
	unsigned int mask = (count < 32) ? ((1 << count) - 1) : ~0;
	data[idx].aval = (*ptr_typed)[idx] & mask;
	data[idx].bval = 0;
	count -= 32;
	++idx;
      }
      vpi_value_buf.value.vector = data;
    }
  }
  else if (bits > 32)
  {
    /* ptr will be an unsigned long long* */
    unsigned long long* ptr_typed = (unsigned long long*) ptr;

    unsigned long long mask = (bits < 64) ? ((1llu << bits) - 1llu) : ~0llu;
    vpi_value_buf.format = vpiVectorVal;
    data = make_vecval(bits);
    data[0].aval = (unsigned int) ((*ptr_typed & mask) & 0xFFFFFFFFllu);
    data[0].bval = 0;
    data[1].aval = (unsigned int) (((*ptr_typed & mask) >> 32) & 0xFFFFFFFFllu);
    data[1].bval = 0;
    vpi_value_buf.value.vector = data;
  }
  else if (bits > 8)
  {
    /* ptr will be an unsigned int* */
    unsigned int* ptr_typed = (unsigned int*) ptr;

    unsigned int mask = (bits < 32) ? ((1 << bits) - 1) : ~0;
    vpi_value_buf.format = vpiVectorVal;
    data = make_vecval(bits);
    data[0].aval = *ptr_typed & mask;
    data[0].bval = 0;
    vpi_value_buf.value.vector = data;
  }
  else if (bits > 1)
  {
    /* ptr will be a char* */
    char* ptr_typed = (char*) ptr;

    unsigned int mask = (bits < 32) ? ((1 << bits) - 1) : ~0;
    vpi_value_buf.format = vpiVectorVal;
    data = make_vecval(bits);
    data[0].aval = *ptr_typed & mask;
    data[0].bval = 0;
    vpi_value_buf.value.vector = data;
  }
  else
  {
    /* ptr will be a char* */
    char* ptr_typed = (char*) ptr;

    vpi_value_buf.format = vpiScalarVal;
    vpi_value_buf.value.scalar = (*ptr_typed & 0x01) ? vpi1 : vpi0;
  }

  vpi_put_value(hdl, &vpi_value_buf, NULL, vpiNoDelay);

  if (data)
    debug_vpi_free(data, "from make_vecval");
  if (bits > 64 || type == POLYMORPHIC)
  {
    /* ptr will be an unsigned int**, and we should free the memory */
    unsigned int** ptr_typed = (unsigned int**) ptr;
    debug_vpi_free(*ptr_typed, "result words");
  }
}

// -------------------------

/* free all storage allocated by get_vpi_arg() */
void free_vpi_args(void)
{
  while (allocated_args)
  {
    tMemBlock* block = allocated_args;
    allocated_args = block->next;
    debug_vpi_free(block->mem, "argument words");
    debug_vpi_free(block, "tMemBlock");
  }
}

// -------------------------
