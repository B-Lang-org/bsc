/*
 * Almost all primitive operations are defined
 * static inline in bs_prim_ops.h
 *
 * This file contains just the implementation of
 * functions which manage copies of arguments to
 * foreign functions.
 */

#include <vector>
#include <string>
#include <cstring>

#include "bluesim_types.h"
#include "bs_mem_defines.h"
#include "mem_alloc.h"

// Used internally to record argument copies which have been
// allocated but not yet released.
static std::vector<unsigned int*> argument_copies_uint;
static std::vector<unsigned int>  argument_sizes_uint;
static std::vector<char*>         argument_copies_char;
static std::vector<unsigned int>  argument_sizes_char;

// Records the current return argument
static unsigned int* current_return_data = NULL;

// Copy a small argument (used with polymorphic arguments <= 8 bits)
unsigned int* copy_arg(const tUInt8* data, unsigned int /* n */)
{
  unsigned int* copy = (unsigned int*) alloc_mem(1);
  argument_copies_uint.push_back(copy);
  argument_sizes_uint.push_back(1);
  copy[0] = (unsigned int) (*data);
  return copy;
}

// Copy a word argument (used with polymorphic arguments <= 32 bits)
unsigned int* copy_arg(const tUInt32* data)
{
  unsigned int* copy = (unsigned int*) alloc_mem(1);
  argument_copies_uint.push_back(copy);
  argument_sizes_uint.push_back(1);
  copy[0] = (unsigned int) (*data);
  return copy;
}

// Copy a small argument (used with polymorphic arguments <= 64 bits)
unsigned int* copy_arg(const tUInt64* data, unsigned int /* n */)
{
  unsigned int* copy = (unsigned int*) alloc_mem(2);
  argument_copies_uint.push_back(copy);
  argument_sizes_uint.push_back(2);
  copy[0] = (unsigned int) (*data);
  copy[1] = (unsigned int) ((*data) >> 32);
  return copy;
}

// Copy an array of unsigned ints (used with wide data, polymorphic or not)
unsigned int* copy_arg(const unsigned int* data, unsigned int n)
{
  unsigned int* copy = (unsigned int*) alloc_mem(n);
  argument_copies_uint.push_back(copy);
  argument_sizes_uint.push_back(n);
  memcpy(copy, data, n * sizeof(unsigned int));
  return copy;
}

// Copy a string argument
char* copy_arg(const std::string& str)
{
  unsigned int n = (str.length() / BYTES_PER_WORD) + 1;
  char* copy = (char*) alloc_mem(n);
  argument_copies_char.push_back(copy);
  argument_sizes_char.push_back(n);
  strcpy(copy, str.c_str());
  return copy;
}

// Allocate an unitialized temporary array
unsigned int* ignore_arg(unsigned int n)
{
  unsigned int* arg = (unsigned int*) alloc_mem(n);
  argument_copies_uint.push_back(arg);
  argument_sizes_uint.push_back(n);
  current_return_data = NULL;
  return arg;
}

unsigned int* return_arg(unsigned int n)
{
  unsigned int* arg = (unsigned int*) alloc_mem(n);
  argument_copies_uint.push_back(arg);
  argument_sizes_uint.push_back(n);
  current_return_data = arg;
  return arg;
}

// Copy data from current_return_data back to the result
tUInt8  write_return(unsigned int unused, tUInt8* data)
{
  *data = (tUInt8) (current_return_data[0] & 0xFF);
  return *data;
}

tUInt32 write_return(unsigned int unused, tUInt32* data)
{
  *data = (tUInt32) (current_return_data[0]);
  return *data;
}

tUInt64 write_return(unsigned int unused, tUInt64* data)
{
  *data = ((tUInt64) current_return_data[0]);
  *data |= ((tUInt64) current_return_data[1]) << 32;
  return *data;
}

// Delete all of the currently allocated argument copies
void delete_arg_copies()
{
  std::vector<unsigned int*>::iterator u = argument_copies_uint.begin();
  std::vector<unsigned int>::iterator  s = argument_sizes_uint.begin();
  while (u != argument_copies_uint.end())
  {
    unsigned int* ptr = *(u++);
    unsigned int  n = *(s++);
    free_mem(ptr, n);
  }

  std::vector<char*>::iterator c = argument_copies_char.begin();
  s = argument_sizes_char.begin();
  while (c != argument_copies_char.end())
  {
    char* ptr = *(c++);
    unsigned int  n = *(s++);
    free_mem(ptr, n);
  }

  argument_copies_uint.clear();
  argument_sizes_uint.clear();
  argument_copies_char.clear();
  argument_sizes_char.clear();
}
