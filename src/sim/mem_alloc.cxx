#include <cstdlib>
#include <algorithm>

#define MAX_CHUNK_WORDS 16

// superimpose this structure on allocated memory to create a free list structure
typedef struct tMemHeader tMemHeader;
struct tMemHeader
{
  tMemHeader* next;
};

static bool is_active = false;
static tMemHeader* free_list[MAX_CHUNK_WORDS+1];

void init_mem_allocator()
{
  if (!is_active)
  {
    for (unsigned int i = 0; i < MAX_CHUNK_WORDS; ++i)
      free_list[i] = NULL;
    is_active = true;
  }
}

void shutdown_mem_allocator()
{
  if (is_active)
  {
    for (unsigned int i = 0; i < MAX_CHUNK_WORDS; ++i)
    {
      tMemHeader* mem = free_list[i];
      while (mem)
      {
	tMemHeader* next = mem->next;
	delete[] mem;
	mem = next;
      }
      free_list[i] = NULL;
    }
    is_active = false;
  }
}

void* alloc_mem(unsigned int nWords)
{
  static unsigned int min_words = (sizeof(tMemHeader) + sizeof(unsigned int) - 1) / sizeof(unsigned int);
  if ((nWords > MAX_CHUNK_WORDS) || (free_list[nWords] == NULL))
  {
    return new unsigned int[std::max(nWords,min_words)];
  }
  else
  {
    tMemHeader* ret = free_list[nWords];
    free_list[nWords] = ret->next;
    return (void*)ret;
  }
}

void free_mem(void* ptr, unsigned int nWords)
{
  if (nWords > MAX_CHUNK_WORDS)
    delete[] ((unsigned int*)ptr);
  else if (ptr != NULL)
  {
    tMemHeader* mem = (tMemHeader*) ptr;
    mem->next = free_list[nWords];
    free_list[nWords] = mem;
  }
}
