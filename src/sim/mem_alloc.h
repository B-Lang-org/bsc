#ifndef __MEM_ALLOC_H__
#define __MEM_ALLOC_H__

// call before any alloc_mem/free_mem
void init_mem_allocator();

// call after all alloc_mem/free_mem
void shutdown_mem_allocator();

void* alloc_mem(unsigned int nWords);

void free_mem(void* ptr, unsigned int nWords);

#endif /* __MEM_ALLOC_H__ */
