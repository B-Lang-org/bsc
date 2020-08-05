/* This file contains definitions of utility functions
 * which enhance code portability.
 */
#include <cstdarg>
#include <cstdlib>
#include <cstdio>
#include <errno.h>
#include <unistd.h>

#include "portability.h"

/* exponentiation on unsigned ints */
unsigned long long powll(unsigned int base, unsigned int exp)
{
  if (exp == 0)  return 1llu;
  if (base == 0) return 0llu;

  unsigned long long ret = 1;
  unsigned long long m = base;
  while (exp > 0)
  {
    if (exp & 1) ret *= m;
    exp = exp >> 1;
    m = m * m;
  }

  return ret;
}


// re-implement asprintf using only C99 features
// must be specifically marked as not throwing exceptions
// in order to not conflict with glibc's asprintf prototype
int new_asprintf(char **strp, const char* fmt, ...) throw()
{
  va_list ap1, ap2;

  va_start(ap1,fmt);
  va_copy(ap2,ap1);

  size_t output_chars = vsnprintf(NULL, 0, fmt, ap1);
  va_end(ap1);

  // add space for the terminating null
  size_t output_size = output_chars + 1;

  char* output_buffer = (char*) malloc(output_size);

  int result = vsnprintf(output_buffer, output_size, fmt, ap2);
  va_end(ap2);

  if (result != -1) {
    *strp = output_buffer;
  }
  else {
    free(strp);
  }

  return(result);
}

/* portable semaphore facade */

#if USE_NAMED_SEMAPHORES

/*
 * Implementation using named semaphores.
 */

tSemaphore* create_semaphore()
{
  // allocate semaphore struct
  tSemaphore* semaphore = (tSemaphore*) malloc(sizeof(tSemaphore));
  if (semaphore == NULL)
  {
    perror("malloc");
    return NULL;
  }

  // allocate space for the name
  semaphore->name = (char*) malloc(14);
  if (semaphore->name == NULL)
  {
    perror("malloc");
    free(semaphore);
    return NULL;
  }

  // choose a unique name
  static int seq_number = 0;
  sprintf(semaphore->name, "/bsim%05d%03d", getpid(), seq_number++);

  // create the semaphore
  semaphore->sem = sem_open( semaphore->name
                           , O_CREAT | O_EXCL
                           , S_IRUSR | S_IWUSR
                           , 0 );
  if (semaphore->sem == SEM_FAILED)
  {
    perror("sem_open");
    free(semaphore->name);
    free(semaphore);
    return NULL;
  }

  return semaphore;
}

void post_semaphore(tSemaphore* semaphore)
{
  if (semaphore != NULL)
    sem_post(semaphore->sem);
}

void trywait_on_semaphore(tSemaphore* semaphore)
{
  if (semaphore == NULL) return;

  while ((sem_trywait(semaphore->sem) != 0) && (errno == EINTR));
}

void wait_on_semaphore(tSemaphore* semaphore)
{
  if (semaphore == NULL) return;

  while ((sem_wait(semaphore->sem) != 0) && (errno == EINTR));
}

void release_semaphore(tSemaphore* semaphore)
{
  if (semaphore == NULL) return;
  sem_close(semaphore->sem);
  sem_unlink(semaphore->name);
  free(semaphore->name);
  free(semaphore);
}

#else /* USE_NAMED_SEMAPHORES */

/*
 * Implementation using unnamed semaphores.
 */

tSemaphore* create_semaphore()
{
  // allocate semaphore struct
  tSemaphore* semaphore = (tSemaphore*) malloc(sizeof(tSemaphore));
  if (semaphore == NULL)
  {
    perror("malloc");
    return NULL;
  }

  // initialize the semaphore
  if (sem_init(semaphore, 0, 0) != 0)
  {
    perror("sem_init");
    free(semaphore);
    return NULL;
  }

  return semaphore;
}

void post_semaphore(tSemaphore* semaphore)
{
  if (semaphore != NULL)
    sem_post(semaphore);
}

void trywait_on_semaphore(tSemaphore* semaphore)
{
  if (semaphore == NULL) return;

  while ((sem_trywait(semaphore) != 0) && (errno == EINTR)) {} ;
}

void wait_on_semaphore(tSemaphore* semaphore)
{
  if (semaphore == NULL) return;

  while ((sem_wait(semaphore) != 0) && (errno == EINTR)) {};
}

void release_semaphore(tSemaphore* semaphore)
{
  if (semaphore == NULL) return;
  sem_destroy(semaphore);
  free(semaphore);
}

#endif
