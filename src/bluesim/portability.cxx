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
  // Since multiple bluesim processes may be running at the same time, we need
  // to use a name that is unique to this process.
  char* name;
  asprintf(&name, "/bsim_arbitrary_sem_name_%05d", getpid());
  // Remove the semaphore if it already exists.  It should not exist, but just
  // in case it does, we want to remove it so that we can create it.
  sem_unlink(name);
  // create the semaphore
  tSemaphore* semaphore = sem_open( name
                                  , O_CREAT | O_EXCL
                                  , S_IRUSR | S_IWUSR
                                  , 0 );
  if (semaphore == SEM_FAILED)
  {
    perror("sem_open");
    semaphore = NULL;
  }
  // Unlink the semaphore to get rid of the name.  The underlying semaphore will
  // continue to exist as long as there are open handles to it, but we don't
  // wan't to keep the name around.
  sem_unlink(name);
  free(name);
  return semaphore;
}

void release_semaphore(tSemaphore* semaphore)
{
  if (semaphore == NULL) return;
  sem_close(semaphore);
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

void release_semaphore(tSemaphore* semaphore)
{
  if (semaphore == NULL) return;
  sem_destroy(semaphore);
  free(semaphore);
}

#endif /* USE_NAMED_SEMAPHORES */

/*
 * Common implementation for both named and unnamed semaphores.
 */

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

