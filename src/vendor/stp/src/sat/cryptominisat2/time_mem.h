/****************************************************************************************[Solver.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef TIME_MEM_H
#define TIME_MEM_H

#ifdef _WIN32
  #ifndef WIN32_LEAN_AND_MEAN
    #define WIN32_LEAN_AND_MEAN
  #endif
  #include <windows.h>
  // Include windows.h first
  #include <psapi.h>
#else
  #include <sys/time.h>
  #include <sys/resource.h>
  #include <unistd.h>
#endif
#include <cstdint>
#include <realtimeapiset.h>

namespace MINISAT
{
using namespace MINISAT;

/*************************************************************************************/
#ifdef _WIN32
static inline double cpuTime(void) {
    constexpr uint64_t FILETIME_to_s = 1e7; // 100 ns / FILETIME
    FILETIME creationTime, undefined, kernelTime, userTime;
    if (GetProcessTimes(GetCurrentProcess(), &creationTime, &undefined
                                                     , &kernelTime, &userTime) == 0) { 
        return 0;
    }
    return (double)(userTime.dwLowDateTime | ((uint64_t)userTime.dwHighDateTime << 32)) / FILETIME_to_s; }
#else
static inline double cpuTime(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }
#endif


#ifdef _WIN32

static inline uint64_t memUsed() {
    PROCESS_MEMORY_COUNTERS pmc;
    auto err = GetProcessMemoryInfo(GetCurrentProcess(), &pmc, sizeof(pmc));
    if (err == 0) return 0;
    return pmc.WorkingSetSize;
}

#elif defined(__linux__)

static inline int memReadStat(int field)
{
    char    name[256];
    pid_t pid = getpid();
    sprintf(name, "/proc/%d/statm", pid);
    FILE*   in = fopen(name, "rb");
    if (in == NULL) return 0;
    int     value;
    for (; field >= 0; field--)
        fscanf(in, "%d", &value);
    fclose(in);
    return value;
}

static inline uint64_t memUsed() { return (uint64_t)memReadStat(0) * (uint64_t)getpagesize(); }

#elif defined(__FreeBSD__)

static inline uint64_t memUsed(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return ru.ru_maxrss*1024; 
}

#else

static inline uint64_t memUsed() { return 0; }

#endif

#if defined(__linux__)
#include <fpu_control.h>
#endif

};

#endif //TIME_MEM_H
