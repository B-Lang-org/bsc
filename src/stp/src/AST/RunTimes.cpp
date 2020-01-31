//Hold the runtime statistics. E.g. how long was spent in simplification.
//The times don't add up to the runtime, because we allow multiple times to
//be counted simultaneously. For example, the current Transform()s call
//Simplify_TopLevel, so inside simplify time will be counted towards both
//Simplify_TopLevel & Transform.

// This is intended as a low overhead profiling class. So runtimes can
// always be tracked.

#include <cassert>
#include <sys/time.h>
#include <sstream>
#include <iostream>
#include <utility>
#include "RunTimes.h"
#include "../sat/utils/System.h"

// BE VERY CAREFUL> Update the Category Names to match.
std::string RunTimes::CategoryNames[] = { "Transforming", "Simplifying", "Parsing", "CNF Conversion", "Bit Blasting", "SAT Solving", "Bitvector Solving","Variable Elimination", "Sending to SAT Solver", "Counter Example Generation","SAT Simplification", "Constant Bit Propagation","Array Read Refinement", "Applying Substitutions", "Removing Unconstrained", "Pure Literals" , "ITE Contexts", "AIG core simplification", "Interval Propagation", "Always True"};

namespace BEEV
{
  void FatalError(const char * str);
}


long RunTimes::getCurrentTime()
{
  timeval t;
  gettimeofday(&t, NULL);
  return (1000 * t.tv_sec) + (t.tv_usec / 1000);
}

void RunTimes::print()
{
  if (0 !=  category_stack.size())
    {
      std::cerr << "size:" <<  category_stack.size() << std::endl;
      std::cerr << "top:" << CategoryNames[category_stack.top().first] << std::endl;
      BEEV::FatalError("category stack is not yet empty!!");
    }

  std::ostringstream result;
  result << "statistics\n";
  std::map<Category, int>::const_iterator it1 = counts.begin();
  std::map<Category, long>::const_iterator it2 = times.begin();

  int cummulative_ms = 0;

  while (it1 != counts.end())
  	{
  		int time_ms = 0;
  		if ((it2 = times.find(it1->first)) != times.end())
  			time_ms = it2->second;

  		if (time_ms!=0)
  		{
  			result << " " << CategoryNames[it1->first] << ": " << it1->second;
  			result << " [" << time_ms << "ms]";
  			result << std::endl;
  			cummulative_ms += time_ms;
  		}
  		it1++;
  	}
  std::cerr << result.str();
  std::cerr << std::fixed;
  std::cerr.precision(2);
  std::cerr << "Statistics Total: " << ((double)cummulative_ms)/1000 << "s" << std::endl;
  std::cerr << "CPU Time Used   : " << Minisat::cpuTime() << "s" << std::endl;
  std::cerr << "Peak Memory Used: " << Minisat::memUsedPeak() << "MB" << std::endl;

  clear();

}

void RunTimes::addTime(Category c, long milliseconds)
{
  std::map<Category, long>::iterator it;
  if ((it = times.find(c)) == times.end())
    {
      times[c] = milliseconds;
    }
  else
    {
      it->second += milliseconds;
    }

}

void RunTimes::addCount(Category c)
{
  std::map<Category, int>::iterator it;
  if ((it = counts.find(c)) == counts.end())
    {
      counts[c] = 1;
    }
  else
    {
      it->second++;
    }
}

void RunTimes::stop(Category c)
{
  Element e = category_stack.top();
  category_stack.pop();
  if (e.first != c)
    {
      std::cerr << e.first;
      std::cerr << c;
      BEEV::FatalError("Don't match");
    }
  addTime(c, getCurrentTime() - e.second);
  addCount(c);
}

void RunTimes::start(Category c)
{
  category_stack.push(std::make_pair(c, getCurrentTime()));
}
