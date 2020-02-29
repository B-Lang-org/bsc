/***********************************************************************************
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
**************************************************************************************************/

#include "RestartTypeChooser.h"
#include "Solver.h"

//#define VERBOSE_DEBUG
//#define PRINT_VARS

namespace MINISAT
{
using namespace MINISAT;

RestartTypeChooser::RestartTypeChooser(const Solver& s) :
    solver(s)
    , topX(100)
    , limit(40)
{
}

void RestartTypeChooser::addInfo()
{
    firstVarsOld = firstVars;
    calcHeap();
    uint sameIn = 0;
    if (!firstVarsOld.empty()) {
        uint thisTopX = std::min(firstVarsOld.size(), (size_t)topX);
        for (uint i = 0; i != thisTopX; i++) {
            if (std::find(firstVars.begin(), firstVars.end(), firstVarsOld[i]) != firstVars.end())
                sameIn++;
        }
        #ifdef VERBOSE_DEBUG
        std::cout << "    Same vars in first&second first 100: " << sameIn << std::endl;
        #endif
        sameIns.push_back(sameIn);
    }
    
    #ifdef VERBOSE_DEBUG
    std::cout << "Avg same vars in first&second first 100: " << avg() << " standard Deviation:" << stdDeviation(sameIns) <<std::endl;
    #endif
}

const RestartType RestartTypeChooser::choose()
{
    pair<double, double> mypair = countVarsDegreeStDev();
    if ((mypair.second  < 80 && 
        (avg() > (double)limit || ((avg() > (double)(limit*0.9) && stdDeviation(sameIns) < 5))))
        ||
        (mypair.second  < 80 && (double)solver.xorclauses.size() > (double)solver.nClauses()*0.1))
        return static_restart;
    else
        return dynamic_restart;
}

const double RestartTypeChooser::avg() const
{
    double sum = 0.0;
    for (uint i = 0; i != sameIns.size(); i++)
        sum += sameIns[i];
    return (sum/(double)sameIns.size());
}

const double RestartTypeChooser::stdDeviation(vector<uint32_t>& measure) const
{
    double average = avg();
    double variance = 0.0;
    for (uint i = 0; i != measure.size(); i++)
        variance += pow((double)measure[i]-average, 2);
    variance /= (double)measure.size();
    
    return sqrt(variance);
}

void RestartTypeChooser::calcHeap()
{
    firstVars.clear();
    firstVars.reserve(topX);
    #ifdef PRINT_VARS
    std::cout << "First vars:" << std::endl;
    #endif
    Heap<Solver::VarOrderLt> tmp(solver.order_heap);
    uint32_t thisTopX = std::min(tmp.size(), topX);
    for (uint32_t i = 0; i != thisTopX; i++) {
        #ifdef PRINT_VARS
        std::cout << tmp.removeMin()+1 << ", ";
        #endif
        firstVars.push_back(tmp.removeMin());
    }
    #ifdef PRINT_VARS
    std::cout << std::endl;
    #endif
}

const std::pair<double, double> RestartTypeChooser::countVarsDegreeStDev() const
{
    vector<uint32_t> degrees;
    degrees.resize(solver.nVars(), 0);
    addDegrees(solver.clauses, degrees);
    addDegrees(solver.binaryClauses, degrees);
    addDegrees(solver.xorclauses, degrees);
    uint32_t sum = 0;
    uint32_t *i = &degrees[0], *j = i;
    for (uint32_t *end = i + degrees.size(); i != end; i++) {
        if (*i != 0) {
            sum += *i;
            *j++ = *i;
        }
    }
    degrees.resize(degrees.size() - (i-j));
    
    double avg = (double)sum/(double)degrees.size();
    double stdDev = stdDeviation(degrees);
    
    #ifdef VERBOSE_DEBUG
    std::cout << "varsDegree avg:" << avg << " stdDev:" << stdDev << std::endl;
    #endif
    
    return std::make_pair(avg, stdDev);
}

template<class T>
void RestartTypeChooser::addDegrees(const vec<T*>& cs, vector<uint32_t>& degrees) const
{
    for (T * const*c = cs.getData(), * const*end = c + cs.size(); c != end; c++) {
        T& cl = **c;
        if (cl.learnt()) continue;
        
        for (const Lit *l = cl.getData(), *end2 = l + cl.size(); l != end2; l++) {
            degrees[l->var()]++;
        }
    }
}

template void RestartTypeChooser::addDegrees(const vec<Clause*>& cs, vector<uint32_t>& degrees) const;
template void RestartTypeChooser::addDegrees(const vec<XorClause*>& cs, vector<uint32_t>& degrees) const;

}; //NAMESPACE MINISAT

