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

#ifndef PACKEDMATRIX_H
#define PACKEDMATRIX_H

#include <algorithm>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "PackedRow.h"

//#define DEBUG_MATRIX

namespace MINISAT
{
using namespace MINISAT;

class PackedMatrix
{
public:
    PackedMatrix() :
        mp(NULL)
        , numRows(0)
        , numCols(0)
    {
    }
    
    PackedMatrix(const PackedMatrix& b) :
        numRows(b.numRows)
        , numCols(b.numCols)
    {
        #ifdef DEBUG_MATRIX
        assert(b.numRows > 0 && b.numCols > 0);
        #endif
        
        mp = new uint64_t[numRows*2*(numCols+1)];
        memcpy(mp, b.mp, sizeof(uint64_t)*numRows*2*(numCols+1));
    }
    
    ~PackedMatrix()
    {
        delete[] mp;
    }
    
    void resize(const uint num_rows, uint num_cols)
    {
        num_cols = num_cols / 64 + (bool)(num_cols % 64);
        if (numRows*2*(numCols+1) < num_rows*2*(num_cols+1)) {
            delete[] mp;
            mp = new uint64_t[num_rows*2*(num_cols+1)];
        }
        numRows = num_rows;
        numCols = num_cols;
    }
    
    void resizeNumRows(const uint num_rows)
    {
        #ifdef DEBUG_MATRIX
        assert(num_rows <= numRows);
        #endif
        
        numRows = num_rows;
    }
    
    PackedMatrix& operator=(const PackedMatrix& b)
    {
        #ifdef DEBUG_MATRIX
        //assert(b.numRows > 0 && b.numCols > 0);
        #endif
        
        if (numRows*2*(numCols+1) < b.numRows*2*(b.numCols+1)) {
            delete[] mp;
            mp = new uint64_t[b.numRows*2*(b.numCols+1)];
        }
        
        numRows = b.numRows;
        numCols = b.numCols;
        memcpy(mp, b.mp, sizeof(uint64_t)*numRows*2*(numCols+1));
        
        return *this;
    }

    inline PackedRow getMatrixAt(const uint i)
    {
        #ifdef DEBUG_MATRIX
        assert(i <= numRows);
        #endif
        
        return PackedRow(numCols, mp+i*2*(numCols+1));
    }
    inline PackedRow getVarsetAt(const uint i)
    {
        #ifdef DEBUG_MATRIX
        assert(i <= numRows);
        #endif
        
        return PackedRow(numCols, mp+i*2*(numCols+1)+(numCols+1));
    }
    
    inline const PackedRow getMatrixAt(const uint i) const
    {
        #ifdef DEBUG_MATRIX
        assert(i <= numRows);
        #endif
        
        return PackedRow(numCols, mp+i*2*(numCols+1));
    }
    
    inline const PackedRow getVarsetAt(const uint i) const
    {
        #ifdef DEBUG_MATRIX
        assert(i <= numRows);
        #endif
        
        return PackedRow(numCols, mp+i*2*(numCols+1)+(numCols+1));
    }
    
    class iterator
    {
    public:
        PackedRow operator*()
        {
            return PackedRow(numCols, mp);
        }
        
        iterator& operator++()
        {
            mp += 2*(numCols+1);
            return *this;
        }
        
        iterator operator+(const uint num) const
        {
            iterator ret(*this);
            ret.mp += 2*(numCols+1)*num;
            return ret;
        }
        
        const uint operator-(const iterator& b) const
        {
            return (mp - b.mp)/(2*(numCols+1));
        }
        
        void operator+=(const uint num)
        {
            mp += 2*(numCols+1)*num;
        }
        
        const bool operator!=(const iterator& it) const
        {
            return mp != it.mp;
        }
        
        const bool operator==(const iterator& it) const
        {
            return mp == it.mp;
        }
        
    private:
        friend class PackedMatrix;
        
        iterator(uint64_t* _mp, const uint _numCols) :
            mp(_mp)
            , numCols(_numCols)
        {}
        
        uint64_t* mp;
        const uint numCols;
    };
    
    inline iterator beginMatrix()
    {
        return iterator(mp, numCols);
    }
    
    inline iterator endMatrix()
    {
        return iterator(mp+numRows*2*(numCols+1), numCols);
    }
    
    inline iterator beginVarset()
    {
        return iterator(mp+(numCols+1), numCols);
    }
    
    inline iterator endVarset()
    {
        return iterator(mp+(numCols+1)+numRows*2*(numCols+1), numCols);
    }
    
    inline const uint getSize() const
    {
        return numRows;
    }

private:
    
    uint64_t* mp;
    uint numRows;
    uint numCols;
};

}; //NAMESPACE MINISAT

#endif //PACKEDMATRIX_H

