/*
 * Author: Christoph Jabs - christoph.jabs@helsinki.fi
 * Based on (MSU3, OLL): Open-WBO (https://github.com/sat-group/open-wbo)
 *
 * Copyright © 2022 Christoph Jabs, University of Helsinki
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the “Software”), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in 
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */

#ifndef _totalizer_hpp_INCLUDED
#define _totalizer_hpp_INCLUDED

#include <vector>
#include "maxhs/core/Wcnf.h"

//#include "satsolver.hpp"
//#include "types.hpp"

using std::vector;


enum CardBoundType { CARD_UB, CARD_LB, CARD_BOTH };

// Implementation of the totalizer encoding for incremental use
class Totalizer {
private:
  uint32_t upper{};        // Maximum encoded right hand side
  vector<Lit> inLits{};  // The set of input literals
  vector<Lit> outLits{}; // The set of output literals
  uint32_t nClauses{}; // The number of clauses that the totalizer is made up of
  uint32_t nVars{};    // The number of variables that belong to the totalizer

  vector<Lit> tmpBuffer{}; // Temporary buffer for building the totalizer

  //const CardBoundType boundType; // If the totalizer encodes <= / >= or both
  const CardBoundType boundType{CARD_UB}; 

  Wcnf *const solver; // The Wcnf formula that the totalizer modifies 
  uint32_t startingVar;  // The (next) new variable offset

  vector<vector<Lit>> treeLeft{};  // Left hand sides of the adders
  vector<vector<Lit>> treeRight{}; // Right hand sides of the adders
  vector<vector<Lit>> treeOut{};   // Outputs of the adders
  vector<uint32_t> treeUpper{};      // Maximum encoded value of the adders

  void toCnf(vector<Lit> &); // Encode variables in tmpBuffer to outputs
  void adder(vector<Lit> &, vector<Lit> &, vector<Lit> &); // Encode adder

  // Options
  uint32_t verbose{2}; // The verbosity level of output

public:
  Totalizer(Wcnf *const, uint32_t var_offset);
  uint32_t build(vector<Lit> &,
             uint32_t);             // Build totalizer over inLits up to upper

  void join(Totalizer &, uint32_t); // Join with a second totalizer
  void addLits(vector<Lit> &, uint32_t); // Add additional input literals
  void updateUpper(uint32_t);              // Update the maximum encoded value
  Lit getOutLit(
      uint32_t bound) const { // Get the output literal corresponding to bound
    return outLits[bound];
  }
  inline size_t getNLits() const {
    return inLits.size();
  } // Get the number of input literals
  // Stats getter
  inline uint32_t getUpper() const { return upper; }
  inline uint32_t getNClauses() const { return nClauses; }
  inline uint32_t getNVars() const { return nVars; }

  // Option getter and setter
  uint32_t getVerbose() const { return verbose; }
  void setVerbose(uint32_t verb) { verbose = verb; }
};

#endif