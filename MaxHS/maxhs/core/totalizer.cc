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

#include "maxhs/core/totalizer.h"

#include <cassert>
#include <cmath>

// #include "globaloptions.hpp"
// #include "logging.hpp"

Totalizer::Totalizer(Wcnf *const F, uint32_t var_offset)
    : solver(F), startingVar(var_offset) {}

uint32_t Totalizer::build(vector<Lit> &_inLits, uint32_t _upper) {
  if (verbose >= 3)
    cout << "Building totalizer over " << _inLits.size() << " literals\n";

  inLits = _inLits;
  outLits.clear();

  upper = _upper;
  if (upper > inLits.size()) upper = inLits.size();

  // Corner case (single literal)
  if (inLits.size() == 1) {
    outLits.push_back(inLits[0]);
    treeUpper.push_back(upper);
    treeOut.push_back(outLits);
    treeLeft.push_back({});
    treeRight.push_back({});
    return startingVar;
  }

  // Create out literals
  for (uint32_t i = 0; i < inLits.size(); i++) {
    outLits.push_back(mkLit(startingVar++));
    nVars++;
  }

  tmpBuffer = inLits;

  toCnf(outLits);
  assert(tmpBuffer.size() == 0);

  if (verbose >= 3)
    cout << "Totalizer stats: #clauses=" << nClauses << "; #vars=" << nVars
         << "\n";
  return startingVar;
}

void Totalizer::toCnf(vector<Lit> &lits) {
  vector<Lit> left{};
  vector<Lit> right{};

  assert(lits.size() > 1);
  uint32_t split = floor(lits.size() / 2);

  for (uint32_t i = 0; i < lits.size(); i++) {
    if (i < split) {
      // left branch
      if (split == 1) {
        assert(tmpBuffer.size() > 0);
        left.push_back(tmpBuffer.back());
        tmpBuffer.pop_back();
      } else {
        left.push_back(mkLit(startingVar++));
        nVars++;
      }
    } else {
      // right branch
      if (lits.size() - split == 1) {
        assert(tmpBuffer.size() > 0);
        right.push_back(tmpBuffer.back());
        tmpBuffer.pop_back();
      } else {
        right.push_back(mkLit(startingVar++));
        nVars++;
      }
    }
  }

  if (left.size() > 1) toCnf(left);
  if (right.size() > 1) toCnf(right);
  adder(left, right, lits);
}

void Totalizer::adder(vector<Lit> &left, vector<Lit> &right,
                      vector<Lit> &output) {
  assert(output.size() == left.size() + right.size());

  // Save tree for iterative extension
  treeLeft.push_back(left);
  treeRight.push_back(right);
  treeOut.push_back(output);
  treeUpper.push_back(upper);

  // Encode adder
  for (uint32_t i = 0; i <= left.size(); i++) {
    for (uint32_t j = 0; j <= right.size(); j++) {
      if (i + j > upper + 1) continue;
      vector<Lit> clause;
      clause.clear();
      if (boundType == CARD_UB || boundType == CARD_BOTH) {
        if (i == 0 && j != 0) {
          clause.push_back(~right[j - 1]);
          clause.push_back(output[i + j - 1]);
          solver->addHardClause(clause);
          // solver->addClause(~right[j - 1], output[i + j - 1]);
        } else if (j == 0 && i != 0) {
          clause.push_back(~left[i - 1]);
          clause.push_back(output[i + j - 1]);
          solver->addHardClause(clause);
          // solver->addClause(-left[i - 1], output[i + j - 1]);
        } else if (i != 0 && j != 0) {
          clause.push_back(~left[i - 1]);
          clause.push_back(~right[j - 1]);
          clause.push_back(output[i + j - 1]);
          solver->addHardClause(clause);
          // solver->addClause(-left[i - 1], -right[j - 1], output[i + j - 1]);
        }
        if (i != 0 || j != 0) nClauses++;
      }

      // I think we only have UPPER bounds here

      /* if (boundType == CARD_LB || boundType == CARD_BOTH) {
        if (i == left.size() && j != right.size())
          solver->addClause(right[j], -output[i + j]);
        else if (j == right.size() && i != left.size())
          solver->addClause(left[i], -output[i + j]);
        else if (i != left.size() && j != right.size())
          solver->addClause(left[i], right[j], -output[i + j]);
        if (i != left.size() || j != right.size()) nClauses++;
      } */
    }
  }
}

// Do I use this function??? NOOOUU
/* void Totalizer::join(Totalizer &tot, uint32_t _upper) {
  uint32_t leftIdx = treeUpper.size() - 1;
  uint joinedSize = treeUpper.size() + tot.treeUpper.size();
  treeLeft.reserve(joinedSize);
  treeRight.reserve(joinedSize);
  treeOut.reserve(joinedSize);
  treeUpper.reserve(joinedSize);
  treeLeft.insert(treeLeft.end(), tot.treeLeft.begin(), tot.treeLeft.end());
  treeRight.insert(treeRight.end(), tot.treeRight.begin(), tot.treeRight.end());
  treeOut.insert(treeOut.end(), tot.treeOut.begin(), tot.treeOut.end());
  treeUpper.insert(treeUpper.end(), tot.treeUpper.begin(), tot.treeUpper.end());

  nClauses += tot.nClauses;

  vector<Lit> left = treeOut[leftIdx];
  vector<Lit> right = treeOut[joinedSize - 1];

  inLits.insert(inLits.end(), tot.inLits.begin(), tot.inLits.end());

  outLits.clear();
  for (uint32_t i = 0; i < left.size() + right.size(); i++) {
    outLits.push_back(mkLit(startingVar++));
    nVars++;
  }
  adder(left, right, outLits);

  // Update upper (if required)
  updateUpper(_upper);
} */

/* void Totalizer::addLits(vector<Lit> &lits, uint32_t _upper) {
  if (verbose >= 3)
    cout << "Extending totalizer with " << lits.size() << " literals\n";
  // Build new tot from additional lits
   Totalizer tot{solver, boundType}; 
  and where to pass on the variable offset tot.build(lits, _upper); join(tot,
  _upper); 
} */

/* void Totalizer::updateUpper(uint32_t _upper) {
  if (_upper <= upper) return;
  upper = _upper;
  if (upper > outLits.size()) upper = outLits.size();

  if (verbose >= 3)
    cout << "Extending totalizer to upper bound of " << upper << "\n";

  for (uint32_t z = 0; z < treeUpper.size(); z++) {
    // Encode additional adder clauses
    for (uint32_t i = 0; i <= treeLeft[z].size(); i++) {
      for (uint32_t j = 0; j <= treeRight[z].size(); j++) {
        if (i + j > upper + 1 || i + j <= treeUpper[z] + 1) continue;
        vector<Lit> clause;
        clause.clear();
        if (boundType == CARD_UB || boundType == CARD_BOTH) {
          if (i == 0 && j != 0) {
            clause.push_back(~treeRight[z][j - 1]);
            clause.push_back(treeOut[z][i + j - 1]);
            solver->addHardClause(clause);
            // solver->addClause(-treeRight[z][j - 1], treeOut[z][i + j - 1]);
          } else if (j == 0 && i != 0) {
            clause.push_back(~treeLeft[z][i - 1]);
            clause.push_back(treeOut[z][i + j - 1]);
            solver->addHardClause(clause);
            // solver->addClause(-treeLeft[z][i - 1], treeOut[z][i + j - 1]);
          } else if (i != 0 && j != 0) {
            clause.push_back(~treeLeft[z][i - 1]);
            clause.push_back(~treeRight[z][j - 1]);
            clause.push_back(treeOut[z][i + j - 1]);
            solver->addHardClause(clause);
            // solver->addClause(-treeLeft[z][i - 1], -treeRight[z][j - 1],
            // treeOut[z][i + j - 1]);
          }
          nClauses++;
        }

        if (boundType == CARD_LB || boundType == CARD_BOTH) {
          if (i == treeLeft[z].size() && j != treeRight[z].size())
            solver->addClause(treeRight[z][j], -treeOut[z][i + j]);
          else if (j == treeRight[z].size() && i != treeLeft[z].size())
            solver->addClause(treeLeft[z][i], -treeOut[z][i + j]);
          else if (i != treeLeft[z].size() && j != treeRight[z].size())
            solver->addClause(treeLeft[z][i], treeRight[z][j],
                              -treeOut[z][i + j]);
        } 
      }
    }
    treeUpper[z] = upper;
  }; 
} */
