/****************************************************************************************[Dimacs.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Dimacs_h
#define Minisat_Dimacs_h

#include <math.h>
#include <stdio.h>
#include <string.h>

#include <iostream>
#include <sstream>
#include <vector>

#ifdef GLUCOSE
#include "glucose/core/SolverTypes.h"
#include "glucose/utils/ParseUtils.h"
#else
#include "minisat/core/SolverTypes.h"
#include "minisat/utils/ParseUtils.h"
#endif

#include "maxhs/core/BMFEncoder.h"
#include "maxhs/core/MaxSolverTypes.h"
#include "maxhs/core/TwEncoder.h"
#include "maxhs/core/Wcnf.h"
#include "maxhs/core/MWCBEncoder.h"

using std::cerr;
using std::cout;

#ifdef GLUCOSE
namespace Minisat = Glucose;
#endif

template <class B>
static long double parseIntegerLongDouble(B& in) {
  long double val = 0;
  bool neg = false;
  skipWhitespace(in);
  if (*in == '-')
    neg = true, ++in;
  else if (*in == '+')
    ++in;
  if (*in < '0' || *in > '9')
    cerr << "PARSE ERROR! Unexpected char: " << *in << "\n", exit(3);
  while (*in >= '0' && *in <= '9') val = val * 10 + (*in - '0'), ++in;
  return neg ? -val : val;
}

// JD
template <class B>
static long double parseLongDouble(B& in) {
  long double val = 0;
  bool neg = false;
  bool frac = false;
  int exponent = 0;
  int n = -1;
  skipWhitespace(in);
  if (*in == '-')
    neg = true, ++in;
  else if (*in == '+')
    ++in;
  if ((*in < '0' || *in > '9') && *in != '.' && *in != 'e' && *in != '-' &&
      *in != '+')
    cerr << "PARSE ERROR 3! Unexpected char: " << *in << "\n", exit(3);
  while ((*in >= '0' && *in <= '9') || *in == '.' || *in == 'e' || *in == '-' ||
         *in == '+') {
    if (*in == '.')
      frac = true;
    else if (*in == 'e') {
      bool expNeg = false;
      ++in;
      while (*in == '-' || *in == '0' || *in == '+') {
        if (*in == '-') expNeg = true;
        ++in;
      }
      int intExp = parseInt(in);
      exponent = expNeg ? -intExp : intExp;
    } else
      frac       ? val = val + (*in - '0') * pow(10.0, n),
             --n : val = val * 10 + (*in - '0');
    ++in;
  }
  val = val * pow(10, exponent);
  return neg ? -val : val;
}

//=================================================================================================
// DIMACS Parser:

template <class B>
static void readClause(B& in, vector<Lit>& lits) {
  int parsed_lit, var;
  lits.clear();
  for (;;) {
    parsed_lit = parseInt(in);
    if (parsed_lit == 0) break;
    var = abs(parsed_lit) - 1;
    lits.push_back((parsed_lit > 0) ? mkLit(var) : ~mkLit(var));
  }
}

// JD Read clauses with weights
template <class B>
static void readClause(B& in, vector<Lit>& lits, Weight& outW) {
  bool first_time = true;
  int parsed_lit, var;
  lits.clear();
  for (;;) {
    if (first_time) {
      first_time = false;
      outW = parseLongDouble(in);
      continue;
    }
    parsed_lit = parseInt(in);
    if (parsed_lit == 0) break;
    var = abs(parsed_lit) - 1;
    lits.push_back((parsed_lit > 0) ? mkLit(var) : ~mkLit(var));
  }
}
/********************************************************/
template <class B>
static bool parse_SCV_matrix_reals(B& in, Wcnf* F, bool verify) {
  vector<vector<double>> MatrixX;
  bool first_time = true;
  int n{};
  for (;;) {
    if (*in == EOF) break;
    vector<double> xi;
    for (;;) {
      if (*in == '\n') {
        if (xi.size() && first_time) {
          first_time = false;
          n = xi.size();
        }
        if (xi.size() != static_cast<size_t>(n)) {
          log(0, "Odd things happened", xi);
        }
        MatrixX.push_back(xi);
        skipLine(in);
        break;
      }
      skipWhitespace(in);
      if (eagerMatch(in, ",")) continue;
      double real = parseLongDouble(in);
      xi.push_back(real);
    }
  }
  log(4, "matr ", MatrixX);
  encode_matrice_reals(F, MatrixX, verify);
  return true;
}

template <class B>
static bool parse_SCV_matrix(B& in, Wcnf* F, bool verify) {
  vector<vector<int>> MatrX;
  int k = params.undercover_BMF;
  log(1, "b Undercover BMF with k = ", k);

  for (;;) {
    if (*in == EOF) break;
    vector<int> row;
    bool emptyCell = true;
    for (;;) {
      if (*in == '\n') {
        if (row.size()) {
          if (emptyCell) row.push_back(-1);
          MatrX.push_back(row);
          F->MatrixX.addVec(row);
        }
        skipLine(in);
        break;
      }
      skipWhitespace(in);
      if (eagerMatch(in, "0")) {
        row.push_back(0);
        emptyCell = false;
      } else if (eagerMatch(in, "1")) {
        row.push_back(1);
        emptyCell = false;
      } else if (eagerMatch(in, ",")) {
        if (emptyCell) row.push_back(-1);
        emptyCell = true;
      } else if (eagerMatch(in, "nan")) {
        row.push_back(-1);
      } else {
        cout << "Error parsing the binary matrix, unsupported character found: "
                "\'"
             << char(*in) << "\'\n";
        return false;
      }
    }
  }
  /* for (auto row : MatrX) {
    for (auto cell : row) {
      cout << cell << ' ';
    }
    cout << '\n';
  }
  return false; */
  encode_matrice(F, MatrX, k, verify);
  return true;
}

template <class B>
static bool parse_DIMACS_main(B& in, Wcnf* F) {
  vector<Lit> lits;
  int clauses = 0;
  // JD Note that partial maxsat clauses either have weight 1 or partial_Top
  bool clausesHaveWeights = false;

  // structs for the TW instances
  vector<vector<int>> twGraph;
  bool twInstance{false};
  bool zero_offset{false};
  int nodes, _edges;

  for (;;) {
    skipWhitespace(in);
    if (*in == EOF)
      break;
    else if (*in == 'p') {
      // JD it could be unweighted or weighted CNF
      if (eagerMatch(in, "p cnf")) {
        int nvars = parseInt(in);
        clauses = parseInt(in);
        F->set_dimacs_params(nvars, clauses);
        // JD
      } else if (eagerMatch(in, "wcnf")) {
        clausesHaveWeights = true;
        int nvars = parseInt(in);
        clauses = parseInt(in);
        if (!eagerMatch(in, "\n")) {
          Weight top = parseIntegerLongDouble(in);
          F->set_dimacs_params(nvars, clauses, top);
        } else {  // no top => no hard clauses => no upper bound on soft clause
                  // weight.
          F->set_dimacs_params(nvars, clauses);
        }
      } else if (eagerMatch(in, "tw")) {
        // the Dimacs file is a graph for tree width problem
        twInstance = true;
        nodes = parseInt(in);
        _edges = parseInt(in);
        cout << "c nodes: " << nodes << ", edges " << _edges << "\n";
      } else {
        // not 'p cnf' or 'p wcnf'
        // Then it is DIMACS graph use tw
        // return false;
        twInstance = true;
        nodes = parseInt(in);
        _edges = parseInt(in);
        cout << "c nodes: " << nodes << ", edges " << _edges << "\n";
      }
    } else if (*in == 'c') {
      skipLine(in);
    } else if (twInstance) {
      // reading edges for TW instance
      if (eagerMatch(in, "e")) {
        // Do nothing with it
      }
      vector<int> edge = {parseInt(in), parseInt(in)};
      if (edge[0] == 0 || edge[1] == 0) zero_offset = true;
      twGraph.push_back(edge);

    } else {
      // JD parse the weights of clauses as well (default weight 1)
      // printf("A| parse clause\n");
      Weight w = 1;
      clausesHaveWeights ? readClause(in, lits, w) : readClause(in, lits);
      F->addDimacsClause(lits, w);
    }
  }
  if (twInstance) {
    /* for (auto &vec : twGraph) {
      for (auto &a : vec) {
        cout << ' ' << a;
      }
      cout << "\n";
    } */
    assert(twGraph.size() == _edges);
    encode_graph(F, twGraph, nodes, zero_offset);
  }
  return true;
}

// Inserts problem into solver.
//
static bool parse_DIMACS(gzFile input_stream, Wcnf* F, std::string suffix,
                         bool verify) {
  Minisat::StreamBuffer in(input_stream);
  if (strcmp(suffix.c_str(), "csv") == 0) {
    if (params.undercover_BMF) return parse_SCV_matrix(in, F, verify);
    else return parse_SCV_matrix_reals(in, F, verify);
  } else {
    return parse_DIMACS_main(in, F);
  }
}

#endif
