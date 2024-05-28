#ifndef TwEncoder_h
#define TwEncoder_h

#include <map>

#include "maxhs/core/Wcnf.h"
#include "maxhs/core/totalizer.h"

Lit makeLit(uint64_t, uint64_t, uint64_t, uint64_t offset = 0);
uint64_t getTriangularIndex(uint64_t, uint64_t, uint64_t);

static void encode_graph(Wcnf *F, vector<vector<int>> &edgeList, int nodes,
                         bool zero_offset) {
  uint32_t n = (uint32_t)nodes;

  // std::map<Lit, int> allLits;
  vector<Totalizer> totalizers;

  vector<Lit> lits;

  // Transitivity: For distinct i,j,k ord*_ij and ord*_jk -> ord*_ij
  // -ord*_ij or -ord*_jk or ord*_ik
  for (uint64_t i = 0; i < n; i++) {
    for (uint64_t j = 0; j < n; j++) {
      if (j == i) continue;
      for (uint64_t k = 0; k < n; k++) {
        if (k == j || k == i) continue;
        lits.clear();
        lits.push_back(~(makeLit(i, j, n)));  // -ord*_ij
        lits.push_back(~(makeLit(j, k, n)));  // -ord*_jk
        lits.push_back((makeLit(i, k, n)));   // ord*_ik
        F->addHardClause(lits);
        // cout << lits << ' ' << ~(makeLit(i, j, n)) << ' ' << ~(makeLit(j, k,
        // n))
        //     << ' ' << (makeLit(i, k, n)) << "\n";
        // log(2, "lits ", lits);
      }
    }
  }

  /* for (uint32_t i = 0; i < n; i++) {
    for (uint32_t j = 0; j < n; j++) {
      if (j == i) continue;
      log(2, makeLit(i, j, n));
    }
    log(2, '\n');
  } */

  // cout << "Next the O_ji variables\n";
  uint64_t oijs_offset = n * (n - 1) / 2;

  // Encoding the ordered Grapg O_ijs: distinct i,j,k
  // (O_ki and O_kj) -> (O_ij or O_ji)
  //  -O_ki or -O_kj or O_ji or O_ij
  for (uint64_t k = 0; k < n; k++) {
    for (uint64_t i = 0; i < n; i++) {
      if (k == i) continue;
      for (uint64_t j = i; j < n; j++) {
        if (j == i || j == k) continue;
        lits.clear();
        lits.push_back(~(makeLit(k, i, n, oijs_offset)));  // -O_ki
        lits.push_back(~(makeLit(k, j, n, oijs_offset)));  // -O_kj
        lits.push_back((makeLit(i, j, n, oijs_offset)));   // O_ij
        lits.push_back((makeLit(j, i, n, oijs_offset)));   // O_ji

        F->addHardClause(lits);

        // cout << lits << ' ' << ~(makeLit(k, i, n, oijs_offset)) << ' '
        //     << ~(makeLit(k, j, n, oijs_offset)) << ' '
        //     << (makeLit(i, j, n, oijs_offset)) << ' '
        //     << (makeLit(j, i, n, oijs_offset)) << "\n";
      }
    }
  }

  // lits = objective function over O_ij j=/=i
  // we get n objective functions containing n-1 lits
  if (params.treewidth == 0) {
    for (uint64_t i = 0; i < n; i++) {
      lits.clear();
      for (uint64_t j = 0; j < n; j++) {
        if (j == i) continue;
        lits.push_back(makeLit(i, j, n, oijs_offset));
        // cout << (makeLit(k, i, n, oijs_offset)) << ' ';
      }
      F->addObjective(lits);
      log(2, "b Adding objective clause ", lits);
      // cout << "\n";
    }
  }

  // cout << "\nThen the -ord_ji or -O_ij \n";
  // ord*_ij -> -O_ji : -ord*_ij or -O_ji
  for (uint64_t i = 0; i < n; i++) {
    for (uint64_t j = 0; j < n; j++) {
      if (j == i) continue;
      lits.clear();
      lits.push_back(~(makeLit(i, j, n, 0)));            // -ord*_ij
      lits.push_back(~(makeLit(j, i, n, oijs_offset)));  // -O_ji
      F->addHardClause(lits);
      // cout << lits << "\n";
    }
  }

  // cout << "\nThe redundant clauses\n";
  // redundant clauses -O_ji or -O_ij
  for (uint64_t i = 0; i < n; i++) {
    for (uint64_t j = i; j < n; j++) {
      if (j == i) continue;
      lits.clear();
      lits.push_back(~(makeLit(i, j, n, oijs_offset)));  // -O_ij
      lits.push_back(~(makeLit(j, i, n, oijs_offset)));  // -O_ji
      F->addHardClause(lits);
      // cout << lits << "\n";
    }
  }

  // finally for each edge (v_i,v_j) in E, i<j, add (O_ij or O_ji)
  for (auto &edge : edgeList) {
    int i = edge[0];
    int j = edge[1];
    lits.clear();
    lits.push_back(
        (makeLit(i - (zero_offset ? 0 : 1), j - (zero_offset ? 0 : 1), n,
                 oijs_offset)));  // O_ij
    lits.push_back(
        (makeLit(j - (zero_offset ? 0 : 1), i - (zero_offset ? 0 : 1), n,
                 oijs_offset)));  // O_ji
    F->addHardClause(lits);
    log(2, "edges ", i, ' ', j, lits);
  }

  uint64_t newVarOffset = (n * (n - 1)) / 2 + (n * (n - 1));
  // now what remains is the set of soft constraints, sums over O_ijs
  // Enter totalizer
  if (params.treewidth == 1) {
    for (uint64_t i = 0; i < n; i++) {
      Totalizer toti(F, newVarOffset);
      lits.clear();
      // build the A_i clause over all O_ij for j=/=i
      for (uint64_t j = 0; j < n; j++) {
        if (j == i) continue;
        lits.push_back((makeLit(i, j, n, oijs_offset)));  // O_ij
      }
      newVarOffset = toti.build(lits, n - 1);
      totalizers.push_back(toti);
    }

    uint64_t wOffset = newVarOffset;
    // -W_i <-> (-y1_i+1 and ... -yn_i+1), for all i (bounds) in 1..n-2
    for (uint64_t i = 0; i < n - 1; i++) {  // i is the bound
      lits.clear();
      // -W_i <- -y(tot)_i+1 for all tot in 1..n
      // (y(tot)_i+1 or W_i)
      lits.push_back(~mkLit(newVarOffset));
      for (auto tot : totalizers) {
        // y(tot)_i+1
        Lit yTotI = tot.getOutLit(i);
        lits.push_back(yTotI);
        // -W_i -> -y(tot)_i+1  :  W_i or -y(tot)_i+1
        vector<Lit> implClause = {mkLit(newVarOffset), ~yTotI};
        F->addClausalConstr(implClause);
        // cout << "Implication clause " << implClause << "\n";
      }
      F->addClausalConstr(lits);
      // cout << "Equation clause " << lits << "\n";
      newVarOffset++;
    }

    // -W_i -> -W_i+1  :  W_i or -W_i+1
    // additionally, W_i as soft clause for each i=1..n-1
    for (uint64_t i = wOffset; i < wOffset + n - 1; i++) {
      lits.clear();
      lits.push_back(mkLit(i));
      lits.push_back(~mkLit(i + 1));
      F->addClausalConstr(lits);
      F->varForObjectiveFunc(mkLit(i));
    }
    F->varForObjectiveFunc(mkLit(wOffset + n - 1));
  }

  F->set_dimacs_params(newVarOffset, F->nHards(), n - 1);
  // F->printSimpStats();
  // F->printFormulaStats();
}

Lit makeLit(uint64_t i, uint64_t j, uint64_t n, uint64_t offset) {
  if (!offset) {
    return (i < j) ? mkLit(getTriangularIndex(i, j, n))
                   : ~mkLit(getTriangularIndex(j, i, n));
  }
  return mkLit(offset + ((i < j) ? i * (n - 1) + j - 1 : i * (n - 1) + j));
}

// Get the linear index corresponding to the value of the upper triangualr
// matrix at point (i,j), i<j
uint64_t getTriangularIndex(uint64_t i, uint64_t j, uint64_t n) {
  return (n * (n - 1) / 2) - (n - i) * ((n - i) - 1) / 2 + j - i - 1;
}

#endif
