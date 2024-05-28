#ifndef BmfEncoder_h
#define BmfEncoder_h
#include <map>
#include <set>

#include "maxhs/core/Wcnf.h"
#include "maxhs/core/totalizer.h"
#include "maxhs/ifaces/Cplex.h"

int getCellInd(int iRow, int jCol, int offset, int numCols) {
  return offset + iRow * numCols + jCol;
};

// args: i, j, l, m = #rows, n = #cols
int getTcellInd(int iRow, int jCol, int l, int numRows, int numCols) {
  return (l * numCols * numRows) + (iRow * numCols) + jCol;
};

static void encode_matrice(Wcnf *F, vector<vector<int>> &MatriceX, int k,
                           bool verify) {
  int mRows = MatriceX.size();
  int nCols = MatriceX[0].size();

  // key: ind(X[i,j]), value: s_ij
  std::map<int, int> cellIndToSoftVar;
  // key: s_ij, value: (i,j)
  std::map<int, std::tuple<int, int>> onesCoord;
  // the set of s_ij vars
  std::set<int> ones;
  vector<Lit> cls;
  int maxCost{0};

  int aOffset = 0;
  int bOffset = mRows * k;
  int tOffset = bOffset + k * nCols;
  int zOffset = tOffset + k * nCols * mRows;
  int newVarOffset = zOffset + k * nCols;

  log(1, "Rows: ", mRows, " Cols: ", nCols, " Offsets a: ", aOffset,
      ", b: ", bOffset, " newVar: ", newVarOffset);
  for (int i = 0; i < mRows; i++) {
    for (int j = 0; j < nCols; j++) {
      if (MatriceX[i][j] == 0) {
        // The cell i,j is zero / false, row i in A o col j in B must be zero
        // (-A_i,l or -B_l,j) for l in 1..k
        for (int l = 0; l < k; l++) {
          cls.clear();
          Var a_il = getCellInd(i, l, aOffset, k);      // A_( mRows x k )
          Var b_lj = getCellInd(l, j, bOffset, nCols);  // B_( k x nCols )
          cls.push_back(~mkLit(a_il));
          cls.push_back(~mkLit(b_lj));
          F->addHardClause(cls);
        }
      } else if (MatriceX[i][j] == 1) {
        // The cell i,j is 1, we want to have (A o B)_ij be 1 as well

        // Then for l in 0..k-1 there there must be an l s.t. (A_il and B_lj)
        // Aux var T(l)_ij => (A_il and B_lj): (-T(l)_ij or A_il) and (-T(l)_ij
        // or B_lj) the soft clause is the disjunction of k aux vars T(l)_ij
        cls.clear();
        for (int l = 0; l < k; l++) {
          int t_lij = tOffset + getTcellInd(i, j, l, mRows, nCols);
          cls.push_back(~mkLit(t_lij));
        }
        for (int l = 0; l < k; l++) {
          int a_il = getCellInd(i, l, aOffset, k);
          int b_lj = getCellInd(l, j, bOffset, nCols);
          F->addHardClause(cls[l], mkLit(a_il));
          F->addHardClause(cls[l], mkLit(b_lj));
        }
        int s_ij = newVarOffset++;
        cellIndToSoftVar[getCellInd(i, j, 0, nCols)] = s_ij;
        // S_ij -> V_l T(l)_ij  :  -S_ij vV_l T(l)_ji
        // cls.push_back(~mkLit(s_ij));
        // F->addHardClause(cls);
        F->addImplicationObjective(mkLit(s_ij), cls);
        if (params.inform_SAT) {
          vector<Lit> hardCls;
          hardCls.clear();
          for (auto lit : cls) {
            hardCls.push_back(~lit);
          }
          hardCls.push_back(mkLit(s_ij));
          log(2, "adding as clause ", hardCls);
          F->addHardClause(hardCls);
        }
        ones.insert(s_ij);
        onesCoord[s_ij] = std::make_tuple(i, j);
      }
    }
  }
  maxCost = ones.size();

  if (params.bmf_card_gen > 0 && !verify) {
    std::set<int> onesToCheck(ones.begin(), ones.end());
    while (true) {
      std::set<int> incompatibles{};
      for (auto oneCell : onesToCheck) {
        int i = std::get<0>(onesCoord[oneCell]);
        int j = std::get<1>(onesCoord[oneCell]);
        bool allIncomp{true};
        for (auto incomp : incompatibles) {
          auto s_iijj = onesCoord[incomp];
          int ii = std::get<0>(s_iijj);
          int jj = std::get<1>(s_iijj);
          if (!(MatriceX[ii][j] == 0 || MatriceX[i][jj] == 0)) {
            allIncomp = false;
            break;
          }
        }
        if (allIncomp) {
          incompatibles.insert(oneCell);
        }
      }
      if (incompatibles.empty()) break;
      if (params.bmf_card_gen == 3 && (int)incompatibles.size() > 1 &&
          (params.inform_SAT ? (int)incompatibles.size() <= k : 1)) {
        for (int l = 0; l < k; l++) {
          cls.clear();
          for (auto s_ij : incompatibles) {
            int i = std::get<0>(onesCoord[s_ij]);
            int j = std::get<1>(onesCoord[s_ij]);
            int t_lij = tOffset + getTcellInd(i, j, l, mRows, nCols);
            cls.push_back(mkLit(t_lij));
          }
          vector<Lit> dummyVec{};
          F->addCardConstr(cls, cls.size() - 1, 'G', dummyVec);
        }
      }
      if ((int)incompatibles.size() <= k) {
        // remove only the first element from the set as the other elements may
        // contribute to other groups of incompatibles
        onesToCheck.erase(*onesToCheck.begin());
        continue;
      }
      for (auto el : incompatibles) {
        onesToCheck.erase(el);
      }
      if ((int)incompatibles.size() > k) {
        vector<Lit> constr;
        for (auto s_ij : incompatibles) {
          constr.push_back(mkLit(s_ij));
          if (params.inform_SAT /*  || params.bmf_card_gen == 1 */)
            ones.erase(s_ij);  // adding the card constraint to sat solver
                               // requires the soft unit clauses to be deleted
          // When adding only to cplex the soft unit clauses must be preserved
        }
        vector<Lit> o_lits{};
        if (params.inform_SAT) {
          Totalizer tot(F, newVarOffset++);
          newVarOffset = tot.build(constr, constr.size());
          // cout << tot.getNClauses() << ' ' << tot.getNVars() << '\n';
          for (int i = constr.size() - k; i < (int)constr.size(); i++) {
            // F->addSoftClause(~tot.getOutLit(i), 1);
            // F->addImplicationObjective(tot.getOutLit(i), constr, 0, i);
            o_lits.push_back(tot.getOutLit(i));
            F->varForObjectiveFunc(tot.getOutLit(i));
          }
          // F->addToBaseCost(constr.size() - k);
          // add soft clause o_(n-k), meaning n-k of the s_ij vars must be set
          // to false
        }
        F->addCardConstr(constr, incompatibles.size() - k, 'G', o_lits);
      }
    }
  }
  log(0, "amount of card constraints: ", F->getCardConstraints().size());
  log(0, "Remaining compatible ones ", ones.size());
  // Add the remaining s_ij as unit soft clauses to the formula
  for (auto oneCell : ones) {
    F->varForObjectiveFunc(mkLit(oneCell));
  }
  // Symmetry breaking, aux var Z_ij, enforce lex. order on B matr
  if (params.bmf_symbreak && params.bmf_symbreak < 3 && !verify) {
    zOffset = newVarOffset;
    for (int i = 0; i < k - 1; i++) {
      for (int j = 0; j < nCols; j++) {
        cls.clear();
        Lit z_ij = mkLit(getCellInd(i, j, zOffset, nCols));
        Lit z_nextj = mkLit(getCellInd(i, j + 1, zOffset, nCols));
        Lit b_ij = mkLit(getCellInd(i, j, bOffset, nCols));
        Lit b_nexti = mkLit(getCellInd(i + 1, j, bOffset, nCols));
        // (Z_ij ^ -B_ij) => -B_i+1,j
        cls.insert(cls.end(), {~z_ij, b_ij, ~b_nexti});
        F->addHardClause(cls);
        cls.clear();

        if (j == nCols - 1) continue;
        // (Z_ij ^ B_ij ^ B_i+1,j) => Z_i,j+1
        cls.insert(cls.end(), {~z_ij, ~b_ij, ~b_nexti, z_nextj});
        F->addHardClause(cls);
        cls.clear();

        // (Z_ij ^ -B_ij ^ -B_i+1,j) => Z_i,j+1
        cls.insert(cls.end(), {~z_ij, b_ij, b_nexti, z_nextj});
        F->addHardClause(cls);
      }
    }

    for (int i = 0; i < k; i++) {
      // Z_i,0
      F->addHardClause(mkLit(getCellInd(i, 0, zOffset, nCols)));
    }
  }

  log(1, "Rows: ", mRows, " Cols: ", nCols, " Offsets a: ", aOffset,
      ", b: ", bOffset, ", z: ", zOffset, " newVar: ", newVarOffset);
  F->set_dimacs_params(F->nVars(), F->nHards() + F->nSofts(), maxCost);
  log(4, "Hards:");
  for (auto cls : F->hards()) {
    log(4, cls.getVec());
  }
  log(4, "Softs:");
  for (auto cls : F->softs()) {
    log(4, cls.getVec());
  }

  // write WCNF to a file
  // TODO add flag to params to trigger file writing
  /* FILE *fptr;
  fptr = fopen("matrice.wcnf", "w");
  fprintf(fptr, "p wcnf %li %li\n", F->nVars(), F->nHards() + F->nSofts());
  for (auto cnstr : F->hards()) {
    fprintf(fptr, "h");
    for (auto &lit : cnstr) {
      fprintf(fptr, " %i", sign(lit) ? -var(lit) : var(lit));
    }
    fprintf(fptr, "\n");
  }

  for (auto cnstr : F->softs()) {
    fprintf(fptr, "1");
    for (auto &lit : cnstr) {
      fprintf(fptr, " %i", sign(lit) ? -var(lit) : var(lit));
    }
    fprintf(fptr, "\n");
  }

  fclose(fptr); */
}

void encode_bmf_symbreaks_to_MIP(Wcnf *F, MaxHS_Iface::Cplex *cplex) {
  int k = params.undercover_BMF;
  int mRows = F->MatrixX.size();
  int nCols = F->MatrixX.getVec(0).size();
  int tOffset = mRows * k + k * nCols;
  int newVarOffset = F->nVars();
  //int bOffset = newVarOffset++;
  int bOffset = mRows * k;
  int zOffset = tOffset + k * nCols * mRows;
  vector<Lit> cls;

  vector<vector<int>> ones_on_collumn;

  for (int j = 0; j < nCols; j++) {
    vector<int> col;
    ones_on_collumn.push_back(col);
  }

  for (int i = 0; i < mRows; i++) {
    for (int j = 0; j < nCols; j++) {
      if (F->MatrixX.getVec(i)[j] == 1) {
        ones_on_collumn[j].push_back(i);
      }
    }
  }

  //int zOffset = bOffset + k * nCols;
  for (int l = 0; l < k - 1; l++) {
    for (int j = 0; j < nCols; j++) {
      cls.clear();
      vector<Lit> Tlj;

      for (int i : ones_on_collumn[j]) {
        int t_lij = tOffset + getTcellInd(i, j, l, mRows, nCols);
        Tlj.push_back(mkLit(t_lij));
      }
      log(3,"Tlj: ", Tlj);

      Lit z_lj = mkLit(getCellInd(l, j, zOffset, nCols));
      Lit z_nextj = mkLit(getCellInd(l, j + 1, zOffset, nCols));
      Lit b_lj = mkLit(getCellInd(l, j, bOffset, nCols));
      Lit b_nextl = mkLit(getCellInd(l + 1, j, bOffset, nCols));
      b_lj = params.bmf_symbreak == 4 ? b_lj : ~b_lj;
      b_nextl = params.bmf_symbreak == 4 ? b_nextl : ~b_nextl;

      // b_lj <-> sum(Tlj) > 0
      if (Tlj.size())
        cplex->add_impl_objective_constraint(b_lj, Tlj, true);
      else {
        Tlj.push_back(~b_lj);
        cplex->add_clausal_constraint(Tlj);
      }
      // (Z_ij ^ -B_ij) => -B_i+1,j
      cls.insert(cls.end(), {~z_lj, b_lj, ~b_nextl});
      log(3, " (Z_ij ^ -B_ij) => -B_i+1,j", cls);
      cplex->add_clausal_constraint(cls);

      cls.clear();

      if (j == nCols - 1) continue;
      // (Z_ij ^ B_ij ^ B_i+1,j) => Z_i,j+1
      cls.insert(cls.end(), {~z_lj, ~b_lj, ~b_nextl, z_nextj});
      log(3, "(Z_ij ^ B_ij ^ B_i+1,j) => Z_i,j+1", cls);
      cplex->add_clausal_constraint(cls);
      cls.clear();

      // (Z_ij ^ -B_ij ^ -B_i+1,j) => Z_i,j+1
      cls.insert(cls.end(), {~z_lj, b_lj, b_nextl, z_nextj});
      log(3, "(Z_ij ^ -B_ij ^ -B_i+1,j) => Z_i,j+1", cls);
      cplex->add_clausal_constraint(cls);
      cls.clear();
    }
  }

  for (int l = 0; l < k; l++) {
    // Z_i,0
    cls.clear();
    Lit z_l0 = mkLit(getCellInd(l, 0, zOffset, nCols));
    cls.push_back(z_l0);
    log(3, "z0", cls);
    cplex->add_clausal_constraint(cls);
  }
}

#endif
