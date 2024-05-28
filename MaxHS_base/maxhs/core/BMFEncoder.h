#ifndef MBFEncoder_h
#define MBFEncoder_h
#include <map>
#include <set>

#include "maxhs/core/Wcnf.h"
#include "maxhs/core/totalizer.h"

int aOffset, bOffset, mRows, nCols, k;

int getCellInd(int iRow, int jCol, int offset, int numCols) {
  return offset + iRow * numCols + jCol;
};

// args: i, j, l, m = #rows, n = #cols
int getTcellInd(int iRow, int jCol, int l, int numRows, int numCols) {
  return (l * numCols * numRows) + (iRow * numCols) + jCol;
};

void print_matrices(vector<lbool>& model) {
  FILE *fptr;
  fptr = fopen("A.csv", "w");
  for (int i = 0; i < mRows; i++) {
    for (int j = 0; j < k; j++) {
      Var a_ij = getCellInd(i, j, aOffset, k); 
      fprintf(fptr, model[a_ij] == l_True ? "1" : "0");
      fprintf(fptr, j < k-1 ? "," : "\n");
    }
  }
  fclose(fptr);
  fptr = fopen("B.csv", "w");
  for (int i = 0; i < k; i++) {
    for (int j = 0; j < nCols; j++) {
      Var b_ij = getCellInd(i, j, bOffset, nCols); 
      fprintf(fptr, model[b_ij] == l_True ? "1" : "0");
      fprintf(fptr, j < nCols-1 ? "," : "\n");
    }
  }
  fclose(fptr);
};

static void encode_matrice(Wcnf *F, vector<vector<int>> &MatriceX, int _k,
                           bool verify) {
  mRows = MatriceX.size();
  nCols = MatriceX[0].size();
  k = _k;

  // key: s_ij, value: (i,j)
  std::map<int, std::tuple<int, int>> onesCoord;
  // the set of s_ij vars
  std::set<int> ones;

  vector<Lit> cls;

  aOffset = 0;
  bOffset = mRows * k;
  int tOffset = bOffset + k * nCols;
  int newVarOffset = tOffset + k * nCols * mRows;
  int zOffset = 0;

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
          cls.push_back(mkLit(t_lij));
        }
        for (int l = 0; l < k; l++) {
          int a_il = getCellInd(i, l, aOffset, k);
          int b_lj = getCellInd(l, j, bOffset, nCols);
          F->addHardClause(~cls[l], mkLit(a_il));
          F->addHardClause(~cls[l], mkLit(b_lj));
        }
        int s_ij = newVarOffset++;
        cls.push_back(~mkLit(s_ij));
        F->addHardClause(cls);
        ones.insert(s_ij);
        onesCoord[s_ij] = std::make_tuple(i, j);
      }
    }
  }

  if (params.bmf_card_gen > 0 && !verify) {
    std::set<int> onesToCheck(ones.begin(), ones.end());
    while (true) {
      // log(0, "Ones to test: ", onesToCheck.size());
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
          // log(0, "X[i'][j]=", MatriceX[ii][j], " X[i][j']=",MatriceX[i][jj]);
        }
        if (allIncomp) {
          incompatibles.insert(oneCell);
        }
      }
      if (incompatibles.empty()) break;
      if (params.bmf_card_gen == 3 && incompatibles.size() > 1) {
        for (int l = 0; l < k; l++) {
          cls.clear();
          for (auto s_ij : incompatibles) {
            int i = std::get<0>(onesCoord[s_ij]);
            int j = std::get<1>(onesCoord[s_ij]);
            int t_lij = tOffset + getTcellInd(i, j, l, mRows, nCols);
            cls.push_back(mkLit(t_lij));
          }
          // Cannot be used as a clause after all!
          Totalizer tot(F, newVarOffset++);
          newVarOffset = tot.build(cls, 1);
          // log(0, "Totalizer outlits 0, 1 ", ~tot.getOutLit(0), ' ',~tot.getOutLit(1));
          // log(0, "constraint size: ", incompatibles.size());
          F->addHardClause(~tot.getOutLit(1));
        }
      }
      if ((int)incompatibles.size() <= k) {
        onesToCheck.erase(*onesToCheck.begin());
        continue;
      }
      for (auto el : incompatibles) {
        onesToCheck.erase(el);
      }
      if ((int)incompatibles.size() > k) {
        vector<Lit> constr;
        for (auto s_ij : incompatibles) {
          constr.push_back(~mkLit(s_ij));
          if (params.bmf_card_gen == 1 || params.bmf_card_gen == 3)
            ones.erase(s_ij);  // adding the card constraint to sat solver
                               // requires the soft unit clauses to be deleted
          // When adding only to cplex the soft unit clauses must be preserved
        }
        // Adding the cardinality constraint to cplex solver
        if (params.bmf_card_gen == 1 || params.bmf_card_gen == 3) {
          // log(0, "Adding cardinality constr ", constr, " >= ", k);
          Totalizer tot(F, newVarOffset++);
          newVarOffset = tot.build(constr, constr.size());
          // cout << tot.getNClauses() << ' ' << tot.getNVars() << '\n';
          for (int i = constr.size() - k; i < (int)constr.size(); i++) {
            F->addSoftClause(~tot.getOutLit(i), 1);
          }
          F->addToBaseCost(constr.size() - k);
          // add soft clause o_(n-k), meaning n-k of the s_ij vars must be set
          // to false
        } else {
          F->addCardConstr(constr, incompatibles.size() - k, 'G');
        }
      }
    }
  }
  log(1, "amount of card constraints: ", F->getCardConstraints().size());
  log(1, "Remaining compatible ones ", ones.size());
  // Add the remaining s_ij as unit soft clauses to the formula
  for (auto oneCell : ones) {
    F->addSoftClause(mkLit(oneCell), 1);
  }
  // Symmetry breaking, aux var Z_ij, enforce lex. order on B matr
  if (params.bmf_symbreak && !verify) {
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
  F->set_dimacs_params(F->nVars(), F->nHards() + F->nSofts(), mRows * nCols);
  log(3, "Hards:");
  for (auto cls : F->hards()) {
    log(3, cls.getVec());
  }
  log(3, "Softs:");
  for (auto cls : F->softs()) {
    log(3, cls.getVec());
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

#endif
