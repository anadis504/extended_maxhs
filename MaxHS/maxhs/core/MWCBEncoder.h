#ifndef MwcbEncoder_h
#define MwcbEncoder_h

#include "maxhs/core/MaxSolver.h"
#include "maxhs/core/Wcnf.h"
#include "maxhs/core/totalizer.h"
#include "maxhs/ifaces/Cplex.h"

int t = 2;
int s = 2;
int k = 2;
int n, m;

std::set<Lit> added_dijs;

static void encode_matrice_reals(Wcnf* F, vector<vector<double>>& MatriceX,
                                 bool verify) {
  int newVarOffset = 0;
  n = MatriceX.size();
  m = MatriceX[0].size();

  if (params.mwcb_k) k = params.mwcb_k;
  if (params.mwcb_s) s = params.mwcb_s;
  if (params.mwcb_t) t = params.mwcb_t;

  for (auto row : MatriceX) {
    vector<Lit> dij_row;
    F->matr.addVec(row);
    for (size_t i = 0; i < row.size(); i++) {
      dij_row.push_back(mkLit(newVarOffset++));
    }
    F->d_vars.addVec(dij_row);
    F->update_maxorigvar(dij_row);
  }
  double upper_bound{};
  for (int j = 0; j < m; j++) {
    vector<double> col;
    for (int i = 0; i < n; i++) {
      col.push_back(MatriceX[i][j]);
    }
    std::sort(col.begin(), col.end());
    F->ranks_by_col.addVec(col);
    upper_bound += (col[col.size() - 1] - col[0]);
    F->lb_vec.push_back(var(mkLit(newVarOffset++)));
    F->ub_vec.push_back(var(mkLit(newVarOffset++)));
  }
  for (int i = 0; i < n; i++) {
    F->y_vars.push_back(mkLit(newVarOffset++));
  }
  for (uint32_t i = 0; i < F->ranks_by_col.size(); i++) {
    log(4, F->ranks_by_col.getVec(i));
  }
  for (uint32_t i = 0; i < F->d_vars.size(); i++) {
    log(2, "The d-vars rowwise: ", F->d_vars.getVec(i));
    auto dij_row = F->d_vars.getVec(i);
    auto yi = F->y_vars[i];
    Totalizer tot(F, newVarOffset++);
    newVarOffset = tot.build(dij_row, dij_row.size() - s);
    auto o_s = tot.getOutLit(m - s);
    F->addHardClause(~o_s, yi);
    log(0, "totalizer -o^(m-s) or yi: ", o_s, ' ', yi);
  }
  Totalizer tot(F, newVarOffset++);
  newVarOffset = tot.build(F->y_vars, k);
  auto o_yn = tot.getOutLit(k);
  F->addHardClause(~o_yn);
  log(2, "Amount of vars in model: ", F->nVars(),
      ", with initial maximum cost: ", upper_bound);
  F->set_dimacs_params(newVarOffset, 0, upper_bound);
};

void init_cplex(Wcnf* F, MaxHS_Iface::Cplex* cplex) {
  vector<std::pair<double, double>> lower_bounds{};
  vector<std::pair<double, double>> upper_bounds{};
  for (auto col : F->ranks_by_col) {
    lower_bounds.push_back(std::make_pair(col[0], col[t]));
    log(2, "lower bounds ", col[0], ' ', col[t]);
    upper_bounds.push_back(
        std::make_pair(col[col.size() - t - 1], col[col.size() - 1]));
    log(2, "upper bounds ", upper_bounds[upper_bounds.size() - 1].first, ' ',
        upper_bounds[upper_bounds.size() - 1].second);
  }
  for (int i = 0; i < (int)F->ranks_by_col.size(); i++) {
    auto col = F->ranks_by_col.getVec(i);
    log(2, col);
  }
  cplex->init_lu_vecs(m, lower_bounds, F->lb_vec, upper_bounds, F->ub_vec);

  for (size_t i = 0; i < F->d_vars.size(); i++) {
    auto di = F->d_vars.getVec(i);
    auto xi = F->matr.getVec(i);
    vector<double> coeffs{};
    for (int j = 0; j < m; j++) {
      Var lj = F->lb_vec[j];
      Var uj = F->ub_vec[j];
      double Ml = lower_bounds[j].second - lower_bounds[j].first;
      double Mu = upper_bounds[j].second - upper_bounds[j].first;

      cplex->add_Big_M_constr(vector<Lit>{mkLit(lj), di[j]},
                              vector<double>{1, -Ml}, xi[j], 'L');
      cplex->add_Big_M_constr(vector<Lit>{mkLit(uj), di[j]},
                              vector<double>{1, Mu}, xi[j], 'G');
    }
    if (params.mwcb < 2) {
      coeffs.clear();
      coeffs.resize(m, 1);
      coeffs.push_back(-(m - s));
      di.push_back(F->y_vars[i]);
      log(4, F->d_vars.getVec(i));
      cplex->add_Big_M_constr(di, coeffs, s, 'L');
    }
  }
  for (int j = 0; j < m; j++) {
    vector<Lit> d_vec{};
    for (int i = 0; i < n; i++) {
      d_vec.push_back(F->d_vars.getVec(i)[j]);
    }
    cplex->add_cardinality_constraint(d_vec, t, 'L');
  }
  if (params.mwcb < 2) cplex->add_cardinality_constraint(F->y_vars, k, 'L');
};

bool checkMWCBEModel(Wcnf* F, vector<double>& lb, vector<double> ub) {
  std::map<int, int> rowwise_out;
  std::map<int, int> colwise_out;
  int yCount = 0;
  log(0, "k, t, s ", k, ' ', t, ' ', s);
  for (size_t i = 0; i < F->matr.size(); i++) {
    auto row = F->matr.getVec(i);
    for (size_t j = 0; j < row.size(); j++) {
      auto xij = row[j];
      if ((xij < lb[j] && fabs(lb[j] - xij) > params.tolerance) ||
          (xij > ub[j] && fabs(xij - ub[j]) > params.tolerance)) {
        /*        if (fabs(lb[j] - xij) > params.tolerance ||
                   fabs(xij - ub[j]) > params.tolerance) { */
        if (rowwise_out[i]) {
          rowwise_out[i]++;
        } else {
          rowwise_out[i] = 1;
        }
        if (colwise_out[j]) {
          colwise_out[j]++;
        } else {
          colwise_out[j] = 1;
        }
        log(4, "sum(d", i, ")^", j, " = ", colwise_out[j]);
        log(4, "xij = ", xij, ", lb = ", lb[j], ", ub = ", ub[j]);
        if (yCount > k || colwise_out[j] > t) {
          log(0, "Incorrect model with sum(y) =", yCount, ", and sum d(", j,
              ")=", colwise_out[j]);
          return false;
        }
      }
    }

    if (rowwise_out[i] > s) yCount++;
    log((rowwise_out[i] ? 3 : 6), "sum(y_", i, ") = ", rowwise_out[i]);
  }
  for (size_t j = 0; j < colwise_out.size(); j++) {
    log(3, "sum(d)^", j, " = ", colwise_out[j]);
  }
  return true;
}

bool checkCplexSol(Wcnf* F, vector<Lit>& soln) {
  auto y_vars = F->y_vars;
  int yCount = 0;
  int nonYCount = 0;
  Lit maxY = y_vars[y_vars.size() - 1];
  vector<Lit> pos_y;
  for (auto l : soln) {
    if (var(l) > var(maxY)) break;
    if (std::find(y_vars.begin(), y_vars.end(), l) != y_vars.end()) {
      yCount++;
      pos_y.push_back(l);
    }
    if (std::find(y_vars.begin(), y_vars.end(), ~l) != y_vars.end()) {
      nonYCount++;
      pos_y.push_back(l);
    }
  }
  log(2, "The assignment over y_vars", pos_y, yCount, ' ', nonYCount);

  vector<Lit> v_intersection;
  std::set_intersection(y_vars.begin(), y_vars.end(), soln.begin(), soln.end(),
                        std::back_inserter(v_intersection));

  if (params.verbosity > 0) {
    log(0, "printing out the positively assigned y_vars");
    for (auto n : v_intersection) cout << n << ' ';
    cout << '\n';
  }

  if (yCount > k) return false;
  return true;
}

#endif
