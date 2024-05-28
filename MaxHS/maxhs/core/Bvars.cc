/***********[Bvars.cc]
Copyright (c) 2012-2015 Jessica Davies, Fahiem Bacchus

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

***********/

#include "maxhs/core/Bvars.h"

#include <algorithm>
#include <ostream>

Bvars::Bvars(const Wcnf* f)
    : theWcnf{f},
      nBvars{theWcnf->nSofts()},
      nOvars{theWcnf->nVars()},
      clsBlit{theWcnf->nSofts(), Minisat::lit_Undef},
      var_types(theWcnf->nVars()),
      mxNum(theWcnf->nVars(), -1) {
  indexBlit.resize(
      theWcnf->getObjectives().total_size() +
          theWcnf->getImplicationObj().size() * (params.undercover_BMF + 1) +
          theWcnf->getVarsForObjFunc().size() + theWcnf->d_vars.total_size(),
      Minisat::lit_Undef);
  for (auto& cls : theWcnf->hards())
    for (auto l : cls) var_types[var(l)].original = true;
  for (auto& cls : theWcnf->softs())
    for (auto l : cls) var_types[var(l)].original = true;

  int maxbvar = -1;
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    auto scls = theWcnf->softs()[i];
    if (scls.size() == 1)
      clsBlit[i] = ~scls[0];  // blit false means clause must be satisfied
    else
      clsBlit[i] = mkLit(make_newVar());
    maxbvar = std::max(maxbvar, var(clsBlit[i]));
  }

  for (size_t i = 0; i < theWcnf->d_vars.size(); i++) {
    auto dij_row = theWcnf->d_vars.getVec(i);
    for (auto dij : dij_row) {
      if (static_cast<size_t>(var(dij)) >= indexBlit.size()) {
        indexBlit.resize(var(dij) + 1, Minisat::lit_Undef);
      }
      indexBlit[nBvars++] = dij;
      maxbvar = std::max(maxbvar, var(dij));

      var_types[var(dij)].original = true;
      var_types[var(dij)].bvar = true;
    }
  }
  for (auto yi : theWcnf->y_vars) {
    if (static_cast<size_t>(var(yi)) >= indexBlit.size()) {
      indexBlit.resize(var(yi) + 1, Minisat::lit_Undef);
    }
    indexBlit[nBvars++] = yi;
    maxbvar = std::max(maxbvar, var(yi));

    var_types[var(yi)].original = true;
    var_types[var(yi)].bvar = true;
  }

  // mark the lits in the objective functions as blits : the polarization is
  // the same as in the obj. func
  for (size_t i = 0; i < theWcnf->getObjectives().size(); i++) {
    auto cls = theWcnf->getObjective(i);
    /* cout << cls << '\n'; */
    for (auto l : cls) {
      if (!var_types[var(l)].bvar) {
        if (static_cast<size_t>(var(l)) >= indexBlit.size()) {
          indexBlit.resize(var(l) + 1, Minisat::lit_Undef);
        }
        indexBlit[nBvars++] = l;
        maxbvar = std::max(maxbvar, var(l));
      }
      var_types[var(l)].bvar = true;
      // blit appears positive in the "core" (obj. func) -> we want to falsify
      // it
      if (!sign(l)) var_types[var(l)].core_is_pos = true;
    }
  }

  // TW configuration 1
  for (size_t i = 0; i < theWcnf->clausalConstraints().size(); i++) {
    auto cls = theWcnf->clausalConstraints().getVec(i);
    // cout << cls << '\n';
    for (auto l : cls) {
      if (!var_types[var(l)].bvar) {
        if (static_cast<size_t>(var(l)) >= indexBlit.size()) {
          indexBlit.resize(var(l) + 1, Minisat::lit_Undef);
        }
        indexBlit[nBvars++] = mkLit(var(l));
        maxbvar = std::max(maxbvar, var(l));
        var_types[var(l)].bvar = true;
        // These bvars add cost if assigned to true => core_is_pos = false
        var_types[var(l)].core_is_pos = true;
      }
    }
  }

  if (theWcnf->getObjectives().size()) {
    objectiveVar = make_newVar();
    var_types[objectiveVar].objective_value = true;
    // var_types[objectiveVar].bvar = true;  // not bvar, should not appear in
    // the sat solver ever (assumptions)
    cout << "b created objective var B " << objectiveVar << "\n";
  }
  log(3, "in bvars initing impl constr ", theWcnf->getImplicationObj().size(),
      " var_types.size() = ", var_types.size());

  auto varsForObjFunc = theWcnf->getVarsForObjFunc();
  log(2, "amount of vars for obj func ", varsForObjFunc.size());
  for (auto l : theWcnf->getVarsForObjFunc()) {
    if (!var_types[var(l)].bvar) {
      indexBlit[nBvars++] = l;
      maxbvar = std::max(maxbvar, var(l));
    }
    var_types[var(l)].bvar = true;
    var_types[var(l)].objective_value = true;
    // blit will appear positive in the "core"
    if (!sign(l)) var_types[var(l)].core_is_pos = true;
  }

  for (auto impl : theWcnf->getImplicationObj()) {
    if (params.inform_SAT) {
      auto s_ij = impl.first;
      if (!var_types[var(s_ij)].bvar) {
        indexBlit[nBvars++] = s_ij;
        maxbvar = std::max(maxbvar, var(s_ij));
      }
      var_types[var(s_ij)].bvar = true;
      // blit will appear positive in the "core"
      if (!sign(s_ij)) var_types[var(s_ij)].core_is_pos = true;
    }
    auto cls = impl.second;
    log(3, cls);
    for (auto l : cls) {
      if (!var_types[var(l)].bvar) {
        indexBlit[nBvars++] = l;
        maxbvar = std::max(maxbvar, var(l));
      }
      var_types[var(l)].bvar = true;
      // blit will appear positive in the "core"
      if (!sign(l)) var_types[var(l)].core_is_pos = true;
    }
  }
  // Not needed without soft clauses
  bvarCls.resize(maxbvar + 1, -1);

  // Hijacking the bvarCls struct by substituting it with bvarIndex : stores the
  // index of the blit in the index table, in order of occurance during
  // initialization
  bvarIndex.resize(maxbvar + 1, -1);
  for (size_t i = 0; i < nBvars; i++) {
    auto blit = indexBlit[i];
    bvarIndex[var(blit)] = i;
  }

  cnstrIndex.resize(maxbvar + 1, -1);
  for (size_t i = 0; i < theWcnf->getObjectives().size(); i++) {
    auto cls = theWcnf->getObjective(i);
    // cout << cls << i <<" here\n";
    for (auto l : cls) {
      // keep track of the constraint index the blit is from
      cnstrIndex[toIndex(var(l))] = i;
    }
  }

  // Not used if no softies
  for (size_t i = 0; i < theWcnf->nSofts(); i++) {
    auto blit = clsBlit[i];
    bvarCls[var(clsBlit[i])] = i;
    var_types[var(blit)].bvar = true;
    if (!sign(blit)) var_types[var(blit)].core_is_pos = true;
  }

  // process mutexes
  mxNum.resize(n_vars(), -1);
  for (size_t i = 0; i < theWcnf->get_SCMxs().size(); i++) {
    auto& mx = theWcnf->get_SCMxs()[i];
    if (mx.encoding_lit() != Minisat::lit_Undef) {
      var_types[var(mx.encoding_lit())].Var_type::dvar = true;
      mxNum[var(mx.encoding_lit())] = i;
    }
    for (auto l : mx.soft_clause_lits()) {
      var_types[var(l)].in_mutex = true;
      if (!sign(l)) var_types[var(l)].orig_core_is_pos = true;
      mxNum[var(l)] = i;
    }
  }
}

void Bvars::printVars() {
  for (size_t i = 0; i < n_vars(); i++) {
    cout << "Var #" << i + 1 << "." << var_types[i] << "\n";
    cout << "is bvar: " << isBvar(i) << "\n";
    if (isBvar(i)) {
      auto clsi = clsIndex(i);
      Lit blit = litOfCls(clsi);
      cout << "Clause " << clsi << ". blit = " << blit << " "
           << theWcnf->getSoft(clsi) << "\n";
      cout << "coreIsPos(" << blit << ") = " << coreIsPos(blit);
      cout << " sign(" << blit << ") = " << sign(blit);
      cout << " isCore(" << blit << ") = " << isCore(blit) << " isNonCore("
           << blit << ") = " << isNonCore(blit) << "\n";
    }
    if (inMutex(i)) {
      cout << "In mutex " << getMxNum(i) << " "
           << theWcnf->get_SCMxs()[getMxNum(i)] << "\n";
      cout << "orig_IsCore(" << mkLit(i) << ") = " << orig_IsCore(mkLit(i))
           << " orig_IsNonCore(" << mkLit(i)
           << ") = " << orig_IsNonCore(mkLit(i)) << "\n";
    }
    cout << "\n";
  }
}

void Bvars::print_var_types() {
  for (size_t i = 0; i < var_types.size(); i++)
    cout << "Var " << i + 1 << " type = " << var_types[i] << "\n";
}

std::ostream& operator<<(std::ostream& os, const Var_type& x) {
  if (x.original) os << "original ";
  if (x.bvar) os << "bvar ";
  if (x.core_is_pos) os << "core_is_pos ";
  if (x.in_mutex) os << "in_mutex ";
  if (x.orig_core_is_pos) os << "orig_core_is_pos ";
  if (x.dvar) os << "dvar ";
  if (x.summation) os << "summation ";
  if (!x.original && !x.bvar && !x.core_is_pos && !x.in_mutex &&
      !x.orig_core_is_pos && !x.dvar && !x.summation)
    os << "not_in_theory ";

  return os;
}
