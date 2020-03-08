//
// DPLL algorithm.
//

#include "DPLL.h"

#ifdef DEBUG
#define DBG(...) printf(__VA_ARGS__)
#else
#define DBG(...)
#endif

bool DPLL::check_sat() {

  // sort literals
  for (int i = 0; i < phi.clauses.size(); i++) {
    // index conversion
    for (int j = 0; j < phi.clauses[i].size(); j++) {
      uint32_t index;
      if (phi.clauses[i][j] > 0) {
        index = phi.clauses[i][j] * 2 - 2;
      } else {
        index = phi.clauses[i][j] * -2 - 1;
      }
      phi.clauses[i][j] = index;
    }
    std::sort(phi.clauses[i].begin(), phi.clauses[i].end());
    for (int j = 0; j < phi.clauses[i].size() - 1; j++) {
      if (phi.clauses[i][j] + 1 == phi.clauses[i][j + 1] &&
          (phi.clauses[i][j] & 2) == (phi.clauses[i][j + 1] & 2)) {
        // n \lor -n, always true
        // remove it
        if (i < phi.clauses.size() - 1) {
          // swap with last clause
          phi.clauses[i] = phi.clauses[phi.clauses.size() - 1];
        }
        phi.clauses.pop_back();
        i--;
        break;
      }
    }
  }

  literals.resize(2 * phi.num_variable);
  for (int i = 0; i < phi.clauses.size(); i++) {
    struct ClauseInfo clause;
    clause.num_unassigned = 0;
    clause.is_satisfied = false;
    for (int j = 0; j < phi.clauses[i].size(); j++) {
      uint32_t index = phi.clauses[i][j];
      literals[index].clauses.push_back(i);
      literals[index].clause_index.push_back(clause.literals.size());
      literals[index].cur_clauses += 1;
      clause.literals.push_back(index);
      clause.num_unassigned += 1;
    }
    clauses.push_back(clause);
  }

  bool res = dpll();
  if (res) {
    // fill unused variables
    for (int i = 1; i <= phi.num_variable; i++) {
      if (model.find(i) == model.end()) {
        // not found
        model[i] = true;
      }
    }
  }
  return res;
}

bool DPLL::dpll() {
  std::stack<Change> stack;

  // check if all clauses are satisfied
  bool is_sat = true;
  bool is_unsat = false;
  for (int i = 0; i < clauses.size(); i++) {
    if (!clauses[i].is_satisfied) {
      is_sat = false;
    } else if (clauses[i].num_unassigned == 0) {
      // unsatisfied && no unassigned
      is_unsat = true;
    }
    if (is_sat == false && is_unsat == true)
      break;
  }
  if (is_sat)
    return true;
  if (is_unsat)
    return false;

  // find unit clause
  bool has_unit = false;
  do {
    has_unit = false;
    for (int i = 0; i < clauses.size(); i++) {
      ClauseInfo &clause = clauses[i];
      if (!clause.is_satisfied && clause.num_unassigned == 1) {
        // unit clause
        has_unit = true;
        for (int index : clause.literals) {
          if (!literals[index].is_assigned) {
            // found unit literal
            struct Change change;
            change.assigned_literal = index;
            change.removed_clause = i;
            stack.push(change);

            clause.is_satisfied = true;
            // remove current clause
            for (int literal_index : clause.literals) {
              literals[literal_index].cur_clauses -= 1;
            }
            setLiteral(index);
            break;
          }
        }
      }
    }
  } while (has_unit);

  // find pure literal
  for (int i = 0; i < literals.size(); i++) {
    if (!literals[i].is_assigned && literals[i].cur_clauses == 0) {
      // no clauses include this literal
      // set it's negative literal
      int neg = i ^ 1;
      struct Change change;
      change.assigned_literal = neg;
      change.removed_clause = 0xFFFFFFFF;
      stack.push(change);
      setLiteral(neg);
    }
  }

  // check sat/unsat again
  is_sat = true;
  is_unsat = false;
  for (int i = 0; i < clauses.size(); i++) {
    if (!clauses[i].is_satisfied) {
      is_sat = false;
    } else if (clauses[i].num_unassigned == 0) {
      // unsatisfied && no unassigned
      is_unsat = true;
    }
    if (is_sat == false && is_unsat == true)
      break;
  }
  if (is_sat)
    return true;
  if (is_unsat) {
    goto backtrack;
  }

  // choose one unassigned literal
  for (int i = 0; i < literals.size(); i++) {
    if (!literals[i].is_assigned) {
      // try to assign it
      setLiteral(i);
      if (dpll()) {
        // satisfied
        return true;
      }
      unsetLiteral(i);
      // try to assign it's negative literal
      int neg = i ^ 1;
      setLiteral(neg);
      if (dpll()) {
        // satisfied
        return true;
      }
      unsetLiteral(neg);

      break;
    }
  }

backtrack:
  // backtrack
  while (!stack.empty()) {
    struct Change change = stack.top();
    stack.pop();
    if (change.removed_clause == 0xFFFFFFFF) {
      // pure literal assign
      unsetLiteral(change.assigned_literal);
    } else {
      // unit propagate
      unsetLiteral(change.assigned_literal);
      ClauseInfo &clause = clauses[change.removed_clause];
      clause.is_satisfied = false;
      // re-add current clause
      for (int literal_index : clause.literals) {
        literals[literal_index].cur_clauses += 1;
      }
    }
  }
  return false;
}

model DPLL::get_model() {
  // TODO: your code here, or in the header file
  return model;
}

void DPLL::setLiteral(uint32_t index) {
  DBG("set %d to true\n", index);
  int neg_index = index ^ 1;
  literals[index].is_assigned = true;
  literals[neg_index].is_assigned = true;
  model[(index >> 1) + 1] = !(index & 1);

  // remove current literal
  for (int clause_index : literals[index].clauses) {
    clauses[clause_index].num_unassigned -= 1;
    clauses[clause_index].is_satisfied = true;
  }
  // remove negative literal
  for (int clause_index : literals[neg_index].clauses) {
    clauses[clause_index].num_unassigned -= 1;
  }
}

void DPLL::unsetLiteral(uint32_t index) {
  DBG("unset %d\n", index);
  int neg_index = index ^ 1;
  literals[index].is_assigned = false;
  literals[neg_index].is_assigned = false;

  // re-add current literal
  for (int clause_index : literals[index].clauses) {
    clauses[clause_index].num_unassigned += 1;
    clauses[clause_index].is_satisfied = false;
  }
  // re-add negative literal
  for (int clause_index : literals[neg_index].clauses) {
    clauses[clause_index].num_unassigned += 1;
  }
}