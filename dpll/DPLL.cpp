//
// DPLL algorithm.
//

#include "DPLL.h"

//#define DEBUG
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

  num_sat = 0;
  num_unsat = 0;
  for (int i = 0; i < clauses.size(); i++) {
    if (clauses[i].num_unassigned == 0 && !clauses[i].is_satisfied) {
      // unsatisfied && no unassigned
      return false;
    }
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
  if (num_sat == clauses.size())
    return true;
  if (num_unsat)
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
            if (setLiteral(index, stack)) {
              // conflict
              goto backtrack;
            }
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
      if (setLiteral(neg, stack)) {
        // conflict
        goto backtrack;
      }
    }
  }

  // check sat/unsat again
  if (num_sat == clauses.size())
    return true;
  if (num_unsat) {
    goto backtrack;
  }

  // choose one unassigned literal
  for (int i = 0; i < literals.size(); i++) {
    if (!literals[i].is_assigned) {
      // try to assign it
      setLiteral(i, stack);
      if (dpll()) {
        // satisfied
        return true;
      }
      unsetLiteral(stack);
      // try to assign it's negative literal
      int neg = i ^ 1;
      setLiteral(neg, stack);
      if (dpll()) {
        // satisfied
        return true;
      }
      unsetLiteral(stack);

      break;
    }
  }

backtrack:
  // backtrack
  while (!stack.empty()) {
    unsetLiteral(stack);
  }
  return false;
}

model DPLL::get_model() {
  // TODO: your code here, or in the header file
  return model;
}

// return true when conflict is found
bool DPLL::setLiteral(uint32_t index, std::stack<Change> &stack) {
  DBG("set %d to true\n", index);
  int neg_index = index ^ 1;
  literals[index].is_assigned = true;
  literals[neg_index].is_assigned = true;
  model[(index >> 1) + 1] = !(index & 1);

  struct Change change;
  change.assigned_literal = index;
  change.removed_clauses_begin = removed_clauses.size();

  // remove current literal
  for (int clause_index : literals[index].clauses) {
    clauses[clause_index].num_unassigned -= 1;
    if (!clauses[clause_index].is_satisfied) {
      num_sat += 1;
      clauses[clause_index].is_satisfied = true;
      for (int literal_index : clauses[clause_index].literals) {
        literals[literal_index].cur_clauses -= 1;
      }
      removed_clauses.push_back(clause_index);
    }
  }
  // remove negative literal
  bool conflict = false;
  for (int clause_index : literals[neg_index].clauses) {
    clauses[clause_index].num_unassigned -= 1;
    if (clauses[clause_index].num_unassigned == 0 &&
        !clauses[clause_index].is_satisfied) {
      num_unsat += 1;
      conflict = true;
    }
  }
  stack.push(change);
  return conflict;
}

void DPLL::unsetLiteral(std::stack<Change> &stack) {
  Change change = stack.top();
  stack.pop();
  int index = change.assigned_literal;
  DBG("unset %d\n", index);
  int neg_index = index ^ 1;
  literals[index].is_assigned = false;
  literals[neg_index].is_assigned = false;

  // re-add current literal
  for (int clause_index : literals[index].clauses) {
    clauses[clause_index].num_unassigned += 1;
  }
  // re-add negative literal
  for (int clause_index : literals[neg_index].clauses) {
    if (clauses[clause_index].num_unassigned == 0 &&
        !clauses[clause_index].is_satisfied) {
      num_unsat -= 1;
    }
    clauses[clause_index].num_unassigned += 1;
  }
  // re-add removed clauses
  for (int i = change.removed_clauses_begin; i < removed_clauses.size(); i++) {
    uint32_t clause_index = removed_clauses[i];
    clauses[clause_index].is_satisfied = false;
    num_sat -= 1;
    for (int literal_index : clauses[clause_index].literals) {
      literals[literal_index].cur_clauses += 1;
    }
  }
  removed_clauses.resize(change.removed_clauses_begin);
}