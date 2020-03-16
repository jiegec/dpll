//
// DPLL algorithm.
//

#include "DPLL.h"
#include <algorithm>

// #define DEBUG
#ifdef DEBUG
#define DBG(...) printf(__VA_ARGS__)
#else
#define DBG(...)
#endif

const uint32_t INVALID_CLAUSE = 0xFFFFFFFF;

bool DPLL::check_sat() {
  // sort literals
  for (uint32_t i = 0; i < phi.clauses.size(); i++) {
    // index conversion
    for (uint32_t j = 0; j < phi.clauses[i].size(); j++) {
      uint32_t index;
      if (phi.clauses[i][j] > 0) {
        index = phi.clauses[i][j] * 2 - 2;
      } else {
        index = phi.clauses[i][j] * -2 - 1;
      }
      phi.clauses[i][j] = index;
    }
    std::sort(phi.clauses[i].begin(), phi.clauses[i].end());
    for (uint32_t j = 0; j < phi.clauses[i].size() - 1; j++) {
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
  for (uint32_t i = 0; i < phi.clauses.size(); i++) {
    struct ClauseInfo clause;
    clause.num_unassigned = 0;
    clause.is_satisfied = false;
    for (uint32_t j = 0; j < phi.clauses[i].size(); j++) {
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
  for (uint32_t i = 0; i < clauses.size(); i++) {
    if (clauses[i].num_unassigned == 0 && !clauses[i].is_satisfied) {
      // unsatisfied && no unassigned
      return false;
    }
  }

#ifdef CDCL
  backtrack_level = 0;
#endif
  bool res = dpll();
  if (res) {
    // fill unused variables
    for (uint32_t i = 1; i <= phi.num_variable; i++) {
      if (m.find(i) == m.end()) {
        // not found
        m[i] = true;
      }
    }
  }
  return res;
}

bool DPLL::dpll() {
  DBG("depth: %d\n", stack.size());

  // check if all clauses are satisfied
  if (num_sat == clauses.size())
    return true;

  // decision loop
  // should have a stack with:
  // 1. empty
  // 2. top element of type TYPE_DECIDE
  do {
    if (num_sat == clauses.size())
      return true;

    // find unit clause
    bool has_unit = false;
    bool backtrack = false;
    do {
      has_unit = false;
      for (uint32_t i = 0; i < clauses.size(); i++) {
        ClauseInfo &clause = clauses[i];
        if (!clause.is_satisfied && clause.num_unassigned == 1) {
          // unit clause
          has_unit = true;
          for (uint32_t index : clause.literals) {
            if (!literals[index].is_assigned) {
              // found unit literal
              if (setLiteral(index, TYPE_IMPLIED)) {
                // conflict
                backtrack = true;
                has_unit = false;
                goto next;
              }
              break;
            }
          }
        }
      }
    } while (has_unit);
next:

    if (num_sat == clauses.size())
      return true;

    // find pure literals
    for (uint32_t i = 0; i < literals.size(); i++) {
      LiteralInfo &literal = literals[i];
      if (!literal.is_assigned && literal.cur_clauses == 0) {
        uint32_t neg = i ^ 1;
        // found pure literal
        if (setLiteral(neg, TYPE_IMPLIED)) {
          // conflict
          unsetLiteral();
          backtrack = true;
          break;
        }
      }
    }

    if (num_sat == clauses.size())
      return true;

    if (!backtrack) {
      // decide a new variable
      backtrack = true;
      for (uint32_t i = 0; i < literals.size(); i++) {
        if (!literals[i].is_assigned) {
          if (setLiteral(i, TYPE_DECIDE)) {
            backtrack = true;
          } else {
            backtrack = false;
          }
          break;
        }
      }
    }

    while (backtrack && !stack.empty()) {
      // backtrack to last TYPE_DECIDE
      while (!stack.empty() && stack.top().type == TYPE_IMPLIED) {
        unsetLiteral();
      }
      if (!stack.empty() && stack.top().type == TYPE_DECIDE) {
        // decide a new variable from last off
        Change change = stack.top();
        unsetLiteral();
        for (uint32_t i = change.assigned_literal + 1; i < literals.size();
             i++) {
          if (!literals[i].is_assigned) {
            if (setLiteral(i, TYPE_DECIDE)) {
              unsetLiteral();
              break;
            } else {
              backtrack = false;
              break;
            }
          }
        }
      }
    }

  } while (!stack.empty());

  return false;
}

model DPLL::get_model() {
  // TODO: your code here, or in the header file
  return m;
}

// return true when conflict is found
bool DPLL::setLiteral(uint32_t index, ChangeType type) {
  DBG("set%s%d to true: %s\n", index % 2 == 0 ? " " : " -", index / 2 + 1,
      type == TYPE_DECIDE ? "decide" : "implied");
  int neg_index = index ^ 1;
  literals[index].is_assigned = true;
  literals[neg_index].is_assigned = true;
  m[(index >> 1) + 1] = !(index & 1);

  struct Change change;
  change.type = type;
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
      conflict = true;
    }
  }
  stack.push(change);
  return conflict;
}

void DPLL::unsetLiteral() {
  Change change = stack.top();
  stack.pop();
  int index = change.assigned_literal;
  DBG("unset%s%d\n", index % 2 == 0 ? " " : " -", index / 2 + 1);
  int neg_index = index ^ 1;
  literals[index].is_assigned = false;
  literals[neg_index].is_assigned = false;

  // re-add current literal
  for (uint32_t clause_index : literals[index].clauses) {
    clauses[clause_index].num_unassigned += 1;
  }
  // re-add negative literal
  for (uint32_t clause_index : literals[neg_index].clauses) {
    clauses[clause_index].num_unassigned += 1;
  }
  // re-add removed clauses
  for (uint32_t i = change.removed_clauses_begin; i < removed_clauses.size();
       i++) {
    uint32_t clause_index = removed_clauses[i];
    clauses[clause_index].is_satisfied = false;
    num_sat -= 1;
    for (int literal_index : clauses[clause_index].literals) {
      literals[literal_index].cur_clauses += 1;
    }
  }
  removed_clauses.resize(change.removed_clauses_begin);
}