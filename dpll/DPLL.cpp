//
// DPLL algorithm.
//

#include "DPLL.h"
#include <algorithm>
#include <set>

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
#ifdef DEBUG
  num_set = 0;
  num_unset = 0;
#endif
  bool res = dpll();
  DBG("set: %d, unset: %d\n", num_set, num_unset);
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
  begin:
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

#ifdef CDCL
              literals[index].unit_clause = i;
#endif
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

    if (!backtrack) {
      // decide a new variable
      backtrack = true;
      for (uint32_t i = 0; i < literals.size(); i += 2) {
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

#ifdef CDCL
    if (backtrack) {
      Change change = stack.back();
      if (change.type == TYPE_IMPLIED) {
        // generate cut from stack top
        uint32_t literal = change.assigned_literal;
        std::set<uint32_t> conflict_literals_pending;
        std::set<uint32_t> conflict_literals_visited;
        std::set<uint32_t> conflict_literals;

        for (uint32_t literal_index :
             clauses[literals[literal].unit_clause].literals) {
          conflict_literals_pending.insert(literal_index ^ 1);
        }

        // negation
        literal ^= 1;
        for (uint32_t clause_index : literals[literal].clauses) {
          if (!clauses[clause_index].is_satisfied &&
              clauses[clause_index].num_unassigned == 0) {
            // unit clause for negation literal
            for (uint32_t literal_index : clauses[clause_index].literals) {
              conflict_literals_pending.insert(literal_index ^ 1);
            }
          }
        }

        // find root literals in conflict clause
        conflict_literals_visited = conflict_literals_pending;
        while (!conflict_literals_pending.empty()) {
          uint32_t literal = *conflict_literals_pending.begin();
          conflict_literals_pending.erase(literal);
          uint32_t depth = literals[literal].assign_depth;
          if (stack[depth].assigned_literal == literal &&
              literals[literal].is_assigned) {
            if (stack[depth].type == TYPE_IMPLIED) {
              for (uint32_t literal_index :
                   clauses[literals[literal].unit_clause].literals) {
                literal_index ^= 1;
                if (conflict_literals_visited.find(literal_index) ==
                    conflict_literals_visited.end()) {
                  conflict_literals_pending.insert(literal_index);
                  conflict_literals_visited.insert(literal_index);
                  if (stack[literals[literal_index].assign_depth].type ==
                          TYPE_DECIDE &&
                      stack[literals[literal_index].assign_depth]
                              .assigned_literal == literal_index) {
                    conflict_literals.insert(literal_index);
                  }
                }
              }
            } else {
              conflict_literals.insert(literal);
            }
          }
        }

        if (!conflict_literals.empty()) {
          uint32_t new_depth = 0;
          for (uint32_t literal : conflict_literals) {
            uint32_t depth = literals[literal].assign_depth;
            if (depth > new_depth && stack[depth].assigned_literal == literal) {
              new_depth = depth;
            }
          }

          // insert new clause
          ClauseInfo new_clause;
          new_clause.num_unassigned = 0;
          new_clause.is_satisfied = false;
          DBG("learning: ");
          for (uint32_t literal : conflict_literals) {
            // negate
            literal = literal ^ 1;

            DBG("%s%d", literal % 2 == 0 ? " " : " -", literal / 2 + 1);
            literals[literal].clauses.push_back(clauses.size());
            literals[literal].clause_index.push_back(
                new_clause.literals.size());
            literals[literal].cur_clauses += 1;
            assert(literals[literal].is_assigned);
            assert(stack[literals[literal ^ 1].assign_depth].assigned_literal ==
                   (literal ^ 1));
            assert(stack[literals[literal ^ 1].assign_depth].type ==
                   TYPE_DECIDE);
            assert(m[(literal >> 1) + 1] == (literal & 1));
            new_clause.literals.push_back(literal);
          }
          DBG("\n");
          clauses.push_back(new_clause);

          // backjump to new_depth
          while (stack.size() > new_depth) {
            unsetLiteral();
          }

          /*
                    for (uint32_t i = 0; i < literals.size(); i += 2) {
                      if (!literals[i].is_assigned) {
                        if (setLiteral(i, TYPE_DECIDE)) {
                          backtrack = true;
                        } else {
                          backtrack = false;
                        }
                        break;
                      }
                    }
                    */
          goto begin;
        }
      }
    }
#endif

    while (backtrack && !stack.empty()) {

      // backtrack to last TYPE_DECIDE
      while (!stack.empty() && stack.back().type == TYPE_IMPLIED) {
        unsetLiteral();
      }
      if (!stack.empty() && stack.back().type == TYPE_DECIDE) {
        Change change = stack.back();
        unsetLiteral();
        if ((change.assigned_literal & 1) == 0) {
          // decide the opposite variable from last off
          uint32_t i = change.assigned_literal ^ 1;
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

#ifdef CDCL
  literals[index].assign_depth = stack.size();
#endif
#ifdef DEBUG
  num_set++;
#endif

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
  stack.push_back(change);
  return conflict;
}

void DPLL::unsetLiteral() {
  Change change = stack.back();
  stack.pop_back();
  int index = change.assigned_literal;
  DBG("unset%s%d\n", index % 2 == 0 ? " " : " -", index / 2 + 1);
  int neg_index = index ^ 1;
  literals[index].is_assigned = false;
  literals[neg_index].is_assigned = false;

#ifdef CDCL
  literals[index].assign_depth = 0;
#endif
#ifdef DEBUG
  num_unset++;
#endif

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