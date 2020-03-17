//
// DPLL algorithm.
//

#ifndef DPLL_DPLL_H
#define DPLL_DPLL_H

#include "common.h"
#include <deque>
#include <stdint.h>

// Conflict driven clause learning
// #define CDCL
#define DEBUG

enum ChangeType { TYPE_DECIDE, TYPE_IMPLIED };

struct LiteralInfo {
  // immutable
  std::vector<uint32_t> clauses;
  std::vector<uint32_t> clause_index;
  // mutable
  uint32_t cur_clauses;
  bool is_assigned;
#ifdef CDCL
  uint32_t unit_clause;
  uint32_t assign_depth;
#endif
};

struct ClauseInfo {
  // immutable
  std::vector<uint32_t> literals;
  // mutable
  uint32_t num_unassigned;
  bool is_satisfied;
};

struct Change {
  uint32_t assigned_literal;
  uint32_t removed_clauses_begin;
  ChangeType type;
};

class DPLL {
public:
  /**
   * Constructor.
   *
   * @param phi the formula to be checked
   * @note Please DON'T CHANGE this signature because the grading script will
   * directly call this function!
   */
  DPLL(const formula &phi) : phi(phi) {}

  /**
   * Check if the formula is satisfiable.
   *
   * @return true if satisfiable, and false if unsatisfiable
   * @note Please DON'T CHANGE this signature because the grading script will
   * directly call this function!
   */
  bool check_sat();

  /**
   * Get a satisfying model (interpretation) of the formula, the model must be
   * *complete*, that is, it must assign every variable a truth value. This
   * function will be called if and only if `check_sat()` returns true.
   *
   * @return an arbitrary (if there exist many) satisfying model
   * @note Please DON'T CHANGE this signature because the grading script will
   * directly call this function!
   */
  model get_model();

private:
  formula phi;
  model m;
  std::deque<Change> stack;
  std::vector<LiteralInfo> literals;
  std::vector<ClauseInfo> clauses;
  std::vector<uint32_t> removed_clauses;
  uint32_t num_sat;
#ifdef CDCL
  uint32_t backtrack_level;
#endif
#ifdef DEBUG
  uint32_t num_set;
  uint32_t num_unset;
#endif

  bool dpll();
  bool setLiteral(uint32_t index, ChangeType type);
  void unsetLiteral();
};

#endif // DPLL_DPLL_H
