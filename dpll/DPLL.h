//
// DPLL algorithm.
//

#ifndef DPLL_DPLL_H
#define DPLL_DPLL_H

#include "common.h"
#include <stack>
#include <stdint.h>

struct LiteralInfo {
  // immutable
  std::vector<uint32_t> clauses;
  std::vector<uint32_t> clause_index;
  // mutable
  uint32_t cur_clauses;
  bool is_assigned;
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
  uint32_t removed_clause;
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
  model model;
  std::vector<LiteralInfo> literals;
  std::vector<ClauseInfo> clauses;

  bool dpll();
  void setLiteral(uint32_t index);
  void unsetLiteral(uint32_t index);
};

#endif // DPLL_DPLL_H
