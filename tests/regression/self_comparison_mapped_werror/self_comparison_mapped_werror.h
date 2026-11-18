#pragma once

#include <cstdint>

struct Z {
}; /// A comparison of one variable with itself under the mappings whose

/// guards compare their operands: Z.geb z z would print z >= z and
/// PrimInt63.eqb i i i == i, which -Wtautological-compare rejects
/// under -Werror.  Core folds each to its value, as it does Nat.leb n n
/// (self_comparison_werror).
struct SelfComparisonMappedWerror {
  static bool z_ge_self(int64_t _x);
  static bool z_gt_self(int64_t _x);
  static bool i_eq_self(int64_t _x);
  static bool i_le_self(int64_t _x);
  static bool i_lt_self(int64_t _x);
};
