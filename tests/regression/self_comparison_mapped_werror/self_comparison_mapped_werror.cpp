#include "self_comparison_mapped_werror.h"

/// A comparison of one variable with itself under the mappings whose
/// guards compare their operands: Z.geb z z would print z >= z and
/// PrimInt63.eqb i i i == i, which -Wtautological-compare rejects
/// under -Werror.  Core folds each to its value, as it does Nat.leb n n
/// (self_comparison_werror).
bool SelfComparisonMappedWerror::z_ge_self(int64_t) { return true; }

bool SelfComparisonMappedWerror::z_gt_self(int64_t) { return false; }

bool SelfComparisonMappedWerror::i_eq_self(int64_t) { return true; }

bool SelfComparisonMappedWerror::i_le_self(int64_t _x) { return i_eq_self(_x); }

bool SelfComparisonMappedWerror::i_lt_self(int64_t) { return false; }
