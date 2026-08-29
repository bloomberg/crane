#include "todo_iota_complex_pattern.h"

uint64_t TodoIotaComplexPattern::sum_triple(
    const TodoIotaComplexPattern::Triple<uint64_t, uint64_t, uint64_t> &t) {
  const auto &[a0, a1, a2] = t;
  return ((a0 + a1) + a2);
}
