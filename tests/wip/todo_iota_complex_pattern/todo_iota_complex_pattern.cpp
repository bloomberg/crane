#include "todo_iota_complex_pattern.h"

unsigned int TodoIotaComplexPattern::sum_triple(
    const TodoIotaComplexPattern::Triple<unsigned int, unsigned int,
                                         unsigned int> &t) {
  const auto &[a0, a1, a2] = t;
  return ((a0 + a1) + a2);
}
