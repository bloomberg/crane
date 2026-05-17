#include "todo_iota_complex_pattern.h"

unsigned int TodoIotaComplexPattern::sum_triple(
    const TodoIotaComplexPattern::Triple<unsigned int, unsigned int,
                                         unsigned int> &t) {
  const auto &[d_a0, d_a1, d_a2] =
      std::get<typename TodoIotaComplexPattern::Triple<
          unsigned int, unsigned int, unsigned int>::MkTriple>(t.v());
  return ((d_a0 + d_a1) + d_a2);
}
