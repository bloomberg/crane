#include "todo_iota_complex_pattern.h"

unsigned int TodoIotaComplexPattern::sum_triple(
    const TodoIotaComplexPattern::Triple<unsigned int, unsigned int,
                                         unsigned int> &t) {
  const auto &[a0, a1, a2] = std::get<typename TodoIotaComplexPattern::Triple<
      unsigned int, unsigned int, unsigned int>::MkTriple>(t.v());
  return ((a0 + a1) + a2);
}
