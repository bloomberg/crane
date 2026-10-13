#include "no_optimize_fold_left_accumulator.h"

List<uint64_t> NoOptimizeFoldLeftAccumulator::rev_(const List<uint64_t> &l) {
  return l.template fold_left<List<uint64_t>>(
      [](const List<uint64_t> &acc, uint64_t x) {
        return List<uint64_t>::cons(x, acc);
      },
      List<uint64_t>::nil());
}
