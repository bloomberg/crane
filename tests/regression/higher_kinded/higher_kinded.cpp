#include "higher_kinded.h"

uint64_t HigherKinded::tree_sum(const HigherKinded::Tree<uint64_t> &t) {
  return tree_fold<uint64_t, uint64_t>(
      [](uint64_t x) { return x; },
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }, t);
}
