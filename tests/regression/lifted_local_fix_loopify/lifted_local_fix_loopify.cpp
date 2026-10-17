#include "lifted_local_fix_loopify.h"

uint64_t LiftedLocalFixLoopify::total_length(const List<List<uint64_t>> &l) {
  return (total_length_crane_len(l, UINT64_C(0)) +
          total_length_crane_len(l.template concat<uint64_t>(), UINT64_C(0)));
}

uint64_t LiftedLocalFixLoopify::weighted(const List<List<uint64_t>> &l) {
  return (weighted_crane_sum_all(
              [](const List<uint64_t> &xs) {
                return weighted_crane_sum_all([](uint64_t n) { return n; }, xs);
              },
              l) +
          weighted_crane_sum_all(
              [](const List<uint64_t> &) { return UINT64_C(1); }, l));
}
