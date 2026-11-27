#include "st_dead_ref_loop_param.h"

uint64_t StDeadRefLoopParam::st_1(STRefs) {
  std::pair<uint64_t, uint64_t> r0 = std::make_pair(UINT64_C(2), UINT64_C(1));
  auto h = [](uint64_t k, uint64_t) -> uint64_t {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    while (true) {
      if (k <= 0) {
        return UINT64_C(5);
      } else {
        uint64_t k_ = k - 1;
        k = k_;
      }
    }
  };
  uint64_t y = h(UINT64_C(4), UINT64_C(1));
  auto [a, b] = r0;
  return (((y * UINT64_C(10)) + a) + b);
}
