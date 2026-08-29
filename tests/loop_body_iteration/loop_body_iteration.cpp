#include "loop_body_iteration.h"

uint64_t LoopBodyIteration::get_reg0(const LoopBodyIteration::state &s) {
  return ListDef::template nth<uint64_t>(UINT64_C(0), s.regs_, UINT64_C(0));
}

LoopBodyIteration::state
LoopBodyIteration::count_loop_body(const LoopBodyIteration::state &s) {
  return state{update_nth<uint64_t>(
      UINT64_C(0),
      (UINT64_C(16) ? (get_reg0(s) + UINT64_C(1)) % UINT64_C(16)
                    : (get_reg0(s) + UINT64_C(1))),
      s.regs_)};
}

LoopBodyIteration::state
LoopBodyIteration::iterate_body(uint64_t n, LoopBodyIteration::state s) {
  if (n <= 0) {
    return s;
  } else {
    uint64_t n_ = n - 1;
    return iterate_body(n_, count_loop_body(std::move(s)));
  }
}
