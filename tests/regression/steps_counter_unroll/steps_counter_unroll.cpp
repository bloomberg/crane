#include "steps_counter_unroll.h"

StepsCounterUnroll::state
StepsCounterUnroll::step(const StepsCounterUnroll::state &s) {
  return state{(UINT64_C(4096) ? (s.pc + UINT64_C(1)) % UINT64_C(4096)
                               : (s.pc + UINT64_C(1)))};
}

StepsCounterUnroll::state
StepsCounterUnroll::steps(uint64_t n, StepsCounterUnroll::state s) {
  if (n <= 0) {
    return s;
  } else {
    uint64_t n_ = n - 1;
    return steps(n_, step(std::move(s)));
  }
}
