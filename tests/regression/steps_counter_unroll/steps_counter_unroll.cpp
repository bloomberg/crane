#include <steps_counter_unroll.h>

__attribute__((pure)) StepsCounterUnroll::state
StepsCounterUnroll::step(const StepsCounterUnroll::state &s) {
  return state{(4096u ? (s.pc + 1u) % 4096u : (s.pc + 1u))};
}

__attribute__((pure)) StepsCounterUnroll::state
StepsCounterUnroll::steps(const unsigned int &n, StepsCounterUnroll::state s) {
  if (n <= 0) {
    return s;
  } else {
    unsigned int n_ = n - 1;
    return steps(n_, step(s));
  }
}
