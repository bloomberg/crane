#ifndef INCLUDED_STEPS_COUNTER_UNROLL
#define INCLUDED_STEPS_COUNTER_UNROLL

#include <utility>

struct StepsCounterUnroll {
  struct state {
    uint64_t pc;

    // ACCESSORS
    state clone() const { return state{(*this).pc}; }
  };

  static state step(const state &s);
  static state steps(uint64_t n, state s);
  static inline const uint64_t t = steps(UINT64_C(5), state{UINT64_C(4094)}).pc;
};

#endif // INCLUDED_STEPS_COUNTER_UNROLL
