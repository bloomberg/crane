#ifndef INCLUDED_STEPS_COUNTER_UNROLL
#define INCLUDED_STEPS_COUNTER_UNROLL

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct StepsCounterUnroll {
  struct state {
    unsigned int pc;

    // ACCESSORS
    state clone() const { return state{(*(this)).pc}; }
  };

  static state step(const state &s);
  static state steps(const unsigned int &n, state s);
  static inline const unsigned int t = steps(5u, state{4094u}).pc;
};

#endif // INCLUDED_STEPS_COUNTER_UNROLL
