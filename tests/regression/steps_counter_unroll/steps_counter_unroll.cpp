#include <steps_counter_unroll.h>

#include <memory>
#include <type_traits>
#include <utility>

std::shared_ptr<StepsCounterUnroll::state>
StepsCounterUnroll::step(std::shared_ptr<StepsCounterUnroll::state> s) {
  return std::make_shared<StepsCounterUnroll::state>(
      state{(4096u ? (s->pc + 1u) % 4096u : (s->pc + 1u))});
}

std::shared_ptr<StepsCounterUnroll::state>
StepsCounterUnroll::steps(const unsigned int n,
                          std::shared_ptr<StepsCounterUnroll::state> s) {
  if (n <= 0) {
    return s;
  } else {
    unsigned int n_ = n - 1;
    return steps(n_, step(std::move(s)));
  }
}
