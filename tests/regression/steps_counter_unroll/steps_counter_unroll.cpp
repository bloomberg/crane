#include <steps_counter_unroll.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<StepsCounterUnroll::state>
StepsCounterUnroll::step(std::shared_ptr<StepsCounterUnroll::state> s) {
  return std::make_shared<StepsCounterUnroll::state>(
      state{((std::move(s)->pc + 1u) % 4096u)});
}

std::shared_ptr<StepsCounterUnroll::state>
StepsCounterUnroll::steps(const unsigned int n,
                          std::shared_ptr<StepsCounterUnroll::state> s) {
  if (n <= 0) {
    return std::move(s);
  } else {
    unsigned int n_ = n - 1;
    return steps(std::move(n_), step(s));
  }
}
