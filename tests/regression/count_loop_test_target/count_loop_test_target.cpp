#include "count_loop_test_target.h"

CountLoopTestTarget::instruction
CountLoopTestTarget::count_loop_test(unsigned int loop_addr) {
  return instruction::isz(0u, loop_addr);
}

unsigned int
CountLoopTestTarget::target_of(const CountLoopTestTarget::instruction &i) {
  if (std::holds_alternative<typename CountLoopTestTarget::instruction::ISZ>(
          i.v())) {
    const auto &[a0, a1] =
        std::get<typename CountLoopTestTarget::instruction::ISZ>(i.v());
    return a1;
  } else {
    return 0u;
  }
}
