#include "count_loop_test_target.h"

CountLoopTestTarget::instruction
CountLoopTestTarget::count_loop_test(uint64_t loop_addr) {
  return instruction::isz(UINT64_C(0), loop_addr);
}

uint64_t
CountLoopTestTarget::target_of(const CountLoopTestTarget::instruction &i) {
  if (std::holds_alternative<typename CountLoopTestTarget::instruction::ISZ>(
          i.v())) {
    const auto &[a0, a1] =
        std::get<typename CountLoopTestTarget::instruction::ISZ>(i.v());
    return a1;
  } else {
    return UINT64_C(0);
  }
}
