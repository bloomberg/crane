#include <count_loop_test_target.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) CountLoopTestTarget::instruction
CountLoopTestTarget::count_loop_test(unsigned int loop_addr) {
  return instruction::isz(0u, loop_addr);
}

__attribute__((pure)) unsigned int
CountLoopTestTarget::target_of(const CountLoopTestTarget::instruction &i) {
  if (std::holds_alternative<typename CountLoopTestTarget::instruction::ISZ>(
          i.v())) {
    const auto &[d_a0, d_a1] =
        std::get<typename CountLoopTestTarget::instruction::ISZ>(i.v());
    return d_a1;
  } else {
    return 0u;
  }
}
