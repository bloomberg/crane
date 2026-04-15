#include <count_loop_test_target.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<CountLoopTestTarget::instruction>
CountLoopTestTarget::count_loop_test(const unsigned int loop_addr) {
  return instruction::isz(0u, loop_addr);
}

__attribute__((pure)) unsigned int CountLoopTestTarget::target_of(
    const std::shared_ptr<CountLoopTestTarget::instruction> &i) {
  if (std::holds_alternative<typename CountLoopTestTarget::instruction::ISZ>(
          i->v())) {
    const auto &_m =
        *std::get_if<typename CountLoopTestTarget::instruction::ISZ>(&i->v());
    return _m.d_a1;
  } else {
    return 0u;
  }
}
