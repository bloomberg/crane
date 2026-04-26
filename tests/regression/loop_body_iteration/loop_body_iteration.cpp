#include <loop_body_iteration.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
LoopBodyIteration::get_reg0(const LoopBodyIteration::state &s) {
  return ListDef::template nth<unsigned int>(0u, s.regs_, 0u);
}

__attribute__((pure)) LoopBodyIteration::state
LoopBodyIteration::count_loop_body(const LoopBodyIteration::state &s) {
  return state{update_nth<unsigned int>(
      0u, (16u ? (get_reg0(s) + 1u) % 16u : (get_reg0(s) + 1u)), s.regs_)};
}

__attribute__((pure)) LoopBodyIteration::state
LoopBodyIteration::iterate_body(const unsigned int &n,
                                LoopBodyIteration::state s) {
  if (n <= 0) {
    return s;
  } else {
    unsigned int n_ = n - 1;
    return iterate_body(n_, count_loop_body(s));
  }
}
