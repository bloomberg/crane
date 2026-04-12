#include <loop_body_iteration.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int LoopBodyIteration::get_reg0(
    const std::shared_ptr<LoopBodyIteration::state> &s) {
  return s->regs_->nth(0u, 0u);
}

std::shared_ptr<LoopBodyIteration::state> LoopBodyIteration::count_loop_body(
    const std::shared_ptr<LoopBodyIteration::state> &s) {
  return std::make_shared<LoopBodyIteration::state>(
      state{update_nth<unsigned int>(
          0u, (16u ? (get_reg0(s) + 1u) % 16u : (get_reg0(s) + 1u)),
          s->regs_)});
}

std::shared_ptr<LoopBodyIteration::state>
LoopBodyIteration::iterate_body(const unsigned int n,
                                std::shared_ptr<LoopBodyIteration::state> s) {
  if (n <= 0) {
    return s;
  } else {
    unsigned int n_ = n - 1;
    return iterate_body(n_, count_loop_body(std::move(s)));
  }
}
