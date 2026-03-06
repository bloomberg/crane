#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <loop_body_iteration.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
LoopBodyIteration::regs_(const std::shared_ptr<LoopBodyIteration::state> &s) {
  return s->regs_;
}

unsigned int LoopBodyIteration::get_reg0(
    const std::shared_ptr<LoopBodyIteration::state> &s) {
  return s->regs_->nth(0, 0);
}

std::shared_ptr<LoopBodyIteration::state> LoopBodyIteration::count_loop_body(
    std::shared_ptr<LoopBodyIteration::state> s) {
  return std::make_shared<LoopBodyIteration::state>(
      state{update_nth<unsigned int>(
          0,
          ((get_reg0(s) + (0 + 1)) %
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)),
          s->regs_)});
}

std::shared_ptr<LoopBodyIteration::state>
LoopBodyIteration::iterate_body(const unsigned int n,
                                std::shared_ptr<LoopBodyIteration::state> s) {
  if (n <= 0) {
    return std::move(s);
  } else {
    unsigned int n_ = n - 1;
    return iterate_body(std::move(n_), count_loop_body(s));
  }
}
