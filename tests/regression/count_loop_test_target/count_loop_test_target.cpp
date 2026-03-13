#include <count_loop_test_target.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<CountLoopTestTarget::instruction>
CountLoopTestTarget::count_loop_test(const unsigned int loop_addr) {
  return instruction::ctor::ISZ_(0u, std::move(loop_addr));
}

__attribute__((pure)) unsigned int CountLoopTestTarget::target_of(
    const std::shared_ptr<CountLoopTestTarget::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename CountLoopTestTarget::instruction::ISZ _args)
                     -> unsigned int {
                   unsigned int a = _args.d_a1;
                   return std::move(a);
                 },
                 [](const typename CountLoopTestTarget::instruction::NOP _args)
                     -> unsigned int { return 0u; }},
      i->v());
}
