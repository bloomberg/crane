#include <algorithm>
#include <any>
#include <cassert>
#include <count_loop_test_target.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<CountLoopTestTarget::instruction>
CountLoopTestTarget::count_loop_test(const unsigned int loop_addr) {
  return instruction::ctor::ISZ_(0, std::move(loop_addr));
}

unsigned int CountLoopTestTarget::target_of(
    const std::shared_ptr<CountLoopTestTarget::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename CountLoopTestTarget::instruction::ISZ _args)
                     -> unsigned int {
                   unsigned int a = _args._a1;
                   return std::move(a);
                 },
                 [](const typename CountLoopTestTarget::instruction::NOP _args)
                     -> unsigned int { return 0; }},
      i->v());
}
