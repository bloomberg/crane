#include <algorithm>
#include <any>
#include <cassert>
#include <decode_opcode_3_wf_behavior_0046.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int DecodeOpcode3WfBehavior0046::acc(
    const std::shared_ptr<DecodeOpcode3WfBehavior0046::state> &s) {
  return s->acc;
}

unsigned int DecodeOpcode3WfBehavior0046::cycles(
    const std::shared_ptr<DecodeOpcode3WfBehavior0046::state> &_x,
    const DecodeOpcode3WfBehavior0046::instruction _x0) {
  return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
}

unsigned int DecodeOpcode3WfBehavior0046::program_cycles(
    const std::shared_ptr<DecodeOpcode3WfBehavior0046::state> &s,
    const std::shared_ptr<List<DecodeOpcode3WfBehavior0046::instruction>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<DecodeOpcode3WfBehavior0046::instruction>::nil
                 _args) -> unsigned int { return 0; },
          [&](const typename List<DecodeOpcode3WfBehavior0046::instruction>::
                  cons _args) -> unsigned int {
            DecodeOpcode3WfBehavior0046::instruction i = _args._a0;
            std::shared_ptr<List<DecodeOpcode3WfBehavior0046::instruction>>
                rest = _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
