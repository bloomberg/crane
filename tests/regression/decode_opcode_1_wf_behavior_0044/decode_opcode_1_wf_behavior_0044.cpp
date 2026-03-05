#include <algorithm>
#include <any>
#include <cassert>
#include <decode_opcode_1_wf_behavior_0044.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int DecodeOpcode1WfBehavior0044::acc(
    const std::shared_ptr<DecodeOpcode1WfBehavior0044::state> &s) {
  return s->acc;
}

unsigned int DecodeOpcode1WfBehavior0044::cycles(
    const std::shared_ptr<DecodeOpcode1WfBehavior0044::state> &_x,
    const DecodeOpcode1WfBehavior0044::instruction _x0) {
  return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
}

unsigned int DecodeOpcode1WfBehavior0044::program_cycles(
    const std::shared_ptr<DecodeOpcode1WfBehavior0044::state> &s,
    const std::shared_ptr<List<DecodeOpcode1WfBehavior0044::instruction>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<DecodeOpcode1WfBehavior0044::instruction>::nil
                 _args) -> unsigned int { return 0; },
          [&](const typename List<DecodeOpcode1WfBehavior0044::instruction>::
                  cons _args) -> unsigned int {
            DecodeOpcode1WfBehavior0044::instruction i = _args._a0;
            std::shared_ptr<List<DecodeOpcode1WfBehavior0044::instruction>>
                rest = _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
