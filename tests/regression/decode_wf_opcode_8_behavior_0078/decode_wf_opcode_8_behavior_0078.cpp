#include <algorithm>
#include <any>
#include <cassert>
#include <decode_wf_opcode_8_behavior_0078.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int DecodeWfOpcode8Behavior0078::acc(
    const std::shared_ptr<DecodeWfOpcode8Behavior0078::state> &s) {
  return s->acc;
}

unsigned int DecodeWfOpcode8Behavior0078::cycles(
    const std::shared_ptr<DecodeWfOpcode8Behavior0078::state> &_x,
    const DecodeWfOpcode8Behavior0078::instruction _x0) {
  return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
}

unsigned int DecodeWfOpcode8Behavior0078::program_cycles(
    const std::shared_ptr<DecodeWfOpcode8Behavior0078::state> &s,
    const std::shared_ptr<List<DecodeWfOpcode8Behavior0078::instruction>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<DecodeWfOpcode8Behavior0078::instruction>::nil
                 _args) -> unsigned int { return 0; },
          [&](const typename List<DecodeWfOpcode8Behavior0078::instruction>::
                  cons _args) -> unsigned int {
            DecodeWfOpcode8Behavior0078::instruction i = _args._a0;
            std::shared_ptr<List<DecodeWfOpcode8Behavior0078::instruction>>
                rest = _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
