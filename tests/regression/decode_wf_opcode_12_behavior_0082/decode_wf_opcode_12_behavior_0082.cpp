#include <algorithm>
#include <any>
#include <cassert>
#include <decode_wf_opcode_12_behavior_0082.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int DecodeWfOpcode12Behavior0082::acc(
    const std::shared_ptr<DecodeWfOpcode12Behavior0082::state> &s) {
  return s->acc;
}

unsigned int DecodeWfOpcode12Behavior0082::cycles(
    const std::shared_ptr<DecodeWfOpcode12Behavior0082::state> &_x,
    const DecodeWfOpcode12Behavior0082::instruction _x0) {
  return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
}

unsigned int DecodeWfOpcode12Behavior0082::program_cycles(
    const std::shared_ptr<DecodeWfOpcode12Behavior0082::state> &s,
    const std::shared_ptr<List<DecodeWfOpcode12Behavior0082::instruction>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<DecodeWfOpcode12Behavior0082::instruction>::nil
                 _args) -> unsigned int { return 0; },
          [&](const typename List<DecodeWfOpcode12Behavior0082::instruction>::
                  cons _args) -> unsigned int {
            DecodeWfOpcode12Behavior0082::instruction i = _args._a0;
            std::shared_ptr<List<DecodeWfOpcode12Behavior0082::instruction>>
                rest = _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
