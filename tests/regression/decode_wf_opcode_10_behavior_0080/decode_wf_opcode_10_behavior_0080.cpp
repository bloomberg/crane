#include <algorithm>
#include <any>
#include <cassert>
#include <decode_wf_opcode_10_behavior_0080.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int DecodeWfOpcode10Behavior0080::acc(
    const std::shared_ptr<DecodeWfOpcode10Behavior0080::state> &s) {
  return s->acc;
}

unsigned int DecodeWfOpcode10Behavior0080::cycles(
    const std::shared_ptr<DecodeWfOpcode10Behavior0080::state> &_x,
    const DecodeWfOpcode10Behavior0080::instruction _x0) {
  return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
}

unsigned int DecodeWfOpcode10Behavior0080::program_cycles(
    const std::shared_ptr<DecodeWfOpcode10Behavior0080::state> &s,
    const std::shared_ptr<List<DecodeWfOpcode10Behavior0080::instruction>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<DecodeWfOpcode10Behavior0080::instruction>::nil
                 _args) -> unsigned int { return 0; },
          [&](const typename List<DecodeWfOpcode10Behavior0080::instruction>::
                  cons _args) -> unsigned int {
            DecodeWfOpcode10Behavior0080::instruction i = _args._a0;
            std::shared_ptr<List<DecodeWfOpcode10Behavior0080::instruction>>
                rest = _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
