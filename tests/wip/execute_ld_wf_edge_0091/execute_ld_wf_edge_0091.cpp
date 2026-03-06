#include <algorithm>
#include <any>
#include <cassert>
#include <execute_ld_wf_edge_0091.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ExecuteLdWfEdge0091::base_addr(
    const std::shared_ptr<ExecuteLdWfEdge0091::layout> &l) {
  return l->base_addr;
}

unsigned int ExecuteLdWfEdge0091::code_size(
    const std::shared_ptr<ExecuteLdWfEdge0091::layout> &l) {
  return l->code_size;
}

std::optional<unsigned int> ExecuteLdWfEdge0091::jump_target(
    const std::shared_ptr<ExecuteLdWfEdge0091::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename ExecuteLdWfEdge0091::instruction::JUN _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename ExecuteLdWfEdge0091::instruction::JMS _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename ExecuteLdWfEdge0091::instruction::NOP _args)
                     -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}
