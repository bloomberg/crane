#include <algorithm>
#include <any>
#include <cassert>
#include <decode_addr12_helper_edge_0027.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int DecodeAddr12HelperEdge0027::base_addr(
    const std::shared_ptr<DecodeAddr12HelperEdge0027::layout> &l) {
  return l->base_addr;
}

unsigned int DecodeAddr12HelperEdge0027::code_size(
    const std::shared_ptr<DecodeAddr12HelperEdge0027::layout> &l) {
  return l->code_size;
}

std::optional<unsigned int> DecodeAddr12HelperEdge0027::jump_target(
    const std::shared_ptr<DecodeAddr12HelperEdge0027::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename DecodeAddr12HelperEdge0027::instruction::JUN _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename DecodeAddr12HelperEdge0027::instruction::JMS _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename DecodeAddr12HelperEdge0027::instruction::NOP _args)
              -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}
