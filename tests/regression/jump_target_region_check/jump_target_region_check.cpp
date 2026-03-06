#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <jump_target_region_check.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int JumpTargetRegionCheck::base_(
    const std::shared_ptr<JumpTargetRegionCheck::layout> &l) {
  return l->base_;
}

unsigned int JumpTargetRegionCheck::code_(
    const std::shared_ptr<JumpTargetRegionCheck::layout> &l) {
  return l->code_;
}

bool JumpTargetRegionCheck::addr_in_region(
    const unsigned int addr,
    const std::shared_ptr<JumpTargetRegionCheck::layout> &l) {
  return ((l->base_ <= addr) && (addr < (l->base_ + l->code_)));
}

std::optional<unsigned int> JumpTargetRegionCheck::jump_target(
    const std::shared_ptr<JumpTargetRegionCheck::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename JumpTargetRegionCheck::instruction::JUN_ _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename JumpTargetRegionCheck::instruction::JMS_ _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename JumpTargetRegionCheck::instruction::NOP_ _args)
              -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}

bool JumpTargetRegionCheck::in_layout(
    const std::shared_ptr<JumpTargetRegionCheck::layout> &l,
    const std::shared_ptr<JumpTargetRegionCheck::instruction> &i) {
  if (jump_target(i).has_value()) {
    unsigned int a = *jump_target(i);
    return addr_in_region(a, l);
  } else {
    return true;
  }
}
