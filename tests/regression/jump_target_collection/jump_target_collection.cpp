#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <jump_target_collection.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int> JumpTargetCollection::jump_target(
    const std::shared_ptr<JumpTargetCollection::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename JumpTargetCollection::instruction::JUN _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargetCollection::instruction::JMS _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargetCollection::instruction::NOP _args)
                     -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}

std::shared_ptr<List<unsigned int>> JumpTargetCollection::collect_targets(
    const std::shared_ptr<
        List<std::shared_ptr<JumpTargetCollection::instruction>>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<JumpTargetCollection::instruction>>::nil _args)
              -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::ctor::nil_();
          },
          [](const typename List<
              std::shared_ptr<JumpTargetCollection::instruction>>::cons _args)
              -> std::shared_ptr<List<unsigned int>> {
            std::shared_ptr<JumpTargetCollection::instruction> i = _args._a0;
            std::shared_ptr<
                List<std::shared_ptr<JumpTargetCollection::instruction>>>
                rest = _args._a1;
            if (jump_target(i).has_value()) {
              unsigned int a = *jump_target(i);
              return List<unsigned int>::ctor::cons_(
                  std::move(a), collect_targets(std::move(rest)));
            } else {
              return collect_targets(std::move(rest));
            }
          }},
      prog->v());
}
