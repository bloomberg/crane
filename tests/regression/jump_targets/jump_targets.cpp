#include <jump_targets.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int>
JumpTargets::jump_target_collection(
    const std::shared_ptr<JumpTargets::instr_collection> &i) {
  return std::visit(
      Overloaded{
          [](const typename JumpTargets::instr_collection::JUN_coll _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args.d_a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename JumpTargets::instr_collection::JMS_coll _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args.d_a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename JumpTargets::instr_collection::NOP_coll _args)
              -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}

std::shared_ptr<List<unsigned int>> JumpTargets::collect_targets(
    const std::shared_ptr<List<std::shared_ptr<JumpTargets::instr_collection>>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<
              std::shared_ptr<JumpTargets::instr_collection>>::Nil _args)
              -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::ctor::Nil_();
          },
          [](const typename List<
              std::shared_ptr<JumpTargets::instr_collection>>::Cons _args)
              -> std::shared_ptr<List<unsigned int>> {
            std::shared_ptr<JumpTargets::instr_collection> i = _args.d_a0;
            std::shared_ptr<
                List<std::shared_ptr<JumpTargets::instr_collection>>>
                rest = _args.d_a1;
            if (jump_target_collection(i).has_value()) {
              unsigned int a = *jump_target_collection(i);
              return List<unsigned int>::ctor::Cons_(
                  std::move(a), collect_targets(std::move(rest)));
            } else {
              return collect_targets(std::move(rest));
            }
          }},
      prog->v());
}

__attribute__((pure)) bool
JumpTargets::addr_in_region(const unsigned int addr,
                            const std::shared_ptr<JumpTargets::layout> &l) {
  return (l->base_ <= addr && addr < (l->base_ + l->code_));
}

__attribute__((pure)) std::optional<unsigned int>
JumpTargets::jump_target_region(
    const std::shared_ptr<JumpTargets::instr_region> &i) {
  return std::visit(
      Overloaded{[](const typename JumpTargets::instr_region::JUN_reg _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args.d_a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargets::instr_region::JMS_reg _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args.d_a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargets::instr_region::NOP_reg _args)
                     -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}

__attribute__((pure)) bool
JumpTargets::in_layout(const std::shared_ptr<JumpTargets::layout> &l,
                       const std::shared_ptr<JumpTargets::instr_region> &i) {
  if (jump_target_region(i).has_value()) {
    unsigned int a = *jump_target_region(i);
    return addr_in_region(a, l);
  } else {
    return true;
  }
}

__attribute__((pure)) std::optional<unsigned int>
JumpTargets::jump_target_jms(const std::shared_ptr<JumpTargets::instr_jms> &i) {
  return std::visit(
      Overloaded{[](const typename JumpTargets::instr_jms::JUN_jms _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args.d_a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargets::instr_jms::JMS_jms _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args.d_a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargets::instr_jms::NOP_jms _args)
                     -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}

__attribute__((pure)) unsigned int
JumpTargets::option_nat_or_zero(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int n = *o;
    return n;
  } else {
    return 0u;
  }
}

__attribute__((pure)) std::optional<unsigned int>
JumpTargets::jump_target_jun(const std::shared_ptr<JumpTargets::instr_jun> &i) {
  return std::visit(
      Overloaded{[](const typename JumpTargets::instr_jun::JUN_jun _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args.d_a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargets::instr_jun::JMS_jun _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args.d_a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargets::instr_jun::NOP_jun _args)
                     -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}

__attribute__((pure)) unsigned int
JumpTargets::target_default(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int a = *o;
    return a;
  } else {
    return 0u;
  }
}
