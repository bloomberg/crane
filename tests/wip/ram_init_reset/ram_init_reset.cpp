#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_init_reset.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<RamInitReset::state>
RamInitReset::reset_state(std::shared_ptr<RamInitReset::state> s) {
  return std::make_shared<RamInitReset::state>(
      state{s->state_regs, 0u, false, 0u, List<unsigned int>::ctor::nil_(),
            s->state_ram, default_sel, s->state_rom});
}

std::pair<std::optional<unsigned int>, std::shared_ptr<RamInitReset::state>>
RamInitReset::pop_stack(std::shared_ptr<RamInitReset::state> s) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::nil _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<RamInitReset::state>> {
                   return std::make_pair(std::nullopt, std::move(s));
                 },
                 [&](const typename List<unsigned int>::cons _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<RamInitReset::state>> {
                   unsigned int x = _args._a0;
                   std::shared_ptr<List<unsigned int>> xs = _args._a1;
                   return std::make_pair(
                       std::make_optional<unsigned int>(std::move(x)),
                       std::make_shared<RamInitReset::state>(
                           state{s->state_regs, s->state_acc, s->state_carry,
                                 s->state_pc, std::move(xs), s->state_ram,
                                 s->state_sel, s->state_rom}));
                 }},
      s->state_stack->v());
}
