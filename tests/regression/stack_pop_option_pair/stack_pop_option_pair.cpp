#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stack_pop_option_pair.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
StackPopOptionPair::stack(const std::shared_ptr<StackPopOptionPair::state> &s) {
  return s->stack;
}

unsigned int
StackPopOptionPair::acc(const std::shared_ptr<StackPopOptionPair::state> &s) {
  return s->acc;
}

std::pair<std::optional<unsigned int>,
          std::shared_ptr<StackPopOptionPair::state>>
StackPopOptionPair::pop_stack(std::shared_ptr<StackPopOptionPair::state> s) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::nil _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<StackPopOptionPair::state>> {
                   return std::make_pair(std::nullopt, std::move(s));
                 },
                 [&](const typename List<unsigned int>::cons _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<StackPopOptionPair::state>> {
                   unsigned int a = _args._a0;
                   std::shared_ptr<List<unsigned int>> rest = _args._a1;
                   return std::make_pair(
                       std::make_optional<unsigned int>(std::move(a)),
                       std::make_shared<StackPopOptionPair::state>(
                           state{std::move(rest), std::move(s)->acc}));
                 }},
      s->stack->v());
}
