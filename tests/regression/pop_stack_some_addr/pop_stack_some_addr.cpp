#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <pop_stack_some_addr.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
PopStackSomeAddr::stack(const std::shared_ptr<PopStackSomeAddr::state> &s) {
  return s->stack;
}

std::pair<std::optional<unsigned int>, std::shared_ptr<PopStackSomeAddr::state>>
PopStackSomeAddr::pop_stack(std::shared_ptr<PopStackSomeAddr::state> s) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::nil _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<PopStackSomeAddr::state>> {
                   return std::make_pair(std::nullopt, std::move(s));
                 },
                 [](const typename List<unsigned int>::cons _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<PopStackSomeAddr::state>> {
                   unsigned int x = _args._a0;
                   std::shared_ptr<List<unsigned int>> xs = _args._a1;
                   return std::make_pair(
                       std::make_optional<unsigned int>(std::move(x)),
                       std::make_shared<PopStackSomeAddr::state>(
                           state{std::move(xs)}));
                 }},
      s->stack->v());
}

unsigned int
PopStackSomeAddr::option_or_zero(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int n = *o;
    return n;
  } else {
    return 0;
  }
}
