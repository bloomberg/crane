#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <pop_stack_empty_is_none.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> PopStackEmptyIsNone::stack(
    const std::shared_ptr<PopStackEmptyIsNone::state> &s) {
  return s->stack;
}

std::pair<std::optional<unsigned int>,
          std::shared_ptr<PopStackEmptyIsNone::state>>
PopStackEmptyIsNone::pop_stack(std::shared_ptr<PopStackEmptyIsNone::state> s) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::nil _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<PopStackEmptyIsNone::state>> {
                   return std::make_pair(std::nullopt, std::move(s));
                 },
                 [](const typename List<unsigned int>::cons _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<PopStackEmptyIsNone::state>> {
                   unsigned int x = _args._a0;
                   std::shared_ptr<List<unsigned int>> xs = _args._a1;
                   return std::make_pair(
                       std::make_optional<unsigned int>(std::move(x)),
                       std::make_shared<PopStackEmptyIsNone::state>(
                           state{std::move(xs)}));
                 }},
      s->stack->v());
}

bool PopStackEmptyIsNone::is_none(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int _x = *o;
    return false;
  } else {
    return true;
  }
}
