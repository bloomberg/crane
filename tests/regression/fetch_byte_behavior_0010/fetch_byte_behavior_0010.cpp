#include <algorithm>
#include <any>
#include <cassert>
#include <fetch_byte_behavior_0010.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int FetchByteBehavior0010::acc(
    const std::shared_ptr<FetchByteBehavior0010::state> &s) {
  return s->acc;
}

unsigned int FetchByteBehavior0010::cycles(
    const std::shared_ptr<FetchByteBehavior0010::state> &_x,
    const FetchByteBehavior0010::instruction _x0) {
  return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
}

unsigned int FetchByteBehavior0010::program_cycles(
    const std::shared_ptr<FetchByteBehavior0010::state> &s,
    const std::shared_ptr<List<FetchByteBehavior0010::instruction>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<FetchByteBehavior0010::instruction>::nil _args)
              -> unsigned int { return 0; },
          [&](const typename List<FetchByteBehavior0010::instruction>::cons
                  _args) -> unsigned int {
            FetchByteBehavior0010::instruction i = _args._a0;
            std::shared_ptr<List<FetchByteBehavior0010::instruction>> rest =
                _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
