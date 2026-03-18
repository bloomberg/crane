#include <mutual_mod.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
EvenOdd::even_length(const std::shared_ptr<EvenOdd::even_list> &e) {
  return std::visit(
      Overloaded{
          [](const typename EvenOdd::even_list::ENil _args) -> unsigned int {
            return 0u;
          },
          [](const typename EvenOdd::even_list::ECons _args) -> unsigned int {
            return (odd_length(_args.d_a1) + 1);
          }},
      e->v());
}

__attribute__((pure)) unsigned int
EvenOdd::odd_length(const std::shared_ptr<EvenOdd::odd_list> &o) {
  return std::visit(
      Overloaded{[](const typename EvenOdd::odd_list::OCons _args)
                     -> unsigned int { return (even_length(_args.d_a1) + 1); }},
      o->v());
}
