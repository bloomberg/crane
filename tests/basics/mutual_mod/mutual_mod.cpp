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
            std::shared_ptr<EvenOdd::odd_list> o = _args.d_a1;
            return (odd_length(std::move(o)) + 1);
          }},
      e->v());
}

__attribute__((pure)) unsigned int
EvenOdd::odd_length(const std::shared_ptr<EvenOdd::odd_list> &o) {
  return std::visit(
      Overloaded{
          [](const typename EvenOdd::odd_list::OCons _args) -> unsigned int {
            std::shared_ptr<EvenOdd::even_list> e = _args.d_a1;
            return (even_length(std::move(e)) + 1);
          }},
      o->v());
}
