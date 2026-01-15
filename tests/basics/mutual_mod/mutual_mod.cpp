#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <mutual_mod.h>
#include <optional>
#include <string>
#include <utility>
#include <variant>

unsigned int
EvenOdd::even_length(const std::shared_ptr<EvenOdd::even_list> &e) {
  return std::visit(
      Overloaded{
          [&](const typename EvenOdd::even_list::ENil _args) -> unsigned int {
            return 0;
          },
          [&](const typename EvenOdd::even_list::ECons _args) -> unsigned int {
            std::shared_ptr<EvenOdd::odd_list> o = _args._a1;
            return (odd_length(o) + 1);
          }},
      e->v());
}
unsigned int EvenOdd::odd_length(const std::shared_ptr<EvenOdd::odd_list> &o) {
  return std::visit(
      Overloaded{
          [&](const typename EvenOdd::odd_list::OCons _args) -> unsigned int {
            std::shared_ptr<EvenOdd::even_list> e = _args._a1;
            return (even_length(e) + 1);
          }},
      o->v());
}
