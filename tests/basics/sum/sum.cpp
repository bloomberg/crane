#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <sum.h>
#include <variant>

unsigned int Sum::either_to_nat(
    const std::shared_ptr<Sum::either<unsigned int, unsigned int>> &e) {
  return std::visit(
      Overloaded{
          [](const typename Sum::either<unsigned int, unsigned int>::Left _args)
              -> unsigned int {
            unsigned int n = _args._a0;
            return std::move(n);
          },
          [](const typename Sum::either<unsigned int, unsigned int>::Right
                 _args) -> unsigned int {
            unsigned int m = _args._a0;
            return std::move(m);
          }},
      e->v());
}
