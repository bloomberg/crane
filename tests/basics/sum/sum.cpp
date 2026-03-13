#include <sum.h>

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

__attribute__((pure)) unsigned int Sum::either_to_nat(
    const std::shared_ptr<Sum::either<unsigned int, unsigned int>> &e) {
  return std::visit(
      Overloaded{
          [](const typename Sum::either<unsigned int, unsigned int>::Left _args)
              -> unsigned int {
            unsigned int n = _args.d_a0;
            return std::move(n);
          },
          [](const typename Sum::either<unsigned int, unsigned int>::Right
                 _args) -> unsigned int {
            unsigned int m = _args.d_a0;
            return std::move(m);
          }},
      e->v());
}
