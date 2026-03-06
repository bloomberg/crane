#include <algorithm>
#include <any>
#include <cassert>
#include <drop_head_default.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
DropHeadDefault::head_after_drop(const std::shared_ptr<List<unsigned int>> &rom,
                                 const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args) -> unsigned int {
            return 0;
          },
          [](const typename List<unsigned int>::cons _args) -> unsigned int {
            unsigned int b1 = _args._a0;
            return std::move(b1);
          }},
      drop<unsigned int>(addr, rom)->v());
}
