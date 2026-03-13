#include <drop_head_default.h>

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
DropHeadDefault::head_after_drop(const std::shared_ptr<List<unsigned int>> &rom,
                                 const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args) -> unsigned int {
            return 0u;
          },
          [](const typename List<unsigned int>::Cons _args) -> unsigned int {
            unsigned int b1 = _args.d_a0;
            return std::move(b1);
          }},
      drop<unsigned int>(addr, rom)->v());
}
