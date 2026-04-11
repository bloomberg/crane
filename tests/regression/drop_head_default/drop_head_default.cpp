#include <drop_head_default.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
DropHeadDefault::head_after_drop(const std::shared_ptr<List<unsigned int>> &rom,
                                 const unsigned int addr) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::Nil) -> unsigned int {
                   return 0u;
                 },
                 [](const typename List<unsigned int>::Cons _args)
                     -> unsigned int { return _args.d_a0; }},
      drop<unsigned int>(addr, rom)->v());
}
