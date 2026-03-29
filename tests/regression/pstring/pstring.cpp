#include <pstring.h>

#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::string
PString::nat_to_string(const std::shared_ptr<Nat> &n) {
  return std::visit(
      Overloaded{[](const typename Nat::O _args) -> std::string { return "O"; },
                 [](const typename Nat::S _args) -> std::string {
                   return "S"s + nat_to_string(_args.d_a0);
                 }},
      n->v());
}

__attribute__((pure)) int PString::nat_to_int(const std::shared_ptr<Nat> &n) {
  return std::visit(
      Overloaded{[](const typename Nat::O _args) -> int { return 0; },
                 [](const typename Nat::S _args) -> int {
                   return 1 + nat_to_int(_args.d_a0);
                 }},
      n->v());
}
