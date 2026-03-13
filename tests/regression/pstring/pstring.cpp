#include <pstring.h>

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

__attribute__((pure)) std::string
PString::nat_to_string(const std::shared_ptr<Nat> &n) {
  return std::visit(
      Overloaded{[](const typename Nat::O _args) -> std::string { return "O"; },
                 [](const typename Nat::S _args) -> std::string {
                   std::shared_ptr<Nat> n_ = _args.d_a0;
                   return "S"s + nat_to_string(std::move(n_));
                 }},
      n->v());
}

__attribute__((pure)) int PString::nat_to_int(const std::shared_ptr<Nat> &n) {
  return std::visit(
      Overloaded{[](const typename Nat::O _args) -> int { return 0; },
                 [](const typename Nat::S _args) -> int {
                   std::shared_ptr<Nat> n_ = _args.d_a0;
                   return 1 + nat_to_int(std::move(n_));
                 }},
      n->v());
}
