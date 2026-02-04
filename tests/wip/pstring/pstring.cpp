#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <pstring.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::string PString::nat_to_string(const std::shared_ptr<Nat::nat> &n) {
  return std::visit(
      Overloaded{
          [](const typename Nat::nat::O _args) -> std::string { return "O"; },
          [](const typename Nat::nat::S _args) -> std::string {
            std::shared_ptr<Nat::nat> n_ = _args._a0;
            return "S" + nat_to_string(n_);
          }},
      n->v());
}

int PString::nat_to_int(const std::shared_ptr<Nat::nat> &n) {
  return std::visit(
      Overloaded{[](const typename Nat::nat::O _args) -> int { return 0; },
                 [](const typename Nat::nat::S _args) -> int {
                   std::shared_ptr<Nat::nat> n_ = _args._a0;
                   return 1 + nat_to_int(n_);
                 }},
      n->v());
}
