#include <functional>
#include <iostream>
#include <memory>
#include <nat.h>
#include <string>
#include <variant>

std::shared_ptr<Nat::nat> Nat::add(const std::shared_ptr<Nat::nat> &m,
                                   const std::shared_ptr<Nat::nat> &n) {
  return std::visit(
      Overloaded{
          [&](const typename Nat::nat::O _args) -> std::shared_ptr<Nat::nat> {
            return n;
          },
          [&](const typename Nat::nat::S _args) -> std::shared_ptr<Nat::nat> {
            std::shared_ptr<Nat::nat> x = _args._a0;
            return nat::ctor::S_(x->add(n));
          }},
      m->v());
}

int Nat::nat_to_int(const std::shared_ptr<Nat::nat> &n) {
  return std::visit(
      Overloaded{[&](const typename Nat::nat::O _args) -> int { return 0; },
                 [&](const typename Nat::nat::S _args) -> int {
                   std::shared_ptr<Nat::nat> n_ = _args._a0;
                   return 1 + n_->nat_to_int();
                 }},
      n->v());
}
