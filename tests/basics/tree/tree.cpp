#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <tree.h>
#include <variant>

std::shared_ptr<Nat::nat> add(const std::shared_ptr<Nat::nat> &n,
                              const std::shared_ptr<Nat::nat> &m) {
  return std::visit(
      Overloaded{
          [&](const typename Nat::nat::O _args) -> std::shared_ptr<Nat::nat> {
            return m;
          },
          [&](const typename Nat::nat::S _args) -> std::shared_ptr<Nat::nat> {
            std::shared_ptr<Nat::nat> p = _args._a0;
            return Nat::nat::ctor::S_(add(p, m));
          }},
      n->v());
}

std::shared_ptr<Nat::nat> max(const std::shared_ptr<Nat::nat> &n,
                              const std::shared_ptr<Nat::nat> &m) {
  return std::visit(
      Overloaded{
          [&](const typename Nat::nat::O _args) -> std::shared_ptr<Nat::nat> {
            return m;
          },
          [&](const typename Nat::nat::S _args) -> std::shared_ptr<Nat::nat> {
            std::shared_ptr<Nat::nat> n_ = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Nat::nat::O _args)
                               -> std::shared_ptr<Nat::nat> { return n; },
                           [&](const typename Nat::nat::S _args)
                               -> std::shared_ptr<Nat::nat> {
                             std::shared_ptr<Nat::nat> m_ = _args._a0;
                             return Nat::nat::ctor::S_(max(n_, m_));
                           }},
                m->v());
          }},
      n->v());
}
