#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <tree.h>
#include <variant>

std::shared_ptr<Nat::nat> add(const std::shared_ptr<Nat::nat> &n,
                              std::shared_ptr<Nat::nat> m) {
  return std::visit(
      Overloaded{
          [&](const typename Nat::nat::O _args) -> std::shared_ptr<Nat::nat> {
            return std::move(m);
          },
          [&](const typename Nat::nat::S _args) -> std::shared_ptr<Nat::nat> {
            std::shared_ptr<Nat::nat> p = _args._a0;
            return Nat::nat::ctor::S_(add(std::move(p), std::move(m)));
          }},
      n->v());
}

std::shared_ptr<Nat::nat> max(std::shared_ptr<Nat::nat> n,
                              std::shared_ptr<Nat::nat> m) {
  return std::visit(
      Overloaded{
          [&](const typename Nat::nat::O _args) -> std::shared_ptr<Nat::nat> {
            return std::move(m);
          },
          [&](const typename Nat::nat::S _args) -> std::shared_ptr<Nat::nat> {
            std::shared_ptr<Nat::nat> n_ = _args._a0;
            return [&](void) {
              if (std::move(m).use_count() == 1 &&
                  std::move(m)->v().index() == 1) {
                auto &_rf = std::get<1>(std::move(m)->v_mut());
                std::shared_ptr<Nat::nat> m_ = std::move(_rf._a0);
                _rf._a0 = max(std::move(n_), std::move(m_));
                return std::move(m);
              } else {
                return std::visit(
                    Overloaded{[&](const typename Nat::nat::O _args)
                                   -> std::shared_ptr<Nat::nat> {
                                 return std::move(n);
                               },
                               [&](const typename Nat::nat::S _args)
                                   -> std::shared_ptr<Nat::nat> {
                                 std::shared_ptr<Nat::nat> m_ = _args._a0;
                                 return Nat::nat::ctor::S_(
                                     max(std::move(n_), std::move(m_)));
                               }},
                    std::move(m)->v());
              }
            }();
          }},
      n->v());
}
