#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <polymorphic_helper.h>
#include <stdexcept>
#include <string>
#include <utility>
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

std::shared_ptr<Nat::nat> foo(std::shared_ptr<Nat::nat> n, const bool b) {
  return add(_foo_aux(std::move(n), n), _foo_aux(b, n));
}
