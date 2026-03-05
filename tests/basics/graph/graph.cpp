#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <graph.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

bool nat_eqb(const std::shared_ptr<Nat> &n, const std::shared_ptr<Nat> &m) {
  return std::visit(
      Overloaded{
          [&](const typename Nat::O _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename Nat::O _args) -> bool { return true; },
                    [](const typename Nat::S _args) -> bool { return false; }},
                m->v());
          },
          [&](const typename Nat::S _args) -> bool {
            std::shared_ptr<Nat> n_ = _args._a0;
            return std::visit(
                Overloaded{
                    [](const typename Nat::O _args) -> bool { return false; },
                    [&](const typename Nat::S _args) -> bool {
                      std::shared_ptr<Nat> m_ = _args._a0;
                      return nat_eqb(std::move(n_), std::move(m_));
                    }},
                m->v());
          }},
      n->v());
}
