#include <graph.h>

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

/// A graph abstraction parameterized by a container type G and
/// node type A. Provides operations for building and querying
/// the graph.
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
            std::shared_ptr<Nat> n_ = _args.d_a0;
            return std::visit(
                Overloaded{
                    [](const typename Nat::O _args) -> bool { return false; },
                    [&](const typename Nat::S _args) -> bool {
                      std::shared_ptr<Nat> m_ = _args.d_a0;
                      return nat_eqb(std::move(n_), std::move(m_));
                    }},
                m->v());
          }},
      n->v());
}
