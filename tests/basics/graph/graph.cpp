#include <graph.h>

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// A graph abstraction parameterized by a container type G and
/// node type A. Provides operations for building and querying
/// the graph.
__attribute__((pure)) bool nat_eqb(const std::shared_ptr<Nat> &n,
                                   const std::shared_ptr<Nat> &m) {
  return std::visit(
      Overloaded{
          [&](const typename Nat::O &) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename Nat::O &) -> bool { return true; },
                    [](const typename Nat::S &) -> bool { return false; }},
                m->v());
          },
          [&](const typename Nat::S &_args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename Nat::O &) -> bool { return false; },
                    [&](const typename Nat::S &_args0) -> bool {
                      return nat_eqb(_args.d_a0, _args0.d_a0);
                    }},
                m->v());
          }},
      n->v());
}
