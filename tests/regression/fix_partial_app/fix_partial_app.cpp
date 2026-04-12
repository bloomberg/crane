#include <fix_partial_app.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// count_nodes: counts nodes in a tree. Will be partially applied.
__attribute__((pure)) unsigned int
FixPartialApp::count_nodes(const std::shared_ptr<FixPartialApp::tree> &t,
                           const unsigned int base) {
  return std::visit(
      Overloaded{
          [&](const typename FixPartialApp::tree::Leaf &) -> unsigned int {
            return base;
          },
          [&](const typename FixPartialApp::tree::Node &_args) -> unsigned int {
            return count_nodes(_args.d_a0,
                               count_nodes(_args.d_a2, (base + 1u)));
          }},
      t->v());
}

__attribute__((pure)) unsigned int
FixPartialApp::tree_sum(const std::shared_ptr<FixPartialApp::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename FixPartialApp::tree::Leaf &) -> unsigned int {
            return 0u;
          },
          [](const typename FixPartialApp::tree::Node &_args) -> unsigned int {
            return ((tree_sum(_args.d_a0) + _args.d_a1) + tree_sum(_args.d_a2));
          }},
      t->v());
}
