#include <map_partial_app.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
MapPartialApp::tree_sum(const std::shared_ptr<MapPartialApp::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename MapPartialApp::tree::Leaf _args) -> unsigned int {
            return 0u;
          },
          [](const typename MapPartialApp::tree::Node _args) -> unsigned int {
            return ((tree_sum(_args.d_a0) + _args.d_a1) + tree_sum(_args.d_a2));
          }},
      t->v());
}

/// wrap: takes tree and nat, builds Node with leaves.
std::shared_ptr<MapPartialApp::tree>
MapPartialApp::wrap(std::shared_ptr<MapPartialApp::tree> t,
                    const unsigned int v) {
  return tree::node(t, v, tree::leaf());
}

/// Sum a list of nats.
__attribute__((pure)) unsigned int
MapPartialApp::sum_list(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args) -> unsigned int {
            return 0u;
          },
          [](const typename List<unsigned int>::Cons _args) -> unsigned int {
            return (_args.d_a0 + sum_list(_args.d_a1));
          }},
      l->v());
}
