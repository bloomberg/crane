#include <map_partial_app.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
MapPartialApp::tree_sum(const std::shared_ptr<MapPartialApp::tree> &t) {
  if (std::holds_alternative<typename MapPartialApp::tree::Leaf>(t->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename MapPartialApp::tree::Node>(&t->v());
    return ((tree_sum(_m.d_a0) + _m.d_a1) + tree_sum(_m.d_a2));
  }
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
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&l->v());
    return (_m.d_a0 + sum_list(_m.d_a1));
  }
}
