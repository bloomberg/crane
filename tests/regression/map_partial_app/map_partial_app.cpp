#include <map_partial_app.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
MapPartialApp::tree_sum(const MapPartialApp::tree &t) {
  if (std::holds_alternative<typename MapPartialApp::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename MapPartialApp::tree::Node>(t.v());
    return ((tree_sum(*(d_a0)) + d_a1) + tree_sum(*(d_a2)));
  }
}

/// wrap: takes tree and nat, builds Node with leaves.
__attribute__((pure)) MapPartialApp::tree
MapPartialApp::wrap(MapPartialApp::tree t, unsigned int v) {
  return tree::node(t, v, tree::leaf());
}

/// Sum a list of nats.
__attribute__((pure)) unsigned int
MapPartialApp::sum_list(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return (d_a0 + sum_list(*(d_a1)));
  }
}
