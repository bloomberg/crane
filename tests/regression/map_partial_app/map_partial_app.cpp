#include "map_partial_app.h"

unsigned int MapPartialApp::tree_sum(const MapPartialApp::tree &t) {
  if (std::holds_alternative<typename MapPartialApp::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename MapPartialApp::tree::Node>(t.v());
    return ((tree_sum(*a0) + a1) + tree_sum(*a2));
  }
}

/// wrap: takes tree and nat, builds Node with leaves.
MapPartialApp::tree MapPartialApp::wrap(MapPartialApp::tree t, unsigned int v) {
  return tree::node(std::move(t), v, tree::leaf());
}

/// Sum a list of nats.
unsigned int MapPartialApp::sum_list(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(l.v());
    return (a0 + sum_list(*a1));
  }
}
