#include "map_partial_app.h"

uint64_t MapPartialApp::tree_sum(const MapPartialApp::tree &t) {
  if (std::holds_alternative<typename MapPartialApp::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename MapPartialApp::tree::Node>(t.v());
    return ((tree_sum(*a0) + a1) + tree_sum(*a2));
  }
}

/// wrap: takes tree and nat, builds Node with leaves.
MapPartialApp::tree MapPartialApp::wrap(MapPartialApp::tree t, uint64_t v) {
  return tree::node(std::move(t), v, tree::leaf());
}

/// Sum a list of nats.
uint64_t MapPartialApp::sum_list(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return (a0 + sum_list(*a1));
  }
}
