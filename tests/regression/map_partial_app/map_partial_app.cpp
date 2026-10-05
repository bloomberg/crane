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
MapPartialApp::tree MapPartialApp::wrap(const MapPartialApp::tree &t,
                                        uint64_t v) {
  return tree::node(t, v, tree::leaf());
}

/// Sum a list of nats.
uint64_t MapPartialApp::sum_list(const List<uint64_t> &l) {
  {
    const List<uint64_t> &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = std::move(_lc1_acc);
    const List<uint64_t> *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}
