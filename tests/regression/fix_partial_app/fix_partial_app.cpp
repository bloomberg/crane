#include <fix_partial_app.h>

/// count_nodes: counts nodes in a tree. Will be partially applied.
unsigned int FixPartialApp::count_nodes(const FixPartialApp::tree &t,
                                        unsigned int base) {
  if (std::holds_alternative<typename FixPartialApp::tree::Leaf>(t.v())) {
    return base;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename FixPartialApp::tree::Node>(t.v());
    return count_nodes(*(d_a0), count_nodes(*(d_a2), (base + 1u)));
  }
}

unsigned int FixPartialApp::tree_sum(const FixPartialApp::tree &t) {
  if (std::holds_alternative<typename FixPartialApp::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename FixPartialApp::tree::Node>(t.v());
    return ((tree_sum(*(d_a0)) + d_a1) + tree_sum(*(d_a2)));
  }
}
