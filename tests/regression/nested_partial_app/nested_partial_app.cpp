#include "nested_partial_app.h"

unsigned int NestedPartialApp::tree_sum(const NestedPartialApp::tree &t) {
  if (std::holds_alternative<typename NestedPartialApp::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename NestedPartialApp::tree::Node>(t.v());
    return ((tree_sum(*a0) + a1) + tree_sum(*a2));
  }
}

/// 3-argument function: builds Node(t1, n, t2).
NestedPartialApp::tree NestedPartialApp::build_node(NestedPartialApp::tree t1,
                                                    unsigned int n,
                                                    NestedPartialApp::tree t2) {
  return tree::node(std::move(t1), n, std::move(t2));
}

/// Variation: 4-argument function, triple nesting.
unsigned int NestedPartialApp::quad_fn(const NestedPartialApp::tree &a,
                                       unsigned int b, unsigned int c,
                                       const NestedPartialApp::tree &d) {
  return (((tree_sum(a) + b) + c) + tree_sum(d));
}
