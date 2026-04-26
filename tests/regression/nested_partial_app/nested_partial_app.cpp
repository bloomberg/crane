#include <nested_partial_app.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
NestedPartialApp::tree_sum(const NestedPartialApp::tree &t) {
  if (std::holds_alternative<typename NestedPartialApp::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename NestedPartialApp::tree::Node>(t.v());
    return ((tree_sum(*(d_a0)) + d_a1) + tree_sum(*(d_a2)));
  }
}

/// 3-argument function: builds Node(t1, n, t2).
__attribute__((pure)) NestedPartialApp::tree
NestedPartialApp::build_node(NestedPartialApp::tree t1, unsigned int n,
                             NestedPartialApp::tree t2) {
  return tree::node(t1, n, t2);
}

/// Variation: 4-argument function, triple nesting.
__attribute__((pure)) unsigned int
NestedPartialApp::quad_fn(const NestedPartialApp::tree &a,
                          const unsigned int &b, const unsigned int &c,
                          const NestedPartialApp::tree &d) {
  return (((tree_sum(a) + b) + c) + tree_sum(d));
}
