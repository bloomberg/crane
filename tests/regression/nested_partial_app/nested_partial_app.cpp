#include <nested_partial_app.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
NestedPartialApp::tree_sum(const std::shared_ptr<NestedPartialApp::tree> &t) {
  if (std::holds_alternative<typename NestedPartialApp::tree::Leaf>(t->v())) {
    return 0u;
  } else {
    const auto &_m =
        *std::get_if<typename NestedPartialApp::tree::Node>(&t->v());
    return ((tree_sum(_m.d_a0) + _m.d_a1) + tree_sum(_m.d_a2));
  }
}

/// 3-argument function: builds Node(t1, n, t2).
std::shared_ptr<NestedPartialApp::tree>
NestedPartialApp::build_node(std::shared_ptr<NestedPartialApp::tree> t1,
                             const unsigned int n,
                             std::shared_ptr<NestedPartialApp::tree> t2) {
  return tree::node(t1, n, t2);
}

/// Variation: 4-argument function, triple nesting.
__attribute__((pure)) unsigned int
NestedPartialApp::quad_fn(const std::shared_ptr<NestedPartialApp::tree> &a,
                          const unsigned int b, const unsigned int c,
                          const std::shared_ptr<NestedPartialApp::tree> &d) {
  return (((tree_sum(a) + b) + c) + tree_sum(d));
}
