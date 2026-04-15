#include <fix_partial_app.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// count_nodes: counts nodes in a tree. Will be partially applied.
__attribute__((pure)) unsigned int
FixPartialApp::count_nodes(const std::shared_ptr<FixPartialApp::tree> &t,
                           const unsigned int base) {
  if (std::holds_alternative<typename FixPartialApp::tree::Leaf>(t->v())) {
    return base;
  } else {
    const auto &_m = *std::get_if<typename FixPartialApp::tree::Node>(&t->v());
    return count_nodes(_m.d_a0, count_nodes(_m.d_a2, (base + 1u)));
  }
}

__attribute__((pure)) unsigned int
FixPartialApp::tree_sum(const std::shared_ptr<FixPartialApp::tree> &t) {
  if (std::holds_alternative<typename FixPartialApp::tree::Leaf>(t->v())) {
    return 0u;
  } else {
    const auto &_m = *std::get_if<typename FixPartialApp::tree::Node>(&t->v());
    return ((tree_sum(_m.d_a0) + _m.d_a1) + tree_sum(_m.d_a2));
  }
}
