#include "shared_uptr_escape.h"

/// BUG: Build a tree, then conditionally either return it once
/// (unique_ptr sufficient) or duplicate it (needs shared_ptr).
/// If escape analysis optimistically picks unique_ptr based on
/// one branch, the other branch's sharing crashes.
uint64_t SharedUptrEscape::conditional_share(uint64_t flag) {
  SharedUptrEscape::tree t = tree::node(
      tree::node(tree::leaf(), UINT64_C(10), tree::leaf()), UINT64_C(20),
      tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
  if (flag <= 0) {
    return std::move(t).identity().tree_sum();
  } else {
    uint64_t _x = flag - 1;
    std::pair<SharedUptrEscape::tree, SharedUptrEscape::tree> p =
        std::move(t).dup();
    return (p.first.tree_sum() + p.second.tree_sum());
  }
}

SharedUptrEscape::wrapper
SharedUptrEscape::wrap_tree(SharedUptrEscape::tree t) {
  return wrapper::wrap(std::move(t));
}
