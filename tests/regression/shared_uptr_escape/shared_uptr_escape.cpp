#include <shared_uptr_escape.h>

/// BUG: Build a tree, then conditionally either return it once
/// (unique_ptr sufficient) or duplicate it (needs shared_ptr).
/// If escape analysis optimistically picks unique_ptr based on
/// one branch, the other branch's sharing crashes.
unsigned int SharedUptrEscape::conditional_share(const unsigned int &flag) {
  SharedUptrEscape::tree t =
      tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                 tree::node(tree::leaf(), 30u, tree::leaf()));
  if (flag <= 0) {
    return std::move(t).identity().tree_sum();
  } else {
    unsigned int _x = flag - 1;
    std::pair<SharedUptrEscape::tree, SharedUptrEscape::tree> p =
        std::move(t).dup();
    return (p.first.tree_sum() + p.second.tree_sum());
  }
}

SharedUptrEscape::wrapper
SharedUptrEscape::wrap_tree(SharedUptrEscape::tree t) {
  return wrapper::wrap(std::move(t));
}
