#include <shared_uptr_escape.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// identity: takes a tree and returns it unchanged.
/// The tree enters as owned and leaves as owned.
std::shared_ptr<SharedUptrEscape::tree>
SharedUptrEscape::identity(std::shared_ptr<SharedUptrEscape::tree> t) {
  return t;
}

/// BUG: Build a tree, then conditionally either return it once
/// (unique_ptr sufficient) or duplicate it (needs shared_ptr).
/// If escape analysis optimistically picks unique_ptr based on
/// one branch, the other branch's sharing crashes.
__attribute__((pure)) unsigned int
SharedUptrEscape::conditional_share(const unsigned int flag) {
  std::shared_ptr<SharedUptrEscape::tree> t =
      tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                 tree::node(tree::leaf(), 30u, tree::leaf()));
  if (flag <= 0) {
    return identity(std::move(t))->tree_sum();
  } else {
    unsigned int _x = flag - 1;
    std::pair<std::shared_ptr<SharedUptrEscape::tree>,
              std::shared_ptr<SharedUptrEscape::tree>>
        p = std::move(t)->dup();
    return (p.first->tree_sum() + p.second->tree_sum());
  }
}

std::shared_ptr<SharedUptrEscape::wrapper>
SharedUptrEscape::wrap_tree(std::shared_ptr<SharedUptrEscape::tree> t) {
  return wrapper::wrap(t);
}
