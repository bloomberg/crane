#include <cps_closure_chain.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
CpsClosureChain::tree_sum(const std::shared_ptr<CpsClosureChain::tree> &t) {
  return tree_sum_cps(t, [](const unsigned int x) { return x; });
}

/// Build a deep tree to stress the closure chain.
std::shared_ptr<CpsClosureChain::tree>
CpsClosureChain::build_left(const unsigned int n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    unsigned int n_ = n - 1;
    return tree::node(build_left(n_), n, tree::leaf());
  }
}

std::shared_ptr<CpsClosureChain::tree>
CpsClosureChain::build_right(const unsigned int n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    unsigned int n_ = n - 1;
    return tree::node(tree::leaf(), n, build_right(n_));
  }
}

std::shared_ptr<CpsClosureChain::tree>
CpsClosureChain::build_balanced(const unsigned int n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    unsigned int n_ = n - 1;
    return tree::node(build_balanced(n_), n, build_balanced(n_));
  }
}
