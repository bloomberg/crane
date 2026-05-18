#include "cps_closure_chain.h"

uint64_t CpsClosureChain::tree_sum(const CpsClosureChain::tree &t) {
  return tree_sum_cps(t, [](uint64_t x) { return x; });
}

/// Build a deep tree to stress the closure chain.
CpsClosureChain::tree CpsClosureChain::build_left(uint64_t n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    uint64_t n_ = n - 1;
    return tree::node(build_left(n_), n, tree::leaf());
  }
}

CpsClosureChain::tree CpsClosureChain::build_right(uint64_t n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    uint64_t n_ = n - 1;
    return tree::node(tree::leaf(), n, build_right(n_));
  }
}

CpsClosureChain::tree CpsClosureChain::build_balanced(uint64_t n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    uint64_t n_ = n - 1;
    return tree::node(build_balanced(n_), n, build_balanced(n_));
  }
}
