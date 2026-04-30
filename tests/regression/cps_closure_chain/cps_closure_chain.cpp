#include <cps_closure_chain.h>

unsigned int CpsClosureChain::tree_sum(const CpsClosureChain::tree &t) {
  return tree_sum_cps(t, [](unsigned int x) { return x; });
}

/// Build a deep tree to stress the closure chain.
CpsClosureChain::tree CpsClosureChain::build_left(unsigned int n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    unsigned int n_ = n - 1;
    return tree::node(build_left(n_), n, tree::leaf());
  }
}

CpsClosureChain::tree CpsClosureChain::build_right(unsigned int n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    unsigned int n_ = n - 1;
    return tree::node(tree::leaf(), n, build_right(n_));
  }
}

CpsClosureChain::tree CpsClosureChain::build_balanced(unsigned int n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    unsigned int n_ = n - 1;
    return tree::node(build_balanced(n_), n, build_balanced(n_));
  }
}
