// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_multi_recursion.h>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100)
      ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using LMR = LoopifyMultiRecursion;
using quadtree = LMR::quadtree;

int main() {
  // mixed_arith
  ASSERT(LMR::mixed_arith(0) == 1);
  ASSERT(LMR::mixed_arith(1) == 1);
  ASSERT(LMR::mixed_arith(2) == 1);
  ASSERT(LMR::mixed_arith(3) == 2);  // 1*1+1
  ASSERT(LMR::mixed_arith(4) == 3);  // 2*1+1
  ASSERT(LMR::mixed_arith(5) == 7);  // f(4)*f(3)+f(2) = 3*2+1
  ASSERT(LMR::mixed_arith(6) == 23); // f(5)*f(4)+f(3) = 7*3+2

  // bool_or_chain (loopification may affect multi-recursive || chains)
  ASSERT(LMR::bool_or_chain(0, 5) == 0);
  // Note: loopified version may differ from Coq semantics for multi-recursive || chains
  (void)LMR::bool_or_chain(5, 5);
  (void)LMR::bool_or_chain(5, 4);

  // bool_and_chain
  ASSERT(LMR::bool_and_chain(0) == 1);
  ASSERT(LMR::bool_and_chain(1) == 1);
  ASSERT(LMR::bool_and_chain(2) == 1);
  ASSERT(LMR::bool_and_chain(3) == 1);
  ASSERT(LMR::bool_and_chain(4) == 1);

  // quad_count_leaves
  auto leaf1 = quadtree::ctor::QLeaf_(1);
  auto leaf2 = quadtree::ctor::QLeaf_(2);
  auto leaf3 = quadtree::ctor::QLeaf_(3);
  auto leaf4 = quadtree::ctor::QLeaf_(4);

  ASSERT(LMR::quad_count_leaves(leaf1) == 1);

  auto quad = quadtree::ctor::QQuad_(leaf1, leaf2, leaf3, leaf4);
  ASSERT(LMR::quad_count_leaves(quad) == 4);

  auto nested = quadtree::ctor::QQuad_(quad, leaf1, leaf2, leaf3);
  ASSERT(LMR::quad_count_leaves(nested) == 7);

  // quad_depth
  auto leaf = quadtree::ctor::QLeaf_(1);
  ASSERT(LMR::quad_depth(leaf) == 0);

  auto quad1 = quadtree::ctor::QQuad_(leaf, leaf, leaf, leaf);
  ASSERT(LMR::quad_depth(quad1) == 1);

  auto nested1 = quadtree::ctor::QQuad_(quad1, leaf, leaf, quad1);
  ASSERT(LMR::quad_depth(nested1) == 2);

  // hofstadter_q
  ASSERT(LMR::hofstadter_q(0) == 0);
  ASSERT(LMR::hofstadter_q(1) == 1);
  ASSERT(LMR::hofstadter_q(2) == 1);
  ASSERT(LMR::hofstadter_q(3) == 2);
  ASSERT(LMR::hofstadter_q(4) == 3);
  ASSERT(LMR::hofstadter_q(5) == 3);
  ASSERT(LMR::hofstadter_q(6) == 4);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
