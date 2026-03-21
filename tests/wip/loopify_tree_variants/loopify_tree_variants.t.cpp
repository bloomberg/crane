// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_tree_variants.h>

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

int main() {
  // Ternary tree
  auto tleaf = LoopifyTreeVariants::ternary::ctor::TLeaf_();
  auto tnode = LoopifyTreeVariants::ternary::ctor::TNode_(tleaf, 5u, tleaf, tleaf);
  ASSERT(LoopifyTreeVariants::ternary_sum(tnode) == 5u);
  ASSERT(LoopifyTreeVariants::ternary_count(tnode) == 1u);

  // Quad tree
  auto qleaf1 = LoopifyTreeVariants::quadtree::ctor::QLeaf_(1u);
  auto qleaf2 = LoopifyTreeVariants::quadtree::ctor::QLeaf_(2u);
  auto qleaf3 = LoopifyTreeVariants::quadtree::ctor::QLeaf_(3u);
  auto qleaf4 = LoopifyTreeVariants::quadtree::ctor::QLeaf_(4u);
  auto quad = LoopifyTreeVariants::quadtree::ctor::Quad_(qleaf1, qleaf2, qleaf3, qleaf4);
  ASSERT(LoopifyTreeVariants::quad_sum(quad) == 10u);

  // Leaf tree
  auto lleaf1 = LoopifyTreeVariants::leaf_tree::ctor::LLeaf_(10u);
  auto lleaf2 = LoopifyTreeVariants::leaf_tree::ctor::LLeaf_(20u);
  auto ltree = LoopifyTreeVariants::leaf_tree::ctor::LNode_(lleaf1, lleaf2);
  ASSERT(LoopifyTreeVariants::leaf_tree_sum(ltree) == 30u);
  ASSERT(LoopifyTreeVariants::leaf_tree_max(ltree) == 20u);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
