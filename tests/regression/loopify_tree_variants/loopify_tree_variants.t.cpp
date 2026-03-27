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
  auto tleaf = LoopifyTreeVariants::ternary::tleaf();
  auto tnode = LoopifyTreeVariants::ternary::tnode(tleaf, 5u, tleaf, tleaf);
  ASSERT(tnode->ternary_sum() == 5u);
  ASSERT(tnode->ternary_count() == 1u);

  // Quad tree
  auto qleaf1 = LoopifyTreeVariants::quadtree::qleaf(1u);
  auto qleaf2 = LoopifyTreeVariants::quadtree::qleaf(2u);
  auto qleaf3 = LoopifyTreeVariants::quadtree::qleaf(3u);
  auto qleaf4 = LoopifyTreeVariants::quadtree::qleaf(4u);
  auto quad = LoopifyTreeVariants::quadtree::quad(qleaf1, qleaf2, qleaf3, qleaf4);
  ASSERT(quad->quad_sum() == 10u);

  // Leaf tree
  auto lleaf1 = LoopifyTreeVariants::leaf_tree::lleaf(10u);
  auto lleaf2 = LoopifyTreeVariants::leaf_tree::lleaf(20u);
  auto ltree = LoopifyTreeVariants::leaf_tree::lnode(lleaf1, lleaf2);
  ASSERT(ltree->leaf_tree_sum() == 30u);
  ASSERT(ltree->leaf_tree_max() == 20u);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
