// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_trees.h>

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
  using Tree = LoopifyTrees::tree<unsigned int>;

  auto leaf = Tree::ctor::Leaf_();
  auto t1 = Tree::ctor::Node_(leaf, 5u, leaf);
  auto t2 = Tree::ctor::Node_(leaf, 3u, leaf);
  auto tree_val = Tree::ctor::Node_(t1, 2u, t2);

  // Test tree functions (methods on tree)
  ASSERT(LoopifyTrees::tree_sum(tree_val) == 10u);
  ASSERT(tree_val->tree_height() == 2u);
  ASSERT(tree_val->tree_size() == 3u);
  ASSERT(LoopifyTrees::leftmost(0u, tree_val) == 5u);
  ASSERT(LoopifyTrees::rightmost(0u, tree_val) == 3u);
  ASSERT(tree_val->count_leaves() == 4u);
  ASSERT(LoopifyTrees::leaf_sum(tree_val) == 8u);
  ASSERT(LoopifyTrees::sum_of_max_branches(tree_val) > 0u);

  // Test mirror
  auto mirrored = tree_val->mirror();
  ASSERT(mirrored != nullptr);

  // Test same_shape
  ASSERT(tree_val->same_shape(tree_val));

  // Test insert_bst
  auto bst = LoopifyTrees::insert_bst(4u, tree_val);
  ASSERT(bst != nullptr);

  // Test rose trees
  using RoseList = ::List<std::shared_ptr<LoopifyTrees::rose>>;
  auto rose_leaf1 =
      LoopifyTrees::rose::ctor::RNode_(5u, RoseList::ctor::Nil_());
  auto rose_leaf2 =
      LoopifyTrees::rose::ctor::RNode_(3u, RoseList::ctor::Nil_());
  auto rose_children = RoseList::ctor::Cons_(
      rose_leaf1, RoseList::ctor::Cons_(rose_leaf2, RoseList::ctor::Nil_()));
  auto rose_tree = LoopifyTrees::rose::ctor::RNode_(10u, rose_children);

  ASSERT(rose_tree->rose_sum() == 18u); // 10 + 5 + 3

  auto rose_doubled =
      rose_tree->rose_map([](unsigned int x) { return x * 2; });
  ASSERT(rose_doubled != nullptr);

  auto rose_flat = rose_tree->rose_flatten();
  ASSERT(rose_flat != nullptr);

  ASSERT(rose_tree->rose_depth() == 2u);

  // Test tree_max
  auto max_tree = LoopifyTrees::tree_max(t1, t2);
  ASSERT(max_tree != nullptr);

  // Test tree_levels
  auto levels = LoopifyTrees::tree_levels(tree_val);
  ASSERT(levels != nullptr);

  std::cout << "All unique tree tests passed!\n";
  return testStatus;
}
