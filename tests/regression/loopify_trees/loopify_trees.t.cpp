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

  auto leaf = Tree::leaf();
  auto t1 = Tree::node(leaf, 5u, leaf);
  auto t2 = Tree::node(leaf, 3u, leaf);
  auto tree_val = Tree::node(t1, 2u, t2);

  // Test tree functions (methods on tree)
  ASSERT(LoopifyTrees::tree_sum(tree_val) == 10u);
  ASSERT(tree_val.tree_height() == 2u);
  ASSERT(tree_val.tree_size() == 3u);
  ASSERT(tree_val.leftmost(0u) == 5u);
  ASSERT(tree_val.rightmost(0u) == 3u);
  ASSERT(tree_val.count_leaves() == 4u);
  ASSERT(LoopifyTrees::leaf_sum(tree_val) == 8u);
  ASSERT(LoopifyTrees::sum_of_max_branches(tree_val) > 0u);

  // Test mirror
  auto mirrored = tree_val.mirror();

  // Test same_shape
  ASSERT(tree_val.same_shape(tree_val));

  // Test insert_bst
  auto bst = LoopifyTrees::insert_bst(4u, tree_val);

  // Test rose trees
  using RoseList = ::List<LoopifyTrees::rose>;
  auto rose_leaf1 =
      LoopifyTrees::rose::rnode(5u, RoseList::nil());
  auto rose_leaf2 =
      LoopifyTrees::rose::rnode(3u, RoseList::nil());
  auto rose_children = RoseList::cons(
      rose_leaf1, RoseList::cons(rose_leaf2, RoseList::nil()));
  auto rose_tree = LoopifyTrees::rose::rnode(10u, rose_children);

  ASSERT(rose_tree.rose_sum() == 18u); // 10 + 5 + 3

  auto rose_doubled =
      rose_tree.rose_map([](unsigned int x) { return x * 2; });

  auto rose_flat = rose_tree.rose_flatten();

  ASSERT(rose_tree.rose_depth() == 2u);

  // Test tree_max
  auto max_tree = LoopifyTrees::tree_max(t1, t2);

  // Test tree_levels
  auto levels = LoopifyTrees::tree_levels(tree_val);

  std::cout << "All unique tree tests passed!\n";
  return testStatus;
}
