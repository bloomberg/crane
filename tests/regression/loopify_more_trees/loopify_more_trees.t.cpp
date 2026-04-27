// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_more_trees.h>

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

using Tree = LoopifyMoreTrees::tree;
using UIntList = List<unsigned int>;

int main() {
  auto leaf = Tree::leaf();
  auto t1 = Tree::node(leaf, 1u, leaf);
  auto t2 = Tree::node(leaf, 2u, leaf);
  auto t3 = Tree::node(t1, 3u, t2);

  // mirror
  auto mirrored = LoopifyMoreTrees::mirror(t3);
  ASSERT(LoopifyMoreTrees::count_nodes(mirrored) == LoopifyMoreTrees::count_nodes(t3));

  // same_shape
  ASSERT(LoopifyMoreTrees::same_shape(t1, t2) == true);
  ASSERT(LoopifyMoreTrees::same_shape(t1, t3) == false);
  ASSERT(LoopifyMoreTrees::same_shape(t3, t3) == true);

  // tree_to_list
  auto lst = LoopifyMoreTrees::tree_to_list(t3);
  // In-order: [1, 3, 2]

  // mirror_equal
  auto symmetric = Tree::node(t1, 5u, t1);
  ASSERT(LoopifyMoreTrees::mirror_equal(symmetric) == true);

  // count_nodes
  ASSERT(LoopifyMoreTrees::count_nodes(leaf) == 0u);
  ASSERT(LoopifyMoreTrees::count_nodes(t1) == 1u);
  ASSERT(LoopifyMoreTrees::count_nodes(t3) == 3u);

  // tree_max
  auto max_tree = LoopifyMoreTrees::tree_max(t1, t2);
  ASSERT(LoopifyMoreTrees::count_nodes(max_tree) == 1u);

  // sum_of_max_branches
  ASSERT(LoopifyMoreTrees::sum_of_max_branches(leaf) == 0u);
  ASSERT(LoopifyMoreTrees::sum_of_max_branches(t1) == 1u);
  ASSERT(LoopifyMoreTrees::sum_of_max_branches(t3) == 5u);  // 3 + max(1, 2)

  // insert_bst
  auto bst = LoopifyMoreTrees::insert_bst(5u, leaf);
  bst = LoopifyMoreTrees::insert_bst(3u, bst);
  bst = LoopifyMoreTrees::insert_bst(7u, bst);
  ASSERT(LoopifyMoreTrees::count_nodes(bst) == 3u);

  // build_bst
  auto nil = UIntList::nil();
  auto l3 = UIntList::cons(5u, UIntList::cons(3u, UIntList::cons(7u, nil)));
  auto bst2 = LoopifyMoreTrees::build_bst(l3);
  ASSERT(LoopifyMoreTrees::count_nodes(bst2) == 3u);

  // tree_levels
  auto levels = LoopifyMoreTrees::tree_levels(t3);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
