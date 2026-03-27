// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_tree_paths.h>
#include <vector>

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

// Helper: convert List<T> to std::vector<T>
template <typename T>
std::vector<T> to_vec(const std::shared_ptr<List<T>> &l) {
  std::vector<T> result;
  const List<T> *cur = l.get();
  while (cur) {
    auto &v = cur->v();
    if (std::holds_alternative<typename List<T>::Cons>(v)) {
      auto &cons = std::get<typename List<T>::Cons>(v);
      result.push_back(cons.d_a0);
      cur = cons.d_a1.get();
    } else {
      break;
    }
  }
  return result;
}

// Helper: convert List<List<unsigned int>> to vector<vector<unsigned int>>
std::vector<std::vector<unsigned int>>
to_vecs(const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  std::vector<std::vector<unsigned int>> result;
  auto outer = to_vec(ll);
  for (auto &inner : outer) {
    result.push_back(to_vec(inner));
  }
  return result;
}

using Tree = LoopifyTreePaths::tree;
using BTree = LoopifyTreePaths::bool_tree;

int main() {
  // paths
  auto leaf = Tree::leaf();
  auto paths_leaf = leaf->paths();
  {
    auto vv = to_vecs(paths_leaf);
    // Leaf should give one empty path: [[]]
    ASSERT(vv.size() == 1u);
    ASSERT(vv[0].empty());
  }

  auto tree1 = Tree::node(leaf, 1u, leaf);
  {
    auto vv = to_vecs(tree1->paths());
    // Node(Leaf, 1, Leaf) -> [[1], [1]]
    ASSERT(vv.size() == 2u);
    ASSERT((vv[0] == std::vector<unsigned int>{1u}));
    ASSERT((vv[1] == std::vector<unsigned int>{1u}));
  }

  auto left = Tree::node(leaf, 2u, leaf);
  auto right = Tree::node(leaf, 3u, leaf);
  auto tree2 = Tree::node(left, 1u, right);
  {
    auto vv = to_vecs(tree2->paths());
    ASSERT(vv.size() == 4u);
    ASSERT((vv[0] == std::vector<unsigned int>{1u, 2u}));
    ASSERT((vv[1] == std::vector<unsigned int>{1u, 2u}));
    ASSERT((vv[2] == std::vector<unsigned int>{1u, 3u}));
    ASSERT((vv[3] == std::vector<unsigned int>{1u, 3u}));
  }

  // or_search
  auto is_even = [](unsigned int x) { return x % 2 == 0; };

  auto leaf_odd = BTree::bleaf(3u);
  auto leaf_even = BTree::bleaf(4u);

  ASSERT(leaf_odd->or_search(is_even) == false);
  ASSERT(leaf_even->or_search(is_even) == true);

  auto btree = BTree::bnode(leaf_odd, leaf_even);
  ASSERT(btree->or_search(is_even) == true);

  auto all_odd = BTree::bnode(leaf_odd, leaf_odd);
  ASSERT(all_odd->or_search(is_even) == false);

  // and_search
  auto is_positive = [](unsigned int x) { return x > 0u; };

  auto bleaf1 = BTree::bleaf(1u);
  auto bleaf2 = BTree::bleaf(2u);
  auto bleaf0 = BTree::bleaf(0u);

  ASSERT(bleaf1->and_search(is_positive) == true);
  ASSERT(bleaf0->and_search(is_positive) == false);

  auto all_pos = BTree::bnode(bleaf1, bleaf2);
  ASSERT(all_pos->and_search(is_positive) == true);

  auto has_zero = BTree::bnode(bleaf1, bleaf0);
  ASSERT(has_zero->and_search(is_positive) == false);

  // count_paths_sum
  ASSERT(leaf->count_paths_sum(0u) == 1u);
  ASSERT(leaf->count_paths_sum(5u) == 0u);

  auto tree3 = Tree::node(leaf, 5u, leaf);
  ASSERT(tree3->count_paths_sum(5u) == 2u);

  auto left1 = Tree::node(leaf, 2u, leaf);
  auto right1 = Tree::node(leaf, 3u, leaf);
  auto tree4 = Tree::node(left1, 1u, right1);
  ASSERT(tree4->count_paths_sum(3u) == 2u);
  ASSERT(tree4->count_paths_sum(4u) == 2u);

  // max_path_sum
  ASSERT(leaf->max_path_sum() == 0u);

  auto tree5 = Tree::node(leaf, 5u, leaf);
  ASSERT(tree5->max_path_sum() == 5u);

  auto left2 = Tree::node(leaf, 2u, leaf);
  auto right2 = Tree::node(leaf, 8u, leaf);
  auto tree6 = Tree::node(left2, 3u, right2);
  ASSERT(tree6->max_path_sum() == 11u);  // 3 + 8

  // flatten_paths
  {
    auto v = to_vec(leaf->flatten_paths());
    ASSERT(v.empty());
  }

  auto tree7 = Tree::node(leaf, 5u, leaf);
  {
    auto v = to_vec(tree7->flatten_paths());
    ASSERT((v == std::vector<unsigned int>{5u}));
  }

  auto left3 = Tree::node(leaf, 2u, leaf);
  auto right3 = Tree::node(leaf, 3u, leaf);
  auto tree8 = Tree::node(left3, 1u, right3);
  {
    auto v = to_vec(tree8->flatten_paths());
    ASSERT((v == std::vector<unsigned int>{1u, 2u, 3u}));
  }

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
