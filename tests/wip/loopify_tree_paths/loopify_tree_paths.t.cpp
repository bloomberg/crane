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
  auto leaf = Tree::ctor::Leaf_();
  auto paths_leaf = LoopifyTreePaths::paths(leaf);
  {
    auto vv = to_vecs(paths_leaf);
    // Leaf should give one empty path: [[]]
    ASSERT(vv.size() == 1u);
    ASSERT(vv[0].empty());
  }

  auto tree1 = Tree::ctor::Node_(leaf, 1u, leaf);
  {
    auto vv = to_vecs(LoopifyTreePaths::paths(tree1));
    // Node(Leaf, 1, Leaf) -> [[1], [1]]
    ASSERT(vv.size() == 2u);
    ASSERT((vv[0] == std::vector<unsigned int>{1u}));
    ASSERT((vv[1] == std::vector<unsigned int>{1u}));
  }

  auto left = Tree::ctor::Node_(leaf, 2u, leaf);
  auto right = Tree::ctor::Node_(leaf, 3u, leaf);
  auto tree2 = Tree::ctor::Node_(left, 1u, right);
  {
    auto vv = to_vecs(LoopifyTreePaths::paths(tree2));
    ASSERT(vv.size() == 4u);
    ASSERT((vv[0] == std::vector<unsigned int>{1u, 2u}));
    ASSERT((vv[1] == std::vector<unsigned int>{1u, 3u}));
    ASSERT((vv[2] == std::vector<unsigned int>{1u, 2u}));
    ASSERT((vv[3] == std::vector<unsigned int>{1u, 3u}));
  }

  // or_search
  auto is_even = [](unsigned int x) { return x % 2 == 0; };

  auto leaf_odd = BTree::ctor::BLeaf_(3u);
  auto leaf_even = BTree::ctor::BLeaf_(4u);

  ASSERT(LoopifyTreePaths::or_search(is_even, leaf_odd) == false);
  ASSERT(LoopifyTreePaths::or_search(is_even, leaf_even) == true);

  auto btree = BTree::ctor::BNode_(leaf_odd, leaf_even);
  ASSERT(LoopifyTreePaths::or_search(is_even, btree) == true);

  auto all_odd = BTree::ctor::BNode_(leaf_odd, leaf_odd);
  ASSERT(LoopifyTreePaths::or_search(is_even, all_odd) == false);

  // and_search
  auto is_positive = [](unsigned int x) { return x > 0u; };

  auto bleaf1 = BTree::ctor::BLeaf_(1u);
  auto bleaf2 = BTree::ctor::BLeaf_(2u);
  auto bleaf0 = BTree::ctor::BLeaf_(0u);

  ASSERT(LoopifyTreePaths::and_search(is_positive, bleaf1) == true);
  ASSERT(LoopifyTreePaths::and_search(is_positive, bleaf0) == false);

  auto all_pos = BTree::ctor::BNode_(bleaf1, bleaf2);
  ASSERT(LoopifyTreePaths::and_search(is_positive, all_pos) == true);

  auto has_zero = BTree::ctor::BNode_(bleaf1, bleaf0);
  ASSERT(LoopifyTreePaths::and_search(is_positive, has_zero) == false);

  // count_paths_sum
  ASSERT(LoopifyTreePaths::count_paths_sum(0u, leaf) == 1u);
  ASSERT(LoopifyTreePaths::count_paths_sum(5u, leaf) == 0u);

  auto tree3 = Tree::ctor::Node_(leaf, 5u, leaf);
  ASSERT(LoopifyTreePaths::count_paths_sum(5u, tree3) == 2u);

  auto left1 = Tree::ctor::Node_(leaf, 2u, leaf);
  auto right1 = Tree::ctor::Node_(leaf, 3u, leaf);
  auto tree4 = Tree::ctor::Node_(left1, 1u, right1);
  ASSERT(LoopifyTreePaths::count_paths_sum(3u, tree4) == 2u);
  ASSERT(LoopifyTreePaths::count_paths_sum(4u, tree4) == 2u);

  // max_path_sum
  ASSERT(LoopifyTreePaths::max_path_sum(leaf) == 0u);

  auto tree5 = Tree::ctor::Node_(leaf, 5u, leaf);
  ASSERT(LoopifyTreePaths::max_path_sum(tree5) == 5u);

  auto left2 = Tree::ctor::Node_(leaf, 2u, leaf);
  auto right2 = Tree::ctor::Node_(leaf, 8u, leaf);
  auto tree6 = Tree::ctor::Node_(left2, 3u, right2);
  ASSERT(LoopifyTreePaths::max_path_sum(tree6) == 11u);  // 3 + 8

  // flatten_paths
  {
    auto v = to_vec(LoopifyTreePaths::flatten_paths(leaf));
    ASSERT(v.empty());
  }

  auto tree7 = Tree::ctor::Node_(leaf, 5u, leaf);
  {
    auto v = to_vec(LoopifyTreePaths::flatten_paths(tree7));
    ASSERT((v == std::vector<unsigned int>{5u}));
  }

  auto left3 = Tree::ctor::Node_(leaf, 2u, leaf);
  auto right3 = Tree::ctor::Node_(leaf, 3u, leaf);
  auto tree8 = Tree::ctor::Node_(left3, 1u, right3);
  {
    auto v = to_vec(LoopifyTreePaths::flatten_paths(tree8));
    ASSERT((v == std::vector<unsigned int>{1u, 2u, 3u}));
  }

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
