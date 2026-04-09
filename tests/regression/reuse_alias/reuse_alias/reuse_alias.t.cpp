#include <reuse_alias.h>

#include <cassert>
#include <iostream>

int main() {
  using RA = ReuseAlias;

  // reuse_fn_bug: transform_tree uses tree_sum(t) alongside pattern vars
  // The reuse optimization should NOT fire when scrutinee is used in body.
  // Expected: tree_sum(Node(left, 60, right)) where left=Node(Leaf,10,Leaf), right=Node(Leaf,30,Leaf)
  //         = 10 + 60 + 30 = 100
  auto r1 = RA::reuse_fn_bug;
  std::cout << "reuse_fn_bug = " << r1 << std::endl;
  assert(r1 == 100u);

  // nested_reuse_bug: nested match with scrutinee used in inner match
  // flag=0: Node(Leaf, 60, right) → sum = 0 + 60 + 30 = 90
  // flag=1: Node(left, 60, Leaf) → sum = 10 + 60 + 0 = 70
  // Total: 90 + 70 = 160
  auto r2 = RA::nested_reuse_bug;
  std::cout << "nested_reuse_bug = " << r2 << std::endl;
  assert(r2 == 160u);

  // recursive_reuse_bug: annotate_sum replaces each node's value with subtree sum
  // Input: Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf))
  // annotate_sum(Leaf) = Leaf
  // annotate_sum(Node(Leaf,10,Leaf)) = Node(Leaf, 10, Leaf) [sum of single-node tree = 10]
  // annotate_sum(Node(Leaf,30,Leaf)) = Node(Leaf, 30, Leaf) [sum = 30]
  // annotate_sum(root) = Node(annotate(left), 60, annotate(right))
  //                     = Node(Node(Leaf,10,Leaf), 60, Node(Leaf,30,Leaf))
  // tree_sum of result = 10 + 60 + 30 = 100
  auto r3 = RA::recursive_reuse_bug;
  std::cout << "recursive_reuse_bug = " << r3 << std::endl;
  assert(r3 == 100u);

  std::cout << "All reuse_alias tests passed!" << std::endl;
  return 0;
}
