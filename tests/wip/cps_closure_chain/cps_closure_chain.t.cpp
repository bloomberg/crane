#include <cps_closure_chain.h>

#include <cassert>
#include <iostream>

int main() {
  using CCC = CpsClosureChain;

  // test_left: left-spine tree 5 nodes, sum = 1+2+3+4+5 = 15
  auto r1 = CCC::test_left;
  std::cout << "test_left = " << r1 << " (expected 15)" << std::endl;
  assert(r1 == 15u);

  // test_right: right-spine tree 5 nodes, sum = 1+2+3+4+5 = 15
  auto r2 = CCC::test_right;
  std::cout << "test_right = " << r2 << " (expected 15)" << std::endl;
  assert(r2 == 15u);

  // test_balanced: balanced tree depth 3
  // Structure: build_balanced 3 =
  //   Node (build_balanced 2) 3 (build_balanced 2)
  //   build_balanced 2 = Node (build_balanced 1) 2 (build_balanced 1)
  //   build_balanced 1 = Node Leaf 1 Leaf
  // sum = 4*1 + 2*2 + 1*3 = 4+4+3 = 11
  auto r3 = CCC::test_balanced;
  std::cout << "test_balanced = " << r3 << " (expected 11)" << std::endl;
  assert(r3 == 11u);

  // test_fold: fold on Node(Node(Leaf,2,Leaf), 3, Node(Leaf,4,Leaf))
  // combine(l, n, r) = l + n + r
  // fold Leaf = base = 1
  // fold Node(Leaf,2,Leaf) = combine(1, 2, 1) = 4
  // fold Node(Leaf,4,Leaf) = combine(1, 4, 1) = 6
  // fold root = combine(4, 3, 6) = 13
  auto r4 = CCC::test_fold;
  std::cout << "test_fold = " << r4 << " (expected 13)" << std::endl;
  assert(r4 == 13u);

  // test_pair: (tree_sum(build_left 4), tree_fold_cps(build_left 4, 0, +, id))
  // build_left 4: Node(Node(Node(Node(Leaf,1,Leaf),2,Leaf),3,Leaf),4,Leaf)
  // tree_sum = 1+2+3+4 = 10
  // tree_fold with base=0, combine=+: same as sum = 10
  auto [s, f] = CCC::test_pair;
  std::cout << "test_pair = (" << s << ", " << f << ") (expected (10, 10))" << std::endl;
  assert(s == 10u);
  assert(f == 10u);

  std::cout << "All cps_closure_chain tests passed!" << std::endl;
  return 0;
}
