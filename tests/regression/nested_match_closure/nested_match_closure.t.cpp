#include <nested_match_closure.h>

#include <cassert>
#include <iostream>

int main() {
  using NMC = NestedMatchClosure;

  // test1: Node (Node Leaf 10 Leaf) 20 Leaf
  // combined = 20 + 10 = 30, go(5) = 30 + 5 = 35
  // BUG: go captures combined by [&], dangles after make_combiner returns.
  auto r1 = NMC::test1;
  std::cout << "test1 = " << r1 << " (expected 35)" << std::endl;
  assert(r1 == 35u);

  // test2: Node (Node (Node Leaf 100 Leaf) 200 Leaf) 300 Leaf
  // total = 300 + 200 + 100 = 600, go(0) = 600
  // BUG: go captures total from triple-nested pattern match by [&].
  auto r2 = NMC::test2;
  std::cout << "test2 = " << r2 << " (expected 600)" << std::endl;
  assert(r2 == 600u);

  // test3: Node (Node Leaf 5 Leaf) 10 (Node Leaf 15 Leaf), base=1000
  // go(0) = 1000 + 10 + tree_sum(left) + tree_sum(right) = 1000 + 10 + 5 + 15 = 1030
  // go(3) = 1030 + 3 = 1033
  // BUG: go captures base (fn param), d_a1, d_a0, d_a2 (structured bindings) by [&].
  auto r3 = NMC::test3;
  std::cout << "test3 = " << r3 << " (expected 1033)" << std::endl;
  assert(r3 == 1033u);

  // test4: Node (Node Leaf 42 Leaf) 100 Leaf, base=500
  // go(0) = 500 + 100 + 42 + 0 = 642
  // BUG: same as test3 but stored in optional, stack may be clobbered.
  auto r4 = NMC::test4;
  std::cout << "test4 = " << r4 << " (expected 642)" << std::endl;
  assert(r4 == 642u);

  std::cout << "All nested_match_closure tests passed!" << std::endl;
  return 0;
}
