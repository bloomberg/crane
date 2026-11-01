#include <mutual_loopify_acc.h>
#include <cassert>
#include <iostream>

using M = MutualLoopifyAcc;

// A tree whose depth alternates between the two machines at every level --
// node (fcons (leaf 1) (fcons (node (fcons t fnil)) fnil)) -- so that a
// machine calling its partner's function where it should run the partner's
// body recurses on the C++ stack once per level.
static M::tree alternating(unsigned depth) {
  M::tree t = M::tree::leaf(1);
  for (unsigned i = 0; i < depth; i++)
    t = M::tree::node(M::forest::fcons(
        M::tree::leaf(1),
        M::forest::fcons(M::tree::node(M::forest::fcons(t, M::forest::fnil())), M::forest::fnil())));
  return t;
}

int main() {
  auto r = M::go(10);
  std::cout << "go 10 = " << r << " (want 10)" << std::endl;
  assert(r == 10);
  auto deep = M::tsum(0, alternating(100000));
  std::cout << "tsum (alternating 100000) = " << deep << " (want 100001)" << std::endl;
  assert(deep == 100001);
  return 0;
}
