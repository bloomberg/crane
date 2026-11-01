#include <loopify_partner_back_under_fixpoint.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = LoopifyPartnerBackUnderFixpoint;

int main() {
  const M::tree leaf = M::tree::node(0, M::forest::forest0(List<M::tree>::nil()));
  assert(M::tree_size(leaf) == 0);
  assert(M::forest_size(M::forest::forest0(List<M::tree>::cons(leaf, List<M::tree>::nil()))) == 0);
  // Each level of the chain adds a node of size 1 and a sibling of size 1.
  for (uint64_t k = 0; k < 32; k++)
    assert(M::tree_size(M::chain(k, leaf)) == 2 * k);
  uint64_t big = M::tree_size(M::chain(2000, leaf));
  std::cout << "tree_size (chain 2000) = " << big << " (want 4000)" << std::endl;
  assert(big == 4000);
  return 0;
}
