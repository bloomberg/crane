#include "coinductive_node_sharing.h"

/// A coinductive value is one heap node, shared by every copy.  An
/// ITree.iter loop suspends every step as a thunk that delegates to the
/// next step's tree; forcing follows those delegations without copying
/// trees, and retargets them, so walking the loop is linear in its length.
/// The t.cpp walks 300000 steps, keeps the first node alive while it
/// does so the whole forced chain is in memory at once, and then drops it:
/// releasing the chain must not recurse once per step.
Itree<CoinductiveNodeSharing::voidE, uint64_t>
CoinductiveNodeSharing::count_to(uint64_t k) {
  return ITree::template iter<CoinductiveNodeSharing::voidE, uint64_t,
                              uint64_t>(
      [=](uint64_t i)
          -> Itree<CoinductiveNodeSharing::voidE, Sum<uint64_t, uint64_t>> {
        if (k <= i) {
          return Itree<CoinductiveNodeSharing::voidE, Sum<uint64_t, uint64_t>>::
              go(ItreeF<CoinductiveNodeSharing::voidE, Sum<uint64_t, uint64_t>,
                        Itree<CoinductiveNodeSharing::voidE,
                              Sum<uint64_t, uint64_t>>>::
                     retf(Sum<uint64_t, uint64_t>::inr(i)));
        } else {
          return Itree<CoinductiveNodeSharing::voidE, Sum<uint64_t, uint64_t>>::
              go(ItreeF<CoinductiveNodeSharing::voidE, Sum<uint64_t, uint64_t>,
                        Itree<CoinductiveNodeSharing::voidE,
                              Sum<uint64_t, uint64_t>>>::
                     retf(Sum<uint64_t, uint64_t>::inl((i + 1))));
        }
      },
      UINT64_C(0));
}
