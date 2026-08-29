#ifndef INCLUDED_ITREE_INVARIANTS
#define INCLUDED_ITREE_INVARIANTS

#include <crane_itree.h>

struct ItreeInvariants {
  static uint64_t count_taus(uint64_t fuel,
                             const std::shared_ptr<ITree<uint64_t>> &t);
};

#endif // INCLUDED_ITREE_INVARIANTS
