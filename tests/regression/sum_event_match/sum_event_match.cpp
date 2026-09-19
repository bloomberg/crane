#include "sum_event_match.h"

std::shared_ptr<ITree<Nat>> SumEventMatch::use() {
  return handle<Nat>(sum1_inl(AE::A0));
}
