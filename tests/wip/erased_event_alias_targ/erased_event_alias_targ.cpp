#include "erased_event_alias_targ.h"

std::shared_ptr<ITree<Nat>> ErasedEventAliasTarg::use(const List<Nat> &x0_) {
  return k<FailE>(x0_);
}
