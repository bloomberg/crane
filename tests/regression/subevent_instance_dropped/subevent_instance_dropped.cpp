#include "subevent_instance_dropped.h"

std::shared_ptr<ITree<Nat>> SubeventInstanceDropped::use(const Nat &n) {
  return boom<FailE, Nat>(n);
}
