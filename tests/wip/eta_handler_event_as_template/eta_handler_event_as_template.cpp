#include "eta_handler_event_as_template.h"

std::shared_ptr<ITree<std::pair<Nat, Nat>>> M::use(const Nat &n) {
  return fused<FailE, Nat>(AE::A0)(n);
}
