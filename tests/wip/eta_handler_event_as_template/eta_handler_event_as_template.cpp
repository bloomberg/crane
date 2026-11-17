#include "eta_handler_event_as_template.h"

std::shared_ptr<ITree<std::pair<Nat, Nat>>> M::use(const Nat &n) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto fused_1 = crane::immortal(fused<FailE, Nat>(AE::A0));
  return fused_1(n);
}
