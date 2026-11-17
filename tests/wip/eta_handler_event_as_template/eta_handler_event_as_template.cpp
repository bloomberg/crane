#include "eta_handler_event_as_template.h"

std::shared_ptr<ITree<std::pair<Nat, Nat>>> M::use(const Nat &n) {
  static const auto fused_1 = crane::immortal(fused<FailE, Nat>(AE::A0));
  return fused_1(n);
}
